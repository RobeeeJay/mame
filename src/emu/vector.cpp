// license:BSD-3-Clause
// copyright-holders:Brad Oliver,Aaron Giles,Bernd Wiebelt,Allard van der Bas
/******************************************************************************
 *
 * vector.cpp
 *
 *        anti-alias code by Andrew Caldwell
 *        (still more to add)
 *
 * Vector Team
 *
 *        Brad Oliver
 *        Aaron Giles
 *        Bernd Wiebelt
 *        Allard van der Bas
 *        Al Kossow (VECSIM)
 *        Hedley Rainnie (VECSIM)
 *        Eric Smith (VECSIM)
 *        Neil Bradley (technical advice)
 *        Andrew Caldwell (anti-aliasing)
 *
 **************************************************************************** */

#include "emu.h"
#include "vector.h"

#include "emuopts.h"

#include <algorithm>
#include <cmath>

#define VECTOR_WIDTH_DENOM 512

// 20000 is needed for mhavoc (see MT 06668) 10000 is enough for other games
#define MAX_POINTS 20000

float vector_options::s_flicker = 0.0f;
float vector_options::s_beam_fade = 15.0f;
float vector_options::s_beam_fade_cycle = 1.2f;
float vector_options::s_beam_jitter = 0.01f;
float vector_options::s_beam_width_min = 0.0f;
float vector_options::s_beam_width_max = 0.0f;
float vector_options::s_beam_dot_size = 0.0f;
float vector_options::s_beam_intensity_weight = 0.0f;

void vector_options::init(emu_options &options)
{
	s_beam_width_min = options.beam_width_min();
	s_beam_width_max = options.beam_width_max();
	s_beam_dot_size = options.beam_dot_size();
	s_beam_intensity_weight = options.beam_intensity_weight();
	s_flicker = options.flicker();
	s_beam_fade = vector_fade::limit_percent(options.beam_fade());
	s_beam_fade_cycle = vector_fade::limit_cycle(options.beam_fade_cycle());
	s_beam_jitter = vector_jitter::limit_percent(options.beam_jitter());
}

// device type definition
DEFINE_DEVICE_TYPE(VECTOR, vector_device, "vector_device", "VECTOR")

vector_device::vector_device(const machine_config &mconfig, const char *tag, device_t *owner, uint32_t clock)
	: device_t(mconfig, VECTOR, tag, owner, clock),
		device_video_output_interface(mconfig, *this),
		m_vector_list(nullptr),
		m_vector_index(0),
		m_min_intensity(255),
		m_max_intensity(0),
		m_prev_jitter_x(0.0f),
		m_prev_jitter_y(0.0f),
		m_dot_texture(nullptr),
		m_visarea(rectangle()),
		m_frame_period(attotime::from_hz(DEFAULT_FRAME_RATE)),
		m_color(rgb_t::green()),
		m_vblank(*this),
		m_vector_update(*this),
		m_vblank_timer(nullptr)
{
}

void vector_device::device_start()
{
	m_vector_update.resolve();

	vector_options::init(machine().options());

	m_prevpoint.x = m_prevpoint.y = m_prevpoint.col = m_prevpoint.intensity = 0;
	m_vector_index = 0;

	/* allocate memory for tables */
	m_vector_list = std::make_unique<point[]>(MAX_POINTS);

	m_dot_bitmap.allocate(vector_fade::DOT_TEXTURE_SIZE, vector_fade::DOT_TEXTURE_SIZE);
	for (int y = 0; y < vector_fade::DOT_TEXTURE_SIZE; y++)
	{
		for (int x = 0; x < vector_fade::DOT_TEXTURE_SIZE; x++)
		{
			int const level = vector_fade::dot_texel(x, y);
			m_dot_bitmap.pix(y, x) = rgb_t(0xff, level, level, level);
		}
	}
	m_dot_texture = machine().render().texture_alloc();
	m_dot_texture->set_bitmap(m_dot_bitmap, m_dot_bitmap.cliprect(), TEXFORMAT_ARGB32);

	// register items for saving
	save_item(NAME(m_prevpoint.x));
	save_item(NAME(m_prevpoint.y));
	save_item(NAME(m_prevpoint.col));
	save_item(NAME(m_prevpoint.intensity));
	save_item(NAME(m_frame_period));

	/* allocate and start the vblank timer */
	m_vblank_timer = timer_alloc(FUNC(vector_device::vblank_timer_callback), this);
	m_vblank_timer->adjust(m_frame_period, 0, m_frame_period);
}


void vector_device::device_stop()
{
	machine().render().texture_free(m_dot_texture);
}


//-------------------------------------------------
//  vblank_timer_callback - periodically fires to
//  drive update_if_primary
//-------------------------------------------------

void vector_device::vblank_timer_callback(s32 param)
{
	update_if_primary();

	// call the vblank callback
	m_vblank(1);
	m_vblank(0);
}

//-------------------------------------------------
//  override_frame_period - forcibly change the
//  refresh rate (from the sliders)
//-------------------------------------------------

void vector_device::override_frame_period(attotime period)
{
	m_frame_period = period;
	m_vblank_timer->adjust(m_frame_period, 0, m_frame_period);
}

//-------------------------------------------------
//  subscribe for frame-begin notifications
//-------------------------------------------------

util::notifier_subscription vector_device::add_frame_begin_notifier(frame_begin_delegate &&n)
{
	return m_frame_begin_notifier.subscribe(std::move(n));
}


//-------------------------------------------------
//  subscribe for frame-end notifications
//-------------------------------------------------

util::notifier_subscription vector_device::add_frame_end_notifier(frame_end_delegate &&n)
{
	return m_frame_end_notifier.subscribe(std::move(n));
}


//-------------------------------------------------
//  subscribe for hidden-move notifications
//-------------------------------------------------

util::notifier_subscription vector_device::add_move_notifier(move_delegate &&n)
{
	return m_move_notifier.subscribe(std::move(n));
}


//-------------------------------------------------
//  subscribe for visible-line notifications
//-------------------------------------------------

util::notifier_subscription vector_device::add_line_notifier(line_delegate &&n)
{
	return m_line_notifier.subscribe(std::move(n));
}


//-------------------------------------------------
// www.dinodini.wordpress.com/2010/04/05/normalized-tunable-sigmoid-functions/
//-------------------------------------------------

float vector_device::normalized_sigmoid(float n, float k)
{
	// valid for n and k in range of -1.0 and 1.0
	return (n - n * k) / (k - fabs(n) * 2.0f * k + 1.0f);
}


//-------------------------------------------------
// Adds a line end point to the vertices list. The vector processor emulation
// needs to call this.
//-------------------------------------------------

void vector_device::add_point(int x, int y, rgb_t color, int intensity, float dwell)
{
	point *newpoint;

	intensity = std::clamp(intensity, 0, 255);

	m_min_intensity = intensity > 0 ? std::min(m_min_intensity, intensity) : m_min_intensity;
	m_max_intensity = intensity > 0 ? std::max(m_max_intensity, intensity) : m_max_intensity;

	if (vector_options::s_flicker && (intensity > 0))
	{
		float random = float(machine().rand() & 255) / 255.0f; // random value between 0.0 and 1.0

		intensity -= int(intensity * random * vector_options::s_flicker);

		intensity = std::clamp(intensity, 0, 255);
	}

	newpoint = &m_vector_list[m_vector_index];
	newpoint->x = x;
	newpoint->y = y;
	newpoint->col = color;
	newpoint->intensity = intensity;
	newpoint->dwell = dwell;

	m_vector_index++;
	if (m_vector_index >= MAX_POINTS)
	{
		m_vector_index--;
		logerror("*** Warning! Vector list overflow!\n");
	}
}


//-------------------------------------------------
// The vector CPU creates a new display list. We save the old display list,
// but only once per refresh.
//-------------------------------------------------

void vector_device::clear_list()
{
	m_vector_index = 0;
}

//-------------------------------------------------
// Update the container with queued vectors.
//-------------------------------------------------

bool vector_device::video_output_update()
{
	if (!m_vector_update.isnull())
		m_vector_update(*this);

	uint32_t flags = PRIMFLAG_ANTIALIAS(1) | PRIMFLAG_BLENDMODE(BLENDMODE_ADD) | PRIMFLAG_VECTOR(1);
	const rectangle &visarea = m_visarea;
	float xscale = 1.0f / (65536 * visarea.width());
	float yscale = 1.0f / (65536 * visarea.height());
	float xoffs = (float)visarea.left();
	float yoffs = (float)visarea.top();

	point *curpoint;

	curpoint = m_vector_list.get();

	container().empty();
	container().add_rect(0.0f, 0.0f, 1.0f, 1.0f, rgb_t(0xff,0x00,0x00,0x00), PRIMFLAG_BLENDMODE(BLENDMODE_ALPHA) | PRIMFLAG_VECTORBUF(1));

	// jitter is a share of screen height, the same physical distance on both axes
	auto const [jitter_aspect_x, jitter_aspect_y] = physical_aspect();
	float const jitter_aspect = float(jitter_aspect_y) / float(jitter_aspect_x);

	bool const fading = vector_options::s_beam_fade > 0.0f;
	float mean_line_energy = 0.0f;
	if (fading)
	{
		int const visible_points = std::count_if(m_vector_list.get(), m_vector_list.get() + m_vector_index, [] (point const &p) { return p.intensity != 0; });
		m_fade.begin_frame(vector_options::s_beam_fade, visible_points, vector_options::s_beam_fade_cycle);

		// total over total, because a sum of ratios would be dominated by tiny lines
		float total_dwell = 0.0f;
		float total_length = 0.0f;
		int last_x = m_prevpoint.x;
		int last_y = m_prevpoint.y;
		for (int i = 0; i < m_vector_index; i++)
		{
			point const &p = m_vector_list[i];
			if (p.intensity != 0)
			{
				float const length = std::hypot(float(p.x - last_x), float(p.y - last_y));
				if (length > 0.0f)
				{
					total_dwell += p.dwell;
					total_length += length;
				}
			}
			last_x = p.x;
			last_y = p.y;
		}
		mean_line_energy = (total_length > 0.0f) ? (total_dwell / total_length) : 0.0f;
	}

	m_frame_begin_notifier();

	for (int i = 0; i < m_vector_index; i++)
	{
		render_bounds coords;

		float intensity = (float)curpoint->intensity / 255.0f;
		float intensity_weight = normalized_sigmoid(intensity, vector_options::s_beam_intensity_weight);

		// check for static intensity
		float beam_width = m_min_intensity == m_max_intensity
			? vector_options::s_beam_width_min
			: vector_options::s_beam_width_min + intensity_weight * (vector_options::s_beam_width_max - vector_options::s_beam_width_min);

		// normalize width
		beam_width *= 1.0f / (float)VECTOR_WIDTH_DENOM;

		// apply point scale for points
		bool const is_dot = m_prevpoint.x == curpoint->x && m_prevpoint.y == curpoint->y;
		float const dot_width = beam_width * vector_options::s_beam_dot_size;
		if (is_dot)
			beam_width = dot_width;

		// each point moves once, so a line starts where the last one ended and shapes stay joined
		float const jitter = vector_options::s_beam_jitter * 0.01f;
		float const jitter_x = (jitter > 0.0f) ? (m_jitter.next() * jitter * jitter_aspect) : 0.0f;
		float const jitter_y = (jitter > 0.0f) ? (m_jitter.next() * jitter) : 0.0f;

		coords.x0 = ((float(m_prevpoint.x) - xoffs) * xscale) + m_prev_jitter_x;
		coords.y0 = ((float(m_prevpoint.y) - yoffs) * yscale) + m_prev_jitter_y;
		coords.x1 = ((float(curpoint->x) - xoffs) * xscale) + jitter_x;
		coords.y1 = ((float(curpoint->y) - yoffs) * yscale) + jitter_y;

		m_prev_jitter_x = jitter_x;
		m_prev_jitter_y = jitter_y;

		// the list is not mutated because a game may redraw it without rebuilding it
		int const faded = fading ? m_fade.next(curpoint->intensity) : curpoint->intensity;

		if (curpoint->intensity != 0)
		{
			uint32_t const col = curpoint->col & 0xffffff;

			if (!fading)
			{
				container().add_line(coords.x0, coords.y0, coords.x1, coords.y1, beam_width, (faded << 24) | col, flags);
			}
			else if (is_dot)
			{
				// The quad supplies the brightness, but only line primitives reach the
				// BGFX vector CRT, so these are what feed bloom and after-image.
				int const level = vector_fade::dot_intensity(faded);
				rgb_t const argb = (level << 24) | col;
				for (int pass = vector_fade::dot_passes(level, curpoint->dwell); pass > 0; pass--)
					container().add_point(coords.x1, coords.y1, beam_width, argb, flags);

				// the quad is 4/3 of the line width, and square on a 4:3 screen
				auto const [aspect_x, aspect_y] = physical_aspect();
				float const half_y = beam_width * (2.0f / 3.0f);
				float const half_x = half_y * float(aspect_y) / float(aspect_x);
				container().add_quad(coords.x1 - half_x, coords.y1 - half_y, coords.x1 + half_x, coords.y1 + half_y, argb, m_dot_texture, PRIMFLAG_BLENDMODE(BLENDMODE_ADD));
			}
			else
			{
				container().add_point(coords.x0, coords.y0, dot_width, (faded << 24) | col, flags);
				float const line_energy = curpoint->dwell / std::hypot(float(curpoint->x - m_prevpoint.x), float(curpoint->y - m_prevpoint.y));
				int const level = vector_fade::line_level(faded, line_energy, mean_line_energy);
				container().add_line(coords.x0, coords.y0, coords.x1, coords.y1, beam_width, (vector_fade::line_intensity(level) << 24) | col, flags);
			}

			// external vector displays have a real phosphor, so they get the unfaded stream
			m_line_notifier(m_prevpoint.x, m_prevpoint.y, curpoint->x, curpoint->y, curpoint->col, curpoint->intensity, visarea.width(), visarea.height());
		}
		else
		{
			m_move_notifier(curpoint->x, curpoint->y, curpoint->col, visarea.width(), visarea.height());
		}

		m_prevpoint.x = curpoint->x;
		m_prevpoint.y = curpoint->y;
		m_prevpoint.col = curpoint->col;
		m_prevpoint.intensity = curpoint->intensity;

		curpoint++;
	}

	m_frame_end_notifier();

	return true;
}


//-------------------------------------------------
//  physical aspect ratio
//-------------------------------------------------

std::pair<unsigned, unsigned> vector_device::physical_aspect() const
{
	return { 4, 3 };
}
