// license:BSD-3-Clause
// copyright-holders:Brad Oliver,Aaron Giles,Bernd Wiebelt,Allard van der Bas
/******************************************************************************
 *
 * vector.c
 *
 *        anti-alias code by Andrew Caldwell
 *        (still more to add)
 *
 * 040227 Fixed miny clip scaling which was breaking in mhavoc. AREK
 * 010903 added support for direct RGB modes MLR
 * 980611 use translucent vectors. Thanks to Peter Hirschberg
 *        and Neil Bradley for the inspiration. BW
 * 980307 added cleverer dirty handling. BW, ASG
 *        fixed antialias table .ac
 * 980221 rewrote anti-alias line draw routine
 *        added inline assembly multiply fuction for 8086 based machines
 *        beam diameter added to draw routine
 *        beam diameter is accurate in anti-alias line draw (Tcosin)
 *        flicker added .ac
 * 980203 moved LBO's routines for drawing into a buffer of vertices
 *        from avgdvg.c to this location. Scaling is now initialized
 *        by calling vector_init(...). BW
 * 980202 moved out of msdos.c ASG
 * 980124 added anti-alias line draw routine
 *        modified avgdvg.c and sega.c to support new line draw routine
 *        added two new tables Tinten and Tmerge (for 256 color support)
 *        added find_color routine to build above tables .ac
 *
 **************************************************************************** */

#include "emu.h"
#include "emuopts.h"
#include "rendutil.h"
#include "vector.h"
#include <math.h>


#define VECTOR_WIDTH_DENOM          512
#define VECTOR_TOTALFADETIME	1.0f

#define MAX_POINTS  10000

#define VECTOR_TEAM \
	"-* Vector Heads *-\n" \
	"Brad Oliver\n" \
	"Aaron Giles\n" \
	"Bernd Wiebelt\n" \
	"Allard van der Bas\n" \
	"Al Kossow (VECSIM)\n" \
	"Hedley Rainnie (VECSIM)\n" \
	"Eric Smith (VECSIM)\n" \
	"Neil Bradley (technical advice)\n" \
	"Andrew Caldwell (anti-aliasing)\n" \
	"- *** -\n"

#if 0

#define TEXTURE_LENGTH_BUCKETS      32
#define TEXTURE_INTENSITY_BUCKETS   4
#define TEXTURE_WIDTH               16

#define MAX_INTENSITY               2
#define VECTOR_BLEED                (0.25f)
#define VECTOR_INT_SCALE            (255.0f * 1.5f)


struct vector_texture
{
	render_texture *    texture;
	bitmap_argb32 *     bitmap;
};

static vector_texture *vectortex[TEXTURE_INTENSITY_BUCKETS][TEXTURE_LENGTH_BUCKETS];


static render_texture *get_vector_texture(float dx, float dy, float intensity)
{
	float length = sqrt(dx * dx + dy * dy);
	int lbucket = length * (float)TEXTURE_LENGTH_BUCKETS;
	int ibucket = (intensity / (float)MAX_INTENSITY) * (float)TEXTURE_INTENSITY_BUCKETS;
	vector_texture *tex;
	int height, x, y;
	float totalint;

	if (lbucket > TEXTURE_LENGTH_BUCKETS)
		lbucket = TEXTURE_LENGTH_BUCKETS;
	if (ibucket > TEXTURE_INTENSITY_BUCKETS)
		ibucket = TEXTURE_INTENSITY_BUCKETS;

	tex = &vectortex[ibucket][lbucket];
	if (tex->texture != NULL)
		return tex->texture;

	height = lbucket * VECTOR_WIDTH_DENOM / TEXTURE_LENGTH_BUCKETS;
	tex->bitmap = global_alloc(bitmap_argb32(TEXTURE_WIDTH, height));
	tex->bitmap.fill(rgb_t(0xff,0xff,0xff,0xff));

	totalint = 1.0f;
	for (x = TEXTURE_WIDTH / 2 - 1; x >= 0; x--)
	{
		int intensity = (int)(totalint * (1.0f - VECTOR_BLEED) * VECTOR_INT_SCALE);
		intensity = MIN(255, intensity);
		totalint -= (float)intensity * (1.0f / VECTOR_INT_SCALE);

		for (y = 0; y < height; y++)
		{
			UINT32 *pix;

			pix = (UINT32 *)bitmap.base + y * bitmap.rowpixels + x;
			*pix = rgb_t((*pix.a() * intensity) >> 8,0xff,0xff,0xff);

			pix = (UINT32 *)bitmap.base + y * bitmap.rowpixels + (TEXTURE_WIDTH - 1 - x);
			*pix = rgb_t((*pix.a() * intensity) >> 8,0xff,0xff,0xff);
		}
	}

	tex->texture = render_texture_create();
	return tex->texture;
}

#endif

#define VCLEAN  0
#define VDIRTY  1
#define VCLIP   2

// device type definition
const device_type VECTOR = &device_creator<vector_device>;

vector_device::vector_device(const machine_config &mconfig, device_type type, const char *name, const char *tag, device_t *owner, UINT32 clock, const char *shortname, const char *source)
	: device_t(mconfig, type, name, tag, owner, clock, shortname, source),
		device_video_interface(mconfig, *this)
{
}

vector_device::vector_device(const machine_config &mconfig, const char *tag, device_t *owner, UINT32 clock)
	: device_t(mconfig, VECTOR, "VECTOR", tag, owner, clock, "vector_device", __FILE__),
		device_video_interface(mconfig, *this)
{
}

float vector_device::m_flicker_correction = 0.0f;
float vector_device::m_beam_width = 0.0f;
int vector_device::m_flicker;
int vector_device::m_vector_index;
int vector_device::m_vector_index_minus_clips;

/* The new vector flickering vars */

/*	The line fade is the reduction in brightness between the starting point of a vector line and the actual line itself.
	All vector lines have a slightly brighter starting point because the beam is not moving when the line is turned on. */
int vector_device::m_vector_linefade = 16;
int vector_device::m_vector_dotboost = 16;

/* This is the internal counter which keeps track of the current amount of phosphor fade for the last drawn line */
float vector_device::m_vector_intensityroller = 0;

/* This texture represents the dot pixel */
bitmap_rgb32* vector_device::m_dotbitmap;
render_texture *vector_device::m_dottexture;

/* The dimensions of the dot bitmap, ideally an odd number */
#define DOTSIZE 7

void vector_device::device_start()
{
	m_beam_width = machine().options().beam();

	/* Grab the settings for this session */
	set_flicker(machine().options().flicker());

	m_vector_index = 0;
	m_vector_index_minus_clips = 0;

	/* allocate memory for tables */
	m_vector_list = auto_alloc_array_clear(machine(), point, MAX_POINTS);
	
	/* allocate memory for the vector dot bitmap */	
	m_dotbitmap = auto_bitmap_rgb32_alloc(machine(), DOTSIZE, DOTSIZE);
	m_dottexture = machine().render().texture_alloc();
	m_dottexture->set_bitmap(*m_dotbitmap, m_dotbitmap->cliprect(), TEXFORMAT_ARGB32);
	
	float ratio_degrees = (float)M_PI / (float)(DOTSIZE - 1);
	
	/* create dot bitmap */
	for (int y = 0; y < DOTSIZE; y++)
	{
		for (int x = 0; x < DOTSIZE; x ++)
		{
			int intensity;
//logerror("X: %i, X-Deg: %f, X-Sin: %f, Y: %i, Y-Deg: %f, Y-Sin: %f", x, (float)x * ratio_degrees, sinf((float)x * ratio_degrees), y, (float)y * ratio_degrees, sinf((float)y * ratio_degrees));
			intensity = (sinf((float)x * ratio_degrees) * 128) + (sinf((float)y * ratio_degrees) * 128);
			
			logerror("X: %i, Y: %i, Intensity: %i", x, y, intensity);
			
			if (intensity > 255)
				intensity = 255;
			if (intensity < 0)
				intensity = 0;
			
			//logerror(", Adjusted Intensity: %i\n", intensity);
			
			m_dotbitmap->pix32(y, x) = rgb_t(0xff, intensity, intensity, intensity);
		}
	}
}

void vector_device::set_flicker(float _flicker)
{
	m_flicker_correction = _flicker;
	m_flicker = (int)(m_flicker_correction * 2.55f);
}

float vector_device::get_flicker()
{
	return m_flicker_correction;
}

void vector_device::set_beam(float _beam)
{
	m_beam_width = _beam;
}

float vector_device::get_beam()
{
	return m_beam_width;
}


/*
 * Adds a line end point to the vertices list. The vector processor emulation
 * needs to call this.
 */
void vector_device::add_point (int x, int y, rgb_t color, int intensity)
{
	point *newpoint;

	if (intensity > 0xff)
		intensity = 0xff;

	if (m_flicker && (intensity > 0))
	{
		intensity += (intensity * (0x80-(machine().rand()&0xff)) * m_flicker)>>16;
		if (intensity < 0)
			intensity = 0;
		if (intensity > 0xff)
			intensity = 0xff;
	}
	newpoint = &m_vector_list[m_vector_index];
	newpoint->x = x;
	newpoint->y = y;
	newpoint->col = color;
	newpoint->intensity = intensity;
	newpoint->status = VDIRTY; /* mark identical lines as clean later */

	m_vector_index++;
	m_vector_index_minus_clips++;
	if (m_vector_index >= MAX_POINTS)
	{
		m_vector_index--;
		logerror("*** Warning! Vector list overflow!\n");
	}
}

/*
 * Add new clipping info to the list
 */
void vector_device::add_clip (int x1, int yy1, int x2, int y2)
{
	point *newpoint;

	newpoint = &m_vector_list[m_vector_index];
	newpoint->x = x1;
	newpoint->y = yy1;
	newpoint->arg1 = x2;
	newpoint->arg2 = y2;
	newpoint->status = VCLIP;

	m_vector_index++;
	if (m_vector_index >= MAX_POINTS)
	{
		m_vector_index--;
		logerror("*** Warning! Vector list overflow!\n");
	}
}


/*
 * The vector CPU creates a new display list. We save the old display list,
 * but only once per refresh.
 */
void vector_device::clear_list (void)
{
	m_vector_index = 0;
}


UINT32 vector_device::screen_update(screen_device &screen, bitmap_rgb32 &bitmap, const rectangle &cliprect)
{
	UINT32 flags = PRIMFLAG_ANTIALIAS(screen.machine().options().antialias() ? 1 : 0) | PRIMFLAG_BLENDMODE(BLENDMODE_ADD) | PRIMFLAG_VECTOR(1);
	UINT32 vector_flags = flags | PRIMFLAG_VECTOR(1);
	const rectangle &visarea = screen.visible_area();
	float xscale = 1.0f / (65536 * visarea.width());
	float yscale = 1.0f / (65536 * visarea.height());
	float xoffs = (float)visarea.min_x;
	float yoffs = (float)visarea.min_y;
	float intensity_stepchange, halfbeam_width_x, halfbeam_width_y;
	point *curpoint;
	render_bounds clip;
	int lastx = 0, lasty = 0;
	int i, linefade, dotboost;

	curpoint = m_vector_list;
	
	/* Flicker is the total amount of phosphor fade to simulate, and it takes VECTOR_TOTALFADETIME frames
		to travel through a full fade which creates a pleasant and convincing flicker illusion on an LCD display */
	intensity_stepchange = (float)m_flicker / (float)(m_vector_index_minus_clips * VECTOR_TOTALFADETIME);
	
	/*if (!m_flicker)
		linefade = 0;
	else*/
		linefade = m_vector_linefade;
	
	dotboost = m_vector_dotboost;
	
	/* Quick calc of half the beam width used for plotting dot texture */
	//halfbeam_width = beam_width * (1.0f / (float)VECTOR_WIDTH_DENOM);
	halfbeam_width_x = m_beam_width * (screen.container().xscale() / (float)VECTOR_WIDTH_DENOM);
	halfbeam_width_y = m_beam_width * (screen.container().yscale() / (float)VECTOR_WIDTH_DENOM);
	//logerror("X-Scale: %f, Y-Scale: %f, Orientation: %i, Aspect: %f\n", screen.container().xscale(), screen.container().yscale(), screen.container().orientation(), screen.container().pixel_aspect());

	screen.container().empty();
	screen.container().add_rect(0.0f, 0.0f, 1.0f, 1.0f, rgb_t(0xff,0x00,0x00,0x00), PRIMFLAG_BLENDMODE(BLENDMODE_ALPHA) | PRIMFLAG_VECTORBUF(1));

	clip.x0 = clip.y0 = 0.0f;
	clip.x1 = clip.y1 = 1.0f;

	for (i = 0; i < m_vector_index; i++)
	{
		render_bounds coords;

		if (curpoint->status == VCLIP)
		{
			coords.x0 = ((float)curpoint->x - xoffs) * xscale;
			coords.y0 = ((float)curpoint->y - yoffs) * yscale;
			coords.x1 = ((float)curpoint->arg1 - xoffs) * xscale;
			coords.y1 = ((float)curpoint->arg2 - yoffs) * yscale;

			clip.x0 = (coords.x0 > 0.0f) ? coords.x0 : 0.0f;
			clip.y0 = (coords.y0 > 0.0f) ? coords.y0 : 0.0f;
			clip.x1 = (coords.x1 < 1.0f) ? coords.x1 : 1.0f;
			clip.y1 = (coords.y1 < 1.0f) ? coords.y1 : 1.0f;
		}
		else
		{
			coords.x0 = ((float)lastx - xoffs) * xscale;
			coords.y0 = ((float)lasty - yoffs) * yscale;
			coords.x1 = ((float)curpoint->x - xoffs) * xscale;
			coords.y1 = ((float)curpoint->y - yoffs) * yscale;
			
			if (m_flicker == 40)
				logerror("Roller: %f, Intensity: %i\n", m_vector_intensityroller, curpoint->intensity);
				
			curpoint->intensity = (int)((float)curpoint->intensity - m_vector_intensityroller);
			
			if (m_flicker == 40)
				logerror("Adjusted Intensity: %i, ", curpoint->intensity);
			
			if (curpoint->intensity < 0)
					curpoint->intensity = 0;
				
			if (m_flicker == 40)
				logerror("Final Intensity: %i\n", curpoint->intensity);

			m_vector_intensityroller += intensity_stepchange;
			if (m_vector_intensityroller > (float)m_flicker)
				m_vector_intensityroller = 0;

			if (curpoint->intensity != 0)
			{
				if (!render_clip_line(&coords, &clip))
				{
					// Check if this is a dot so we can use a bitmap instead of a line
					if ((coords.x0 == coords.x1) && (coords.y0 == coords.y1))
					{
						curpoint->intensity += dotboost;
						if (curpoint->intensity > 255)
							curpoint->intensity = 255;
						
						// Add a bright pixel texture
						screen.container().add_quad(coords.x0 - halfbeam_width_x, coords.y0 - halfbeam_width_y, coords.x1 + halfbeam_width_x, coords.y1 + halfbeam_width_y, (curpoint->intensity << 24) | (curpoint->col & 0xffffff), m_dottexture, flags);
					}
					else
					{
						screen.container().add_quad(coords.x0 - halfbeam_width_x, coords.y0 - halfbeam_width_y, coords.x0 + halfbeam_width_x, coords.y0 + halfbeam_width_y, (curpoint->intensity << 24) | (curpoint->col & 0xffffff), m_dottexture, flags);
						
						curpoint->intensity -= linefade;
						if (curpoint->intensity < 0)
							curpoint->intensity = 0;

						screen.container().add_line(coords.x0, coords.y0, coords.x1, coords.y1,
							m_beam_width * (1.0f / (float)VECTOR_WIDTH_DENOM),
							(curpoint->intensity << 24) | (curpoint->col & 0xffffff),
							vector_flags);
					}
				}
			}

			lastx = curpoint->x;
			lasty = curpoint->y;
		}
		curpoint++;
	}
	return 0;
}
