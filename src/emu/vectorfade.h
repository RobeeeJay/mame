// license:BSD-3-Clause
// copyright-holders:Robee Shepherd
#ifndef MAME_EMU_VECTORFADE_H
#define MAME_EMU_VECTORFADE_H

#pragma once

#include <algorithm>
#include <cmath>
#include <cstdint>


// An LCD has no phosphor, so all vectors in a frame appear equally bright and
// the image looks static.  This dims each visible point in drawing order, by the
// given percentage of its brightness over the course of one frame.  The fade
// carries on through later frames until cycle frames have passed, then resets.
class vector_fade
{
public:
	// the beam dwells where a vector starts, so that end is brighter than the line
	static constexpr int LINE_FADE = 16;
	static constexpr int DOT_BOOST = 16;

	// odd, so the texture has a centre texel at full brightness
	static constexpr int DOT_TEXTURE_SIZE = 7;

	static constexpr float DWELL_REFERENCE = (128.0f * 8.0f) / 12096000.0f;
	static constexpr int DWELL_REFERENCE_PASSES = 15;
	static constexpr int DOT_MAX_PASSES = 32;

	static float limit_percent(float percent) { return std::clamp(percent, 0.0f, 50.0f); }
	static float limit_cycle(float cycle) { return std::clamp(cycle, 1.0f, 1.9f); }

	void begin_frame(float percent, int visible_points, float cycle)
	{
		// the first frame has nothing before it, and an empty frame has no time to count
		if (m_step_valid)
			m_elapsed += 1.0f;
		m_step_valid = visible_points > 0;

		m_percent = percent;
		m_cycle = cycle;
		m_point = 0;
		m_step = (visible_points > 1) ? (1.0f / float(visible_points - 1)) : 0.0f;
	}

	int next(int intensity)
	{
		// invisible beam moves must not count, or the last line would stop short of the percentage
		if (intensity == 0)
			return 0;

		// multiplied, not accumulated, so rounding cannot push the last point past a whole cycle
		float position = m_elapsed + (float(m_point) * m_step);

		// a frame starting exactly on the cycle resets, but its predecessor's last point did not
		if ((m_point == 0) ? (position >= m_cycle) : (position > m_cycle))
		{
			m_elapsed = -(float(m_point) * m_step);
			position = 0.0f;
		}
		m_point++;

		float const level = 1.0f - ((m_percent * 0.01f) * position);
		return std::max(int((float(intensity) * level) + 0.5f), 0);
	}

	static int line_intensity(int faded) { return std::max(faded - LINE_FADE, 0); }
	static int dot_intensity(int faded) { return std::min(faded + DOT_BOOST, 255); }

	// Alpha stops at 255, so the energy of a beam held still can only show by
	// repeating the primitive, which adds up in bloom and halo.  Scaled so a full
	// intensity dot held for the Asteroids bullet's average of 128 DVG states
	// gets DWELL_REFERENCE_PASSES.  Without a dwell, brightness is all there is.
	static int dot_passes(int level, float dwell)
	{
		float const scale = float(level) / 255.0f;
		float const energy = (dwell > 0.0f) ? (scale * (dwell / DWELL_REFERENCE)) : (scale * scale);
		return std::min(1 + int((energy * float(DWELL_REFERENCE_PASSES)) + 0.5f), DOT_MAX_PASSES);
	}

	// A beam moving slowly leaves more energy on each spot of a line.  This is
	// relative to the frame, because absolute energy depends on the monitor's
	// deflection and drive, which are not known, and differ between machines.
	static int line_level(int level, float energy, float mean_energy)
	{
		if ((energy <= 0.0f) || (mean_energy <= 0.0f))
			return level;
		return std::clamp(int((float(level) * (energy / mean_energy)) + 0.5f), 0, 255);
	}

	// brightness of one texel of the soft round-cornered dot
	static int dot_texel(int x, int y)
	{
		float const step = 3.14159265f / float(DOT_TEXTURE_SIZE - 1);
		float const level = (std::sin(float(x) * step) * 128.0f) + (std::sin(float(y) * step) * 128.0f);
		return std::clamp(int(level), 0, 255);
	}

private:
	float m_percent = 0.0f;
	float m_cycle = 1.0f;
	float m_step = 0.0f;
	float m_elapsed = 0.0f; // whole frames since the last reset
	int m_point = 0;
	bool m_step_valid = false;
};


// Deflection amplifiers are noisy, so a real beam never lands exactly where it was
// sent.  This has its own generator because machine().rand() also drives emulation,
// and a display effect must not change how a game plays.
class vector_jitter
{
public:
	static float limit_percent(float percent) { return std::clamp(percent, 0.0f, 0.2f); }

	// a value from -1 to 1
	float next()
	{
		m_state ^= m_state << 13;
		m_state ^= m_state >> 17;
		m_state ^= m_state << 5;
		return (float(m_state) / 2147483647.5f) - 1.0f;
	}

private:
	uint32_t m_state = 0x9d14abd7;
};

#endif // MAME_EMU_VECTORFADE_H
