#include "catch.hpp"

#include "vectorfade.h"

#include <cstdlib>

TEST_CASE("the last of 100 points in a frame reaches the fade percentage", "[emu]")
{
	vector_fade fade;
	fade.begin_frame(50.0f, 100, 1.0f);
	int last = 0;
	for (int point = 0; point < 100; point++)
	{
		int const faded = fade.next(200);
		if (point == 0)
			CHECK(faded == 200);
		last = faded;
	}
	CHECK(last == 100);
}

// The fade is meant to depend on the line count, so a frame of 4 and a frame of
// 1000 both have to span the whole percentage.
TEST_CASE("the fade spans the whole percentage whatever the point count", "[emu]")
{
	for (int points : { 2, 3, 4, 7, 100, 1000, 20000 })
	{
		vector_fade fade;
		fade.begin_frame(50.0f, points, 1.0f);
		int first = 0, last = 0;
		for (int point = 0; point < points; point++)
		{
			last = fade.next(200);
			if (point == 0)
				first = last;
		}
		INFO("points " << points << " first " << first << " last " << last);
		CHECK(first == 200);
		CHECK(last == 100);
	}
}

TEST_CASE("the percentage scales with the point's own brightness", "[emu]")
{
	vector_fade fade;
	fade.begin_frame(50.0f, 2, 1.0f);
	CHECK(fade.next(100) == 100);
	CHECK(fade.next(100) == 50);

	vector_fade dim;
	dim.begin_frame(50.0f, 2, 1.0f);
	CHECK(dim.next(40) == 40);
	CHECK(dim.next(40) == 20);
}

// Beam moves draw nothing, so counting them would leave the last visible line
// short of the percentage in a game that moves the beam after drawing.
TEST_CASE("invisible points stay invisible and do not advance the fade", "[emu]")
{
	vector_fade fade;
	fade.begin_frame(50.0f, 3, 1.0f);
	CHECK(fade.next(0) == 0);
	CHECK(fade.next(200) == 200);
	CHECK(fade.next(0) == 0);
	CHECK(fade.next(200) == 150);
	CHECK(fade.next(0) == 0);
	CHECK(fade.next(200) == 100);
}

TEST_CASE("a cycle of one frame resets at the start of every frame", "[emu]")
{
	vector_fade fade;
	for (int frame = 0; frame < 1000; frame++)
	{
		fade.begin_frame(50.0f, 3, 1.0f);
		INFO("frame " << frame);
		REQUIRE(fade.next(200) == 200);
		REQUIRE(fade.next(200) == 150);
		REQUIRE(fade.next(200) == 100);
	}
}

// This is what lets a fade overlap later frames.
TEST_CASE("a cycle of two frames carries the fade into the second frame then resets", "[emu]")
{
	vector_fade fade;
	fade.begin_frame(25.0f, 3, 2.0f);
	CHECK(fade.next(200) == 200);
	CHECK(fade.next(200) == 175);
	CHECK(fade.next(200) == 150);
	fade.begin_frame(25.0f, 3, 2.0f);
	CHECK(fade.next(200) == 150);
	CHECK(fade.next(200) == 125);
	CHECK(fade.next(200) == 100);
	fade.begin_frame(25.0f, 3, 2.0f);
	CHECK(fade.next(200) == 200);
}

TEST_CASE("a fractional cycle resets part way through a frame", "[emu]")
{
	vector_fade fade;
	fade.begin_frame(40.0f, 3, 1.5f);
	CHECK(fade.next(200) == 200);
	CHECK(fade.next(200) == 160);
	CHECK(fade.next(200) == 120);
	fade.begin_frame(40.0f, 3, 1.5f);
	CHECK(fade.next(200) == 120);
	CHECK(fade.next(200) == 80);
	CHECK(fade.next(200) == 200);

	// the reset fell on the last point, so this frame carries on from it and has
	// no reset of its own: the reset point moves from frame to frame
	fade.begin_frame(40.0f, 3, 1.5f);
	CHECK(fade.next(200) == 200);
	CHECK(fade.next(200) == 160);
	CHECK(fade.next(200) == 120);
}

TEST_CASE("a point count that changes between frames keeps the reset on time", "[emu]")
{
	vector_fade fade;
	fade.begin_frame(50.0f, 100, 2.0f);
	for (int point = 0; point < 100; point++)
		fade.next(200);
	fade.begin_frame(50.0f, 5, 2.0f);
	for (int point = 0; point < 5; point++)
		fade.next(200);
	fade.begin_frame(50.0f, 50, 2.0f);
	CHECK(fade.next(200) == 200);
}

TEST_CASE("a fade that reaches 100 percent before the reset stops at black", "[emu]")
{
	vector_fade fade;
	fade.begin_frame(100.0f, 2, 3.0f);
	fade.next(200);
	CHECK(fade.next(200) == 0);
	fade.begin_frame(100.0f, 2, 3.0f);
	CHECK(fade.next(200) == 0);
	CHECK(fade.next(200) == 0);
}

TEST_CASE("a frame with a single point stays at full brightness on a one frame cycle", "[emu]")
{
	vector_fade fade;
	for (int frame = 0; frame < 4; frame++)
	{
		fade.begin_frame(50.0f, 1, 1.0f);
		INFO("frame " << frame);
		REQUIRE(fade.next(200) == 200);
	}
}

TEST_CASE("a zero cycle leaves points at full brightness rather than dividing by zero", "[emu]")
{
	vector_fade fade;
	fade.begin_frame(50.0f, 4, 0.0f);
	CHECK(fade.next(200) == 200);
	CHECK(fade.next(200) == 200);
}

TEST_CASE("option values outside the limits are brought back inside them", "[emu]")
{
	CHECK(vector_fade::limit_percent(-5.0f) == 0.0f);
	CHECK(vector_fade::limit_percent(15.0f) == 15.0f);
	CHECK(vector_fade::limit_percent(80.0f) == 50.0f);
	CHECK(vector_fade::limit_cycle(0.5f) == 1.0f);
	CHECK(vector_fade::limit_cycle(1.2f) == 1.2f);
	CHECK(vector_fade::limit_cycle(5.0f) == 1.9f);
}

TEST_CASE("lines sit below their start dot and stay in range", "[emu]")
{
	CHECK(vector_fade::line_intensity(200) == 184);
	CHECK(vector_fade::line_intensity(10) == 0);
	CHECK(vector_fade::dot_intensity(200) == 216);
	CHECK(vector_fade::dot_intensity(250) == 255);
}

// One Asteroids bullet cycles through these as the game changes scale.  The
// hardware shimmers because of it, so equal passes would lose real behaviour.
TEST_CASE("a bullet's energy follows the time the beam is held on it", "[emu]")
{
	float const clock = 12096000.0f;
	CHECK(vector_fade::dot_passes(255, (64 * 8) / clock) == 9);
	CHECK(vector_fade::dot_passes(255, (128 * 8) / clock) == 16);
	CHECK(vector_fade::dot_passes(255, (256 * 8) / clock) == 31);
}

// Explosion debris is half intensity and mostly short, and must stay far below a bullet.
TEST_CASE("a dot's energy follows its intensity as well as its dwell", "[emu]")
{
	float const clock = 12096000.0f;
	CHECK(vector_fade::dot_passes(119, (2 * 8) / clock) == 1);
	CHECK(vector_fade::dot_passes(119, (32 * 8) / clock) == 3);
}

TEST_CASE("a very long dwell stops at the most passes", "[emu]")
{
	CHECK(vector_fade::dot_passes(255, 1.0f) == vector_fade::DOT_MAX_PASSES);
}

// Most vector hardware models do not report dwell, and must keep working.
TEST_CASE("a dot with no dwell falls back to its brightness", "[emu]")
{
	CHECK(vector_fade::dot_passes(255, 0.0f) == 16);
	CHECK(vector_fade::dot_passes(119, 0.0f) == 4);
}

// Without this a slow short vector looks the same as a fast long one.
TEST_CASE("a line brightens or dims with its energy relative to the frame", "[emu]")
{
	CHECK(vector_fade::line_level(100, 1.0f, 1.0f) == 100);
	CHECK(vector_fade::line_level(100, 1.7f, 1.0f) == 170);
	CHECK(vector_fade::line_level(100, 0.7f, 1.0f) == 70);
}

TEST_CASE("a very slow line stops at full brightness", "[emu]")
{
	CHECK(vector_fade::line_level(119, 34.0f, 1.0f) == 255);
}

// Hardware that reports no dwell has energy 0 everywhere, and must look unchanged.
TEST_CASE("a line with no dwell keeps its brightness", "[emu]")
{
	CHECK(vector_fade::line_level(119, 0.0f, 0.0f) == 119);
	CHECK(vector_fade::line_level(119, 0.0f, 1.0f) == 119);
	CHECK(vector_fade::line_level(119, 1.0f, 0.0f) == 119);
}

TEST_CASE("a visible dot is always drawn at least once", "[emu]")
{
	CHECK(vector_fade::dot_passes(1, 0.0f) == 1);
	CHECK(vector_fade::dot_passes(0, 0.0f) == 1);
	CHECK(vector_fade::dot_passes(1, 1.0e-9f) == 1);
}

// The centre is what makes a single point stand out against the lines around it.
TEST_CASE("the dot texture is full brightness at its centre and black at its corners", "[emu]")
{
	int const last = vector_fade::DOT_TEXTURE_SIZE - 1;
	CHECK(vector_fade::dot_texel(last / 2, last / 2) == 255);
	CHECK(vector_fade::dot_texel(0, 0) == 0);
	CHECK(vector_fade::dot_texel(last, 0) == 0);
	CHECK(vector_fade::dot_texel(0, last) == 0);
	CHECK(vector_fade::dot_texel(last, last) == 0);
}

// A lopsided texture would shift dots off the point the game asked for.
TEST_CASE("the dot texture is symmetrical", "[emu]")
{
	int const last = vector_fade::DOT_TEXTURE_SIZE - 1;
	for (int y = 0; y <= last; y++)
	{
		for (int x = 0; x <= last; x++)
		{
			INFO("x " << x << " y " << y);
			REQUIRE(vector_fade::dot_texel(x, y) == vector_fade::dot_texel(y, x));
			REQUIRE(std::abs(vector_fade::dot_texel(x, y) - vector_fade::dot_texel(last - x, last - y)) <= 1);
		}
	}
}

TEST_CASE("jitter stays within its range and reaches both sides", "[emu]")
{
	vector_jitter jitter;
	float lowest = 0.0f, highest = 0.0f, total = 0.0f;
	for (int i = 0; i < 100000; i++)
	{
		float const value = jitter.next();
		REQUIRE(value >= -1.0f);
		REQUIRE(value <= 1.0f);
		lowest = std::min(lowest, value);
		highest = std::max(highest, value);
		total += value;
	}
	INFO("lowest " << lowest << " highest " << highest << " mean " << (total / 100000.0f));
	CHECK(lowest < -0.99f);
	CHECK(highest > 0.99f);
	// a lean to one side would drift the whole picture rather than shake it
	CHECK(std::abs(total / 100000.0f) < 0.02f);
}

TEST_CASE("successive jitter values differ", "[emu]")
{
	vector_jitter jitter;
	float const first = jitter.next();
	CHECK(jitter.next() != first);
}

TEST_CASE("jitter values outside the limits are brought back inside them", "[emu]")
{
	CHECK(vector_jitter::limit_percent(-1.0f) == 0.0f);
	CHECK(vector_jitter::limit_percent(0.1f) == 0.1f);
	CHECK(vector_jitter::limit_percent(5.0f) == 0.2f);
}
