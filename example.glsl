#version 450
#extension GL_ARB_separate_shader_objects : enable

struct Ex1 { vec4 p1; };
struct Ex2
{
	struct Ex3 { vec4 p2; };
	Ex3 e3;
};

uniform Ex1 e1;
uniform Ex2 e2;
void main() {}
