#!/usr/bin/env python3
"""Regenerate cached_add.json with Python integers and the addition formulas."""
import json
from pathlib import Path
import random

P = 2**255 - 19
B = 2**51


def value(limbs):
    return sum(x * B**i for i, x in enumerate(limbs)) % P


def add(point, cached, affine):
    x, y, z, t = map(value, point)
    ymx, ypx, t2d, z2 = map(value, cached)
    a = (y - x) * ymx % P
    b = (y + x) * ypx % P
    c = t * t2d % P
    d = 2*z % P if affine else z*z2 % P
    e, f, g, h = (b-a) % P, (d-c) % P, (d+c) % P, (b+a) % P
    return [(v % P).to_bytes(32, "little").hex() for v in (e*f, g*h, f*g, e*h)]


def generate():
    edges = [[0]*5, [1, 0, 0, 0, 0], [B-19]+[B-1]*4, [B-1]*5,
             [2**52-1]*5, [B]*5, [0, 2**52-1, 0, 2**52-1, 0],
             [2**52-1, 0, 2**52-1, 0, 2**52-1]]
    cases = [(f"uniform-{i}", [e]*4, [e]*4) for i,e in enumerate(edges)]
    cases += [(f"mixed-{i}", [edges[(i+j)%8] for j in range(4)],
               [edges[(3*i+2*j)%8] for j in range(4)]) for i in range(8)]
    rng = random.Random(0xCA_C4ED_ADD)
    def field():
        return [rng.randrange(2**52) for _ in range(5)]
    cases += [(f"random-{i}", [field() for _ in range(4)], [field() for _ in range(4)])
              for i in range(16)]
    return [dict(name=name, point=point, cached=cached,
                 projective=add(point, cached, False), affine=add(point, cached, True))
            for name,point,cached in cases]


if __name__ == "__main__":
    Path(__file__).with_name("cached_add.json").write_text(json.dumps(generate(), indent=2) + "\n")
