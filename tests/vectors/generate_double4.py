#!/usr/bin/env python3
"""Regenerate double4.json using only Python integer arithmetic modulo p."""
import json
from pathlib import Path
import random

P = 2**255 - 19
B = 2**51


def value(limbs):
    return sum(limb * B**i for i, limb in enumerate(limbs)) % P


def double4(x, y, z):
    x, y, z = map(value, (x, y, z))
    for _ in range(4):
        a, b, c = x*x % P, y*y % P, z*z % P
        e, g = ((x+y)**2 - a - b) % P, (b-a) % P
        f, h = (g-2*c) % P, (-a-b) % P
        x, y, z, t = e*f % P, g*h % P, f*g % P, e*h % P
    return [v.to_bytes(32, "little").hex() for v in (x, y, z, t)]


def generate():
    edges = [
        [0]*5,
        [1, 0, 0, 0, 0],
        [B-19] + [B-1]*4,
        [B-1]*5,
        [2**52-1, 2**52-2] + [2**52-1]*3,
        [2**60-1, 2**52-512] + [2**52-1]*3,
        [B-1, B, B+1, 2**52-1, B-1],
        [0] + [2**52-1]*4,
    ]
    inputs = [(f"uniform-{i}", row, row, row) for i, row in enumerate(edges)]
    inputs += [(f"mixed-{i}", row, edges[(3*i+1) % 8], edges[(5*i+2) % 8])
               for i, row in enumerate(edges)]
    rng = random.Random(0xD04B1E4)

    def field():
        lo = rng.randrange(2**60)
        return [lo, rng.randrange(2**52 - (lo >> 51))] + [rng.randrange(2**52) for _ in range(3)]

    inputs += [(f"random-{i}", field(), field(), field()) for i in range(16)]
    result = []
    for name, x, y, z in inputs:
        for limbs in (x, y, z):
            assert 0 <= limbs[0] < 2**60
            assert 0 <= limbs[1] + (limbs[0] >> 51) < 2**52
            assert all(0 <= limb < 2**52 for limb in limbs[2:])
        result.append(dict(name=name, x=x, y=y, z=z, output=double4(x, y, z)))
    return result


if __name__ == "__main__":
    Path(__file__).with_name("double4.json").write_text(json.dumps(generate(), indent=2) + "\n")
