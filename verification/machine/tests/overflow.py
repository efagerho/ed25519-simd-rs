"""Deterministic qword boundary cases. All expected values use Python integers."""
from itertools import count, islice, product

from case_data import WORD

LIMB = 2**52
EDGES = sorted({0, 1, 2, WORD - 2, WORD - 1} | {
    2**bit + offset for bit in (26, 32, 51, 52, 63) for offset in (-1, 0, 1)
})


def vectors(mnemonic, group, input_regs, rows):
    """Pack scalar rows (inputs followed by expected result) into eight lanes."""
    rows = iter(rows)
    for index in count():
        lanes = list(islice(rows, 8))
        if not lanes:
            return
        lanes.extend([lanes[-1]] * (8 - len(lanes)))
        *inputs, expected = zip(*lanes)
        yield {
            "id": f"overflow/{mnemonic}/{group}/{index}",
            "instruction": [mnemonic, 0, 1, 2],
            "registers": {str(reg): list(values) for reg, values in zip(input_regs, inputs)},
            "expected": list(expected),
        }


def ifma_rows(high):
    for a, b in product(EDGES, repeat=2):
        upper, lower = divmod((a % LIMB) * (b % LIMB), LIMB)
        term = upper if high else lower
        # Choose the old destination to land exactly on each boundary or its neighbors.
        for boundary in (WORD, LIMB):
            for target in (boundary - 1, boundary, boundary + 1):
                acc = target - term
                if 0 <= acc < WORD:
                    yield a, b, acc, target % WORD


def overflow_cases():
    yield from vectors("vpaddq", "sum", (1, 2),
                       ((a, b, (a + b) % WORD) for a, b in product(EDGES, repeat=2)))
    yield from vectors("vpaddq", "carry", (1, 2),
                       ((a, target - a, target % WORD) for a in EDGES
                        for target in (WORD - 1, WORD, WORD + 1) if 0 <= target - a < WORD))
    yield from vectors("vpmullq", "product", (1, 2),
                       ((a, b, (a * b) % WORD) for a, b in product(EDGES, repeat=2)))
    for mnemonic, high in (("vpmadd52luq", False), ("vpmadd52huq", True)):
        yield from vectors(mnemonic, "accumulate", (1, 2, 0), ifma_rows(high))

    lanes = [0, 1, 2**51, LIMB - 1, 2**63 - 1, 2**63, WORD - 2, WORD - 1]
    for count in range(256):
        scale = 2**count
        for mnemonic, expected in (("vpsllq", [(v * scale) % WORD for v in lanes]),
                                   ("vpsrlq", [v // scale for v in lanes])):
            yield {"id": f"overflow/{mnemonic}/{count}", "instruction": [mnemonic, 0, 1, count],
                   "registers": {"1": lanes}, "expected": expected}
