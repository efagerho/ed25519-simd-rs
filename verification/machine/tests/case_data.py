"""Portable case format for the unmasked EVEX.512 instruction subset."""
import random

# Keys are also the Intel mnemonic. Operands follow Intel syntax.
OPS = {
    "vmovdqa64": ("Copy", "rr"), "vmovdqu64": ("Load", "rbd"),
    "vpxorq": ("Xor", "rrr"), "vpaddq": ("Add", "rrr"),
    "vpsubq": ("Sub", "rrr"), "vpmullq": ("Mul", "rrr"), "vpandq": ("And", "rrr"),
    "vpsllq": ("Shl", "rri"), "vpsrlq": ("Shr", "rri"),
    "vpmadd52luq": ("Madd false", "rrr"), "vpmadd52huq": ("Madd true", "rrr"),
}
GPRS = "rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15".split()
BOUNDS = {"r": (0, 32), "b": (0, 16), "d": (-(2**31), 2**31), "i": (0, 256)}
WORD = 2**64
REGISTER_IDS = {str(n) for n in range(32)}


def vector(value):
    return (isinstance(value, list) and len(value) == 8 and
            all(type(x) is int and 0 <= x < WORD for x in value))


def validate(case):
    if not isinstance(case, dict):
        raise ValueError("expected a JSON object for each case")
    if not isinstance(case.get("id"), str) or not case["id"]:
        raise ValueError("expected a nonempty case id")
    ins = case.get("instruction")
    if not isinstance(ins, list) or not ins or not isinstance(ins[0], str) or ins[0] not in OPS:
        raise ValueError(f"unsupported instruction: {ins}")
    kinds = OPS[ins[0]][1]
    if len(ins) != len(kinds) + 1:
        raise ValueError(f"wrong operand count: {ins}")
    for kind, n in zip(kinds, ins[1:]):
        lo, hi = BOUNDS[kind]
        if type(n) is not int or not lo <= n < hi:
            raise ValueError(f"operand out of range: {ins}")
    overrides = case.get("registers", {})
    if not isinstance(overrides, dict):
        raise ValueError("registers must map ZMM numbers to qword vectors")
    for k, vals in overrides.items():
        if k not in REGISTER_IDS or not vector(vals):
            raise ValueError(f"invalid register initializer {k}")
    if "memory" in case or ins[0] == "vmovdqu64":
        if not vector(case.get("memory")):
            raise ValueError("load memory must contain eight qwords")
    if "expected" in case and not vector(case["expected"]):
        raise ValueError("expected result must contain eight qwords")
    if "bytes" in case and (not isinstance(case["bytes"], str) or not 1 <= len(bytes.fromhex(case["bytes"])) <= 15):
        raise ValueError("expected 1 to 15 instruction bytes")
    for field in ("campaign_seed", "export_seed"):
        if field in case and type(case[field]) is not int:
            raise ValueError(f"{field} must be an integer")


def registers(case):
    overrides = case.get("registers", {})
    return [overrides.get(str(i), list(range(8*i, 8*i+8))) for i in range(32)]


def random_state(case_id, instruction, rng):
    regs = {str(n): [rng.getrandbits(64) for _ in range(8)]
            for n, kind in zip(instruction[1:], OPS[instruction[0]][1]) if kind == "r"}
    case = {"id": case_id, "instruction": instruction, "registers": regs}
    if instruction[0] == "vmovdqu64":
        case["memory"] = [rng.getrandbits(64) for _ in range(8)]
    return case


def campaign(seed, count):
    rng = random.Random(seed)
    names = list(OPS)
    for i in range(count):
        op = names[i % len(names)]
        args = [rng.randrange(*BOUNDS[k]) for k in OPS[op][1]]
        yield {**random_state(f"random/{seed}/{i}", [op, *args], rng), "campaign_seed": seed}
