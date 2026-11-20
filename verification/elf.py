"""Read linked x86-64 ELF symbols and cross-check section and load mappings."""
import os
import re
import struct
import subprocess

def require(condition, message):
    if not condition:
        raise ValueError(message)


def symbol_extent(binary, symbol):
    names = subprocess.check_output(["nm", "-S", "--defined-only", binary], text=True)
    matches = re.findall(rf"^([0-9a-fA-F]+) ([0-9a-fA-F]+) [tT] {re.escape(symbol)}$", names, re.M)
    require(len(matches) == 1, f"expected one defined {symbol} in {binary}")
    addr, size = matches[0]
    return int(addr, 16), int(size, 16)



ELF_HEADER = struct.Struct("<16sHHIQQQIHHHHHH")
PROGRAM_HEADER = struct.Struct("<IIQQQQQQ")


def executable_offset(file, pc, size):
    """Translate a complete symbol range through its executable PT_LOAD."""
    end = pc + size
    require(0 <= pc < end <= 2**64, "invalid symbol range")
    file_size = os.fstat(file.fileno()).st_size
    header = file.read(ELF_HEADER.size)
    require(len(header) == ELF_HEADER.size, "truncated ELF header")
    ident, kind, machine, _, _, phoff, _, _, _, stride, count, *_ = ELF_HEADER.unpack(header)
    require(ident[:6] == b"\x7fELF\x02\x01" and machine == 62 and kind in (2, 3),
            "requires a linked little-endian x86-64 ELF")
    require(stride >= PROGRAM_HEADER.size and phoff + count * stride <= file_size,
            "invalid ELF program header table")
    offset = None
    for index in range(count):
        file.seek(phoff + index * stride)
        tag, flags, pos, addr, _, filesz, memsz, _ = PROGRAM_HEADER.unpack(file.read(PROGRAM_HEADER.size))
        if tag != 1:  # PT_LOAD
            continue
        require(filesz <= memsz and pos + filesz <= file_size and addr + memsz <= 2**64,
                "invalid PT_LOAD extent")
        if not memsz or addr >= end or pc >= addr + memsz:
            continue
        require(offset is None and flags & 1 and addr <= pc and end <= addr + filesz,
                "symbol needs one executable, file-backed PT_LOAD mapping")
        offset = pos + pc - addr
    require(offset is not None, "symbol outside loadable segments")
    return offset


def symbol_bytes(binary, pc, size):
    sections = subprocess.check_output(["objdump", "-h", "-j", ".text", binary], text=True)
    match = re.search(r"^\s*\d+ \.text\s+(\w+)\s+(\w+)\s+\w+\s+(\w+)", sections, re.M)
    require(match, "missing ELF text section")
    length, address, section_offset = (int(x, 16) for x in match.groups())
    require(address <= pc and pc + size <= address + length, "symbol outside text section")
    with open(binary, "rb") as file:
        offset = executable_offset(file, pc, size)
        require(offset == section_offset + pc - address, ".text and PT_LOAD disagree on symbol offset")
        file.seek(offset)
        raw = file.read(size)
    require(len(raw) == size, "truncated symbol")
    return raw
