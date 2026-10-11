#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
miniOS 0.5
==========
A single-file educational virtual OS with:
  - VM32/MEXE2 execution environment
  - simple MiniLang compiler/interpreter
  - virtual filesystem
  - process table
  - 2D graphics API with portable backend abstraction
  - first real JVM layer able to load Java .class and .jar files
  - Java bytecode interpreter for a useful initial subset

Everything is implemented with Python's standard library only.

This version is a JVM foundation, not a Minecraft-compatible JVM yet.
Minecraft will require a much larger Java runtime, threading, NIO/networking,
ZIP/JAR support beyond loading, exceptions, class initialization, arrays,
reflection, graphics/OpenGL integration, native methods, etc.
"""

import datetime
import contextlib
import io
import json
import os
import shlex
import glob
from fnmatch import fnmatchcase
import base64
import ast
import struct
import sys
import time
import zipfile
import zlib
import ntpath
import re
import socket
import urllib.error
import urllib.parse
import urllib.request
import threading
import queue
import traceback
import platform
import ctypes
import ctypes.util
from pathlib import Path
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple

VERSION = "miniOS 0.5"
HOSTNAME = "minios"
RAM_SIZE = 16 * 1024 * 1024  # 16 MiB par processus VM32
WORD_MASK = 0xFFFFFFFF
MAX_VM_INSTRUCTIONS = 1_000_000
JVM_MAX_STEPS = 2_000_000
VM_TIMESLICE = 2000            # instructions par tranche pour un processus de fond
VM_YIELD_SECONDS = 0.001       # laisse les autres processus/terminal respirer
DEBUG_TRACE_MAX = 100000        # sécurité haute; le fichier peut dépasser, la trace mémoire est bornée


def runtime_storage_dir() -> str:
    """Directory where miniOS stores persistent virtual-disk data."""
    try:
        here = os.path.dirname(os.path.abspath(__file__))
        if here:
            return here
    except NameError:
        pass
    return os.getcwd()


MINIOS_DISK_FILE = os.environ.get(
    "MINIOS_DISK_FILE",
    os.path.join(runtime_storage_dir(), "minios_disk.json")
)


# ================================================================
# Utilities
# ================================================================

def rtf_to_text(data: bytes) -> str:
    """Convertit un RTF simple en texte brut.

    miniOS importe parfois des fichiers `.mini` créés avec WordPad ou un
    éditeur enrichi : ces fichiers commencent alors par ``{\\rtf1`` au lieu
    de contenir directement le code MiniLang. Cette fonction retire les
    métadonnées RTF courantes, conserve le texte, les retours à la ligne,
    les tabulations et les caractères Unicode `\\uN`.
    """
    raw = data.decode("latin-1", errors="replace")
    out: List[str] = []
    i = 0
    depth = 0
    # Destinations RTF dont le contenu ne doit pas apparaître dans le fichier
    # MiniLang (polices, couleurs, images, métadonnées...).
    skip_stack: List[bool] = []
    skip_group = False
    ignorable_destinations = {
        "fonttbl", "colortbl", "stylesheet", "info", "generator",
        "pict", "object", "header", "footer", "headerl", "headerr",
        "footerl", "footerr", "filetbl", "themedata", "xmlnstbl",
    }

    def append_text(text: str):
        if not skip_group:
            out.append(text)

    while i < len(raw):
        ch = raw[i]
        if ch == "{":
            depth += 1
            skip_stack.append(skip_group)
            i += 1
            continue
        if ch == "}":
            if depth > 0:
                depth -= 1
            skip_group = skip_stack.pop() if skip_stack else False
            i += 1
            continue
        if ch != "\\":
            append_text(ch)
            i += 1
            continue

        i += 1
        if i >= len(raw):
            break
        c = raw[i]

        # Caractères échappés : \\, \{, \}
        if c in "\\{}":
            append_text(c)
            i += 1
            continue

        # Caractère hexadécimal RTF : \'hh
        if c == "'" and i + 2 < len(raw):
            hh = raw[i + 1:i + 3]
            try:
                append_text(bytes([int(hh, 16)]).decode("cp1252", errors="replace"))
                i += 3
                continue
            except ValueError:
                pass

        # Contrôle RTF : nom de commande alpha + paramètre signé optionnel.
        start = i
        while i < len(raw) and raw[i].isalpha():
            i += 1
        word = raw[start:i]
        sign = 1
        if i < len(raw) and raw[i] in "+-":
            if raw[i] == "-":
                sign = -1
            i += 1
        num_start = i
        while i < len(raw) and raw[i].isdigit():
            i += 1
        number = None
        if i > num_start:
            number = sign * int(raw[num_start:i])
        if i < len(raw) and raw[i] == " ":
            i += 1

        if not word:
            # Contrôle à un caractère inconnu : on ignore le slash et
            # conserve le caractère suivant si nécessaire.
            if c == "~":
                append_text("\\u00A0" if False else " ")
            elif c == "-":
                append_text("-")
            i += 1
            continue

        if word in ignorable_destinations:
            skip_group = True
            continue
        if word in {"pard", "plain"}:
            continue
        if word in {"par", "line"}:
            append_text("\n")
            continue
        if word == "tab":
            append_text("\t")
            continue
        if word == "emdash":
            append_text("—")
            continue
        if word == "endash":
            append_text("–")
            continue
        if word == "bullet":
            append_text("•")
            continue
        if word == "lquote":
            append_text("‘")
            continue
        if word == "rquote":
            append_text("’")
            continue
        if word == "ldblquote":
            append_text("“")
            continue
        if word == "rdblquote":
            append_text("”")
            continue
        if word == "u" and number is not None:
            # RTF stocke Unicode en UTF-16 signé. Le caractère de secours
            # qui suit doit être ignoré.
            codepoint = number if number >= 0 else number + 65536
            try:
                append_text(chr(codepoint))
            except ValueError:
                append_text("�")
            if i < len(raw):
                if raw[i] == "?":
                    i += 1
                elif raw[i] == "\\" and i + 1 < len(raw) and raw[i + 1] == "'":
                    pass
            continue
        # Tous les autres contrôles de mise en forme sont ignorés.

    text_value = "".join(out)
    # Nettoyage léger des sauts de lignes artificiels au début/à la fin.
    return text_value.replace("\r\n", "\n").replace("\r", "\n").strip("\x00")


def maybe_decode_rtf(data: bytes) -> Tuple[bytes, bool]:
    """Retourne (contenu, converti) et convertit automatiquement le RTF."""
    sample = data[:128].lstrip()
    if sample.startswith(b"{\\rtf"):
        return rtf_to_text(data).encode("utf-8"), True
    return data, False


TEXT_EXTENSIONS = {
    ".mini", ".txt", ".text", ".md", ".markdown", ".java", ".json",
    ".xml", ".html", ".htm", ".css", ".js", ".ts", ".py", ".c",
    ".h", ".cpp", ".hpp", ".csv", ".ini", ".cfg", ".conf", ".log",
    ".sh", ".ps1", ".bat", ".cmd", ".yaml", ".yml", ".toml",
}

def decode_text_bytes(data: bytes) -> str:
    """Décode du texte provenant du PC en privilégiant UTF-8.

    Ordre de détection : BOM UTF-8/UTF-16, UTF-8 strict, puis Windows-1252.
    Le fallback CP1252 évite que les fichiers Windows enregistrés en ANSI
    transforment les accents en caractères de remplacement.
    """
    if data.startswith(b"\xef\xbb\xbf"):
        return data[3:].decode("utf-8", errors="strict")
    if data.startswith(b"\xff\xfe") or data.startswith(b"\xfe\xff"):
        return data.decode("utf-16", errors="strict").lstrip("\ufeff")
    try:
        return data.decode("utf-8", errors="strict")
    except UnicodeDecodeError:
        return data.decode("cp1252", errors="replace")

def encode_text_utf8(text: str) -> bytes:
    """Encode tout texte de miniOS en UTF-8 sans BOM."""
    return str(text).encode("utf-8")

def normalize_imported_text(data: bytes, filename: str) -> Tuple[bytes, bool]:
    """Normalise les fichiers texte importés en UTF-8.

    Les fichiers binaires (.mexe, images, etc.) sont laissés intacts.
    """
    data, converted_rtf = maybe_decode_rtf(data)
    ext = os.path.splitext(filename)[1].lower()
    if converted_rtf or ext in TEXT_EXTENSIONS:
        text = decode_text_bytes(data)
        return encode_text_utf8(text), converted_rtf
    return data, converted_rtf

def u32(x: int) -> int:
    return x & WORD_MASK


def s32(x: int) -> int:
    x &= WORD_MASK
    return x if x < 0x80000000 else x - 0x100000000


def read_u1(f: io.BytesIO) -> int:
    b = f.read(1)
    if len(b) != 1:
        raise ValueError("Fichier tronqué")
    return b[0]


def read_u2(f: io.BytesIO) -> int:
    b = f.read(2)
    if len(b) != 2:
        raise ValueError("Fichier tronqué")
    return struct.unpack(">H", b)[0]


def read_u4(f: io.BytesIO) -> int:
    b = f.read(4)
    if len(b) != 4:
        raise ValueError("Fichier tronqué")
    return struct.unpack(">I", b)[0]


def read_i1(f: io.BytesIO) -> int:
    b = f.read(1)
    if len(b) != 1:
        raise ValueError("Fichier tronqué")
    return struct.unpack(">b", b)[0]


def read_i2(f: io.BytesIO) -> int:
    b = f.read(2)
    if len(b) != 2:
        raise ValueError("Fichier tronqué")
    return struct.unpack(">h", b)[0]


def read_i4(f: io.BytesIO) -> int:
    b = f.read(4)
    if len(b) != 4:
        raise ValueError("Fichier tronqué")
    return struct.unpack(">i", b)[0]


def read_bytes(f: io.BytesIO, n: int) -> bytes:
    b = f.read(n)
    if len(b) != n:
        raise ValueError("Fichier tronqué")
    return b


def desc_arg_slots(descriptor: str) -> int:
    """Count JVM method argument local-variable slots (long/double = 2)."""
    if not descriptor.startswith("("):
        raise ValueError(f"Descripteur invalide: {descriptor}")
    i = 1
    slots = 0
    while i < len(descriptor) and descriptor[i] != ")":
        c = descriptor[i]
        if c in "BCSIZFJ D":
            c = c.strip()
            if not c:
                i += 1
                continue
            slots += 2 if c in "JD" else 1
            i += 1
        elif c == "L":
            j = descriptor.find(";", i)
            if j < 0:
                raise ValueError(f"Descripteur invalide: {descriptor}")
            slots += 1
            i = j + 1
        elif c == "[":
            i += 1
            while i < len(descriptor) and descriptor[i] == "[":
                i += 1
            if i < len(descriptor) and descriptor[i] == "L":
                j = descriptor.find(";", i)
                if j < 0:
                    raise ValueError(f"Descripteur invalide: {descriptor}")
                i = j + 1
            else:
                i += 1
            slots += 1
        else:
            raise ValueError(f"Type inconnu dans descriptor: {descriptor}")
    if i >= len(descriptor) or descriptor[i] != ")":
        raise ValueError(f"Descripteur invalide: {descriptor}")
    return slots


def method_return_type(descriptor: str) -> str:
    j = descriptor.find(")")
    return descriptor[j + 1:] if j >= 0 else "V"


def parse_method_descriptor(descriptor: str) -> List[str]:
    args: List[str] = []
    if not descriptor.startswith("("):
        raise ValueError(descriptor)
    i = 1
    while i < len(descriptor) and descriptor[i] != ")":
        start = i
        if descriptor[i] == "[":
            while i < len(descriptor) and descriptor[i] == "[":
                i += 1
            if i < len(descriptor) and descriptor[i] == "L":
                end = descriptor.find(";", i)
                if end < 0:
                    raise ValueError(descriptor)
                i = end + 1
            else:
                i += 1
        elif descriptor[i] == "L":
            end = descriptor.find(";", i)
            if end < 0:
                raise ValueError(descriptor)
            i = end + 1
        else:
            i += 1
        args.append(descriptor[start:i])
    return args


# ================================================================
# MEXE2 + VM32
# ================================================================

MEXE_MAGIC = b"MEXE2\x00"
MEXE_VERSION = 1
ARCH_VM32 = 1


class MEXE:
    HEADER = 16

    def __init__(self, code: bytes = b"", data: bytes = b"", entry: int = 0):
        self.code = code
        self.data = data
        self.entry = entry

    def encode(self) -> bytes:
        header = struct.pack(">6sBBHHI", MEXE_MAGIC, MEXE_VERSION, ARCH_VM32,
                             len(self.code), len(self.data), self.entry)
        return header + self.code + self.data

    @classmethod
    def decode(cls, blob: bytes) -> "MEXE":
        if len(blob) < 16:
            raise ValueError("MEXE trop petit")
        magic, version, arch, code_size, data_size, entry = struct.unpack(">6sBBHHI", blob[:16])
        if magic != MEXE_MAGIC:
            raise ValueError("MEXE magic invalide")
        if version != MEXE_VERSION or arch != ARCH_VM32:
            raise ValueError("Version/architecture MEXE incompatible")
        header_len = 16
        end_code = header_len + code_size
        end_data = end_code + data_size
        if len(blob) < end_data:
            raise ValueError("MEXE tronqué")
        return cls(blob[header_len:end_code], blob[end_code:end_data], entry)


class MemoryManager:
    HEAP_START = 0x00100000      # 1 MiB
    HEAP_END = 0x00BFFFFF        # ~11 MiB

    def __init__(self, size: int = RAM_SIZE):
        self.size = size
        self.limit = min(self.size, self.HEAP_END + 1)
        self.next_ptr = self.HEAP_START
        self.blocks: Dict[int, int] = {}
        self.kinds: Dict[int, str] = {}
        self.free_ranges: List[Tuple[int, int]] = []

    def _insert_free_range(self, start: int, size: int):
        if size <= 0:
            return
        self.free_ranges.append((int(start), int(size)))
        self.free_ranges.sort()
        merged: List[Tuple[int, int]] = []
        for s, n in self.free_ranges:
            if merged and merged[-1][0] + merged[-1][1] >= s:
                prev_s, prev_n = merged[-1]
                end = max(prev_s + prev_n, s + n)
                merged[-1] = (prev_s, end - prev_s)
            else:
                merged.append((s, n))
        self.free_ranges = merged

    def alloc(self, size: int, kind: str = "raw", gc_cpu=None) -> int:
        size = max(1, int(size))
        size = (size + 3) & ~3

        # Réutiliser en priorité les blocs libérés.
        for i, (start, available) in enumerate(self.free_ranges):
            if available >= size:
                ptr = start
                if available == size:
                    self.free_ranges.pop(i)
                else:
                    self.free_ranges[i] = (start + size, available - size)
                self.blocks[ptr] = size
                self.kinds[ptr] = str(kind)
                return ptr

        if self.next_ptr + size > self.limit and gc_cpu is not None:
            self.collect(gc_cpu)
            for i, (start, available) in enumerate(self.free_ranges):
                if available >= size:
                    ptr = start
                    if available == size:
                        self.free_ranges.pop(i)
                    else:
                        self.free_ranges[i] = (start + size, available - size)
                    self.blocks[ptr] = size
                    self.kinds[ptr] = str(kind)
                    return ptr

        if self.next_ptr + size > self.limit:
            raise MemoryError(
                f"heap VM32 pleine ({self.used} octets utilisés, "
                f"{self.available} octets disponibles)"
            )
        ptr = self.next_ptr
        self.next_ptr += size
        self.blocks[ptr] = size
        self.kinds[ptr] = str(kind)
        return ptr

    def free(self, ptr: int) -> bool:
        ptr = int(ptr)
        size = self.blocks.pop(ptr, None)
        self.kinds.pop(ptr, None)
        if size is None:
            return False
        self._insert_free_range(ptr, size)
        return True

    def collect(self, cpu) -> int:
        """Mark-and-sweep léger pour les objets VM32 gérés par ce processus.

        Les chaînes temporaires créées par str()/concaténation/etc. sont ainsi
        récupérées lorsqu'elles ne sont plus référencées par les registres, la
        pile, les variables globales ou les tableaux.
        """
        if not self.blocks:
            return 0

        roots = set()

        def add_root(value):
            try:
                ptr = int(value) & WORD_MASK
            except Exception:
                return
            if ptr in self.blocks:
                roots.add(ptr)

        for value in getattr(cpu, "reg", []):
            add_root(value)

        # Pile utilisateur : les POP effacent désormais leurs anciennes cases,
        # ce qui évite que des pointeurs temporaires y restent artificiellement.
        sp = max(0, int(getattr(cpu, "sp", len(cpu.memory) - 4)))
        stack_end = min(len(cpu.memory) - 4, self.size - 4)
        for addr in range(sp, stack_end + 1, 4):
            try:
                add_root(cpu.read32(addr))
            except Exception:
                break

        # Variables globales compilées dans la zone haute de la VM32.
        global_base = int(getattr(cpu, "global_base", 0x00C00000))
        global_count = min(4096, int(getattr(cpu, "global_count", 1024)))
        if 0 <= global_base < len(cpu.memory):
            end = min(len(cpu.memory), global_base + global_count * 4)
            for addr in range(global_base, end, 4):
                if addr + 4 > len(cpu.memory):
                    break
                try:
                    add_root(cpu.read32(addr))
                except Exception:
                    break

        # Les blocs eux-mêmes peuvent contenir des pointeurs (tableaux,
        # structures construites manuellement avec write32(), etc.).
        marked = set(roots)
        pending = list(roots)
        while pending:
            ptr = pending.pop()
            size = self.blocks.get(ptr)
            if size is None:
                continue
            for addr in range(ptr, ptr + size - 3, 4):
                if addr + 4 > len(cpu.memory):
                    break
                try:
                    child = cpu.read32(addr)
                except Exception:
                    continue
                if child in self.blocks and child not in marked:
                    marked.add(child)
                    pending.append(child)

        dead = [ptr for ptr in list(self.blocks) if ptr not in marked]
        recovered = 0
        for ptr in dead:
            size = self.blocks.get(ptr, 0)
            recovered += size
            self.free(ptr)
        return recovered

    @property
    def used(self) -> int:
        return sum(self.blocks.values())

    @property
    def available(self) -> int:
        return max(0, (self.limit - self.HEAP_START) - self.used)


class CPU:
    # VM32 opcodes
    NOP = 0x00
    MOVI = 0x01
    MOVR = 0x02
    ADD = 0x03
    SUB = 0x04
    MUL = 0x05
    DIV = 0x06
    CMP = 0x07
    JMP = 0x08
    JZ = 0x09
    JNZ = 0x0A
    PUSH = 0x0B
    POP = 0x0C
    CALL = 0x0D
    RET = 0x0E
    LOAD8 = 0x0F
    STORE8 = 0x10
    LOAD32 = 0x11
    STORE32 = 0x12
    INC = 0x13
    DEC = 0x14
    PRINT = 0x15
    SYSCALL = 0x16
    HALT = 0x17
    AND = 0x18
    OR = 0x19
    XOR = 0x1A
    SHL = 0x1B
    SHR = 0x1C
    JLT = 0x1D
    JLE = 0x1E
    JGT = 0x1F
    JGE = 0x20
    GETSP = 0x21
    MOD = 0x22
    NOT = 0x23

    def __init__(self, memory: bytearray, syscall_handler=None):
        self.memory = memory
        self.syscall_handler = syscall_handler
        self.reg = [0] * 8
        self.pc = 0
        self.sp = len(self.memory) - 4
        self.flags = {"zero": False, "negative": False, "carry": False, "less": False, "greater": False}
        self.halted = False
        self.exit_code = 0
        self.code_start = 0
        self.code_end = 0
        self.data_start = 0
        self.data_end = 0
        self.steps = 0
        self.input_code = b""
        self.debug_hook = None

    def reset(self):
        self.reg = [0] * 8
        self.pc = 0
        self.sp = len(self.memory) - 4
        self.flags = {"zero": False, "negative": False, "carry": False, "less": False, "greater": False}
        self.halted = False
        self.exit_code = 0
        self.data_start = 0
        self.data_end = 0
        self.steps = 0

    def load(self, exe: MEXE):
        self.reset()
        if 16 + len(exe.code) + len(exe.data) > len(self.memory):
            raise MemoryError("MEXE trop grand pour VM32")
        self.memory[:] = b"\x00" * len(self.memory)
        self.memory[0:len(exe.code)] = exe.code
        data_addr = len(exe.code)
        self.memory[data_addr:data_addr + len(exe.data)] = exe.data
        self.pc = exe.entry
        self.code_start = 0
        self.code_end = len(exe.code)
        self.data_start = data_addr
        self.data_end = data_addr + len(exe.data)

    def fetch8(self) -> int:
        if self.pc >= len(self.memory):
            raise RuntimeError("PC hors mémoire")
        x = self.memory[self.pc]
        self.pc += 1
        return x

    def fetch16(self) -> int:
        return (self.fetch8() << 8) | self.fetch8()

    def fetch32(self) -> int:
        return (self.fetch16() << 16) | self.fetch16()

    def read32(self, addr: int) -> int:
        if addr < 0 or addr + 4 > len(self.memory):
            raise RuntimeError("lecture mémoire invalide")
        return struct.unpack(">I", self.memory[addr:addr + 4])[0]

    def write32(self, addr: int, value: int):
        if addr < 0 or addr + 4 > len(self.memory):
            raise RuntimeError("écriture mémoire invalide")
        self.memory[addr:addr + 4] = struct.pack(">I", value & WORD_MASK)

    def push(self, value: int):
        self.sp = (self.sp - 4) & WORD_MASK
        self.write32(self.sp, value)

    def pop(self) -> int:
        old_sp = self.sp
        value = self.read32(old_sp)
        # Effacer l'ancienne case évite de conserver artificiellement un
        # pointeur de chaîne/tableau dans la pile et permet au GC de le libérer.
        self.write32(old_sp, 0)
        self.sp = (self.sp + 4) & WORD_MASK
        return value

    def update_flags(self, value: int):
        v = u32(value)
        self.flags["zero"] = v == 0
        self.flags["negative"] = bool(v & 0x80000000)

    def run(self, max_steps: int = MAX_VM_INSTRUCTIONS):
        while not self.halted and self.steps < max_steps:
            self.step()
        if not self.halted:
            raise RuntimeError("VM32: limite d'instructions atteinte")
        return self.exit_code

    def _step_impl(self):
        self.steps += 1
        op = self.fetch8()
        if op == self.NOP:
            return
        if op == self.MOVI:
            r = self.fetch8(); imm = self.fetch32(); self.reg[r & 7] = imm; self.update_flags(imm)
        elif op == self.MOVR:
            d = self.fetch8() & 7; s = self.fetch8() & 7; self.reg[d] = self.reg[s]; self.update_flags(self.reg[d])
        elif op in (self.ADD, self.SUB, self.MUL, self.DIV, self.MOD, self.AND, self.OR, self.XOR, self.SHL, self.SHR):
            d = self.fetch8() & 7; s = self.fetch8() & 7
            a = self.reg[d]; b = self.reg[s]
            if op == self.ADD: value = a + b
            elif op == self.SUB: value = a - b
            elif op == self.MUL: value = a * b
            elif op == self.DIV:
                if b == 0: raise ZeroDivisionError("VM32 division par zéro")
                aa, bb = s32(a), s32(b)
                q = abs(aa) // abs(bb)
                value = -q if (aa < 0) != (bb < 0) else q
            elif op == self.MOD:
                if b == 0: raise ZeroDivisionError("VM32 modulo par zéro")
                aa, bb = s32(a), s32(b)
                q = abs(aa) // abs(bb)
                q = -q if (aa < 0) != (bb < 0) else q
                value = aa - q * bb
            elif op == self.AND: value = a & b
            elif op == self.OR: value = a | b
            elif op == self.XOR: value = a ^ b
            elif op == self.SHL: value = a << (b & 31)
            else: value = s32(a) >> (b & 31)
            self.reg[d] = u32(value); self.update_flags(value)
        elif op == self.CMP:
            a = self.reg[self.fetch8() & 7]; b = self.reg[self.fetch8() & 7]
            sa, sb = s32(a), s32(b)
            v = u32(sa - sb); self.update_flags(v)
            self.flags["carry"] = a < b
            self.flags["less"] = sa < sb
            self.flags["greater"] = sa > sb
        elif op in (self.JMP, self.JZ, self.JNZ, self.JLT, self.JLE, self.JGT, self.JGE, self.CALL):
            addr = self.fetch16()
            if op == self.JMP: self.pc = addr
            elif op == self.JZ and self.flags["zero"]: self.pc = addr
            elif op == self.JNZ and not self.flags["zero"]: self.pc = addr
            elif op == self.JLT and self.flags["less"]: self.pc = addr
            elif op == self.JLE and (self.flags["less"] or self.flags["zero"]): self.pc = addr
            elif op == self.JGT and self.flags["greater"]: self.pc = addr
            elif op == self.JGE and (self.flags["greater"] or self.flags["zero"]): self.pc = addr
            elif op == self.CALL:
                self.push(self.pc); self.pc = addr
        elif op == self.GETSP:
            r = self.fetch8() & 7; self.reg[r] = self.sp; self.update_flags(self.reg[r])
        elif op == self.NOT:
            r = self.fetch8() & 7; self.reg[r] = u32(~self.reg[r]); self.update_flags(self.reg[r])
        elif op == self.RET:
            self.pc = self.pop()
        elif op == self.PUSH:
            self.push(self.reg[self.fetch8() & 7])
        elif op == self.POP:
            r = self.fetch8() & 7; self.reg[r] = self.pop(); self.update_flags(self.reg[r])
        elif op == self.LOAD8:
            d = self.fetch8() & 7; a = self.reg[self.fetch8() & 7]; self.reg[d] = self.memory[a]; self.update_flags(self.reg[d])
        elif op == self.STORE8:
            s = self.fetch8() & 7; a = self.reg[self.fetch8() & 7]; self.memory[a] = self.reg[s] & 0xFF
        elif op == self.LOAD32:
            d = self.fetch8() & 7; a = self.reg[self.fetch8() & 7]; self.reg[d] = self.read32(a); self.update_flags(self.reg[d])
        elif op == self.STORE32:
            s = self.fetch8() & 7; a = self.reg[self.fetch8() & 7]; self.write32(a, self.reg[s])
        elif op == self.INC:
            r = self.fetch8() & 7; self.reg[r] = u32(self.reg[r] + 1); self.update_flags(self.reg[r])
        elif op == self.DEC:
            r = self.fetch8() & 7; self.reg[r] = u32(self.reg[r] - 1); self.update_flags(self.reg[r])
        elif op == self.PRINT:
            r = self.fetch8() & 7; print(s32(self.reg[r]))
        elif op == self.SYSCALL:
            num = self.fetch8()
            if self.syscall_handler:
                self.syscall_handler(self, num)
        elif op == self.HALT:
            self.halted = True
        else:
            raise RuntimeError(f"VM32 opcode inconnu 0x{op:02X} à 0x{self.pc - 1:04X}")

    @staticmethod
    def _opcode_name(op: int) -> str:
        names = {
            CPU.NOP: "NOP", CPU.MOVI: "MOVI", CPU.MOVR: "MOVR", CPU.ADD: "ADD",
            CPU.SUB: "SUB", CPU.MUL: "MUL", CPU.DIV: "DIV", CPU.CMP: "CMP",
            CPU.JMP: "JMP", CPU.JZ: "JZ", CPU.JNZ: "JNZ", CPU.PUSH: "PUSH", CPU.POP: "POP",
            CPU.CALL: "CALL", CPU.RET: "RET", CPU.LOAD8: "LOAD8", CPU.STORE8: "STORE8",
            CPU.LOAD32: "LOAD32", CPU.STORE32: "STORE32", CPU.INC: "INC", CPU.DEC: "DEC",
            CPU.PRINT: "PRINT", CPU.SYSCALL: "SYSCALL", CPU.HALT: "HALT", CPU.AND: "AND",
            CPU.OR: "OR", CPU.XOR: "XOR", CPU.SHL: "SHL", CPU.SHR: "SHR", CPU.JLT: "JLT",
            CPU.JLE: "JLE", CPU.JGT: "JGT", CPU.JGE: "JGE", CPU.GETSP: "GETSP",
            CPU.MOD: "MOD", CPU.NOT: "NOT",
        }
        return names.get(int(op), f"OP_0x{int(op):02X}")

    @staticmethod
    def _syscall_name(num: int) -> str:
        try:
            if "Syscalls" in globals():
                for name, value in vars(Syscalls).items():
                    if name.isupper() and isinstance(value, int) and value == int(num):
                        return name
        except Exception:
            pass
        return f"SYSCALL_{int(num)}"

    def _trace(self, event: Dict[str, Any]):
        hook = getattr(self, "debug_hook", None)
        if hook is not None:
            hook(self, event)

    def step(self):
        start_pc = self.pc
        pre_regs = list(self.reg)
        pre_sp = self.sp
        pre_flags = dict(self.flags)
        op = self.memory[start_pc] if 0 <= start_pc < len(self.memory) else None
        try:
            self._step_impl()
        except BaseException as exc:
            end_pc = self.pc
            raw = bytes(self.memory[start_pc:min(len(self.memory), max(start_pc + 1, end_pc))]) if 0 <= start_pc < len(self.memory) else b""
            event = {
                "type": "instruction_error", "step": self.steps, "pc": start_pc, "pc_after": end_pc,
                "opcode": op, "opcode_name": self._opcode_name(op or 0),
                "raw": raw.hex(" "), "regs_before": pre_regs, "regs_after": list(self.reg),
                "sp_before": pre_sp, "sp_after": self.sp, "flags_before": pre_flags, "flags_after": dict(self.flags),
                "exception": f"{type(exc).__name__}: {exc}",
            }
            if op == self.SYSCALL and start_pc + 1 < len(self.memory):
                event["syscall"] = self._syscall_name(self.memory[start_pc + 1])
                event["syscall_num"] = int(self.memory[start_pc + 1])
            self._trace(event)
            raise
        end_pc = self.pc
        raw_end = min(len(self.memory), max(start_pc + 1, end_pc))
        raw = bytes(self.memory[start_pc:raw_end]) if 0 <= start_pc < len(self.memory) else b""
        event = {
            "type": "instruction", "step": self.steps, "pc": start_pc, "pc_after": end_pc,
            "opcode": op, "opcode_name": self._opcode_name(op or 0),
            "raw": raw.hex(" "), "regs_before": pre_regs, "regs_after": list(self.reg),
            "sp_before": pre_sp, "sp_after": self.sp, "flags_before": pre_flags, "flags_after": dict(self.flags),
        }
        if op == self.SYSCALL and start_pc + 1 < len(self.memory):
            event["syscall"] = self._syscall_name(self.memory[start_pc + 1])
            event["syscall_num"] = int(self.memory[start_pc + 1])
        self._trace(event)


# ================================================================
# Graphiques miniOS
# ================================================================


MAX_IMAGE_PIXELS = 16_777_216  # protection contre les images démesurées

@dataclass
class MiniImage:
    """Image RGB décodée par miniOS, indépendante de la plateforme."""
    width: int
    height: int
    pixels: List[int]  # 0xRRGGBB, ligne par ligne
    source: str = ""


def _checked_image_size(width: int, height: int) -> None:
    width = int(width); height = int(height)
    if width <= 0 or height <= 0:
        raise ValueError("dimensions d'image invalides")
    if width * height > MAX_IMAGE_PIXELS:
        raise ValueError(f"image trop grande: {width}x{height} pixels")


def _decode_ppm(raw: bytes, source: str) -> MiniImage:
    i = 0
    n = len(raw)
    def token() -> bytes:
        nonlocal i
        while i < n:
            if raw[i:i+1] == b'#':
                j = raw.find(b'\n', i)
                i = n if j < 0 else j + 1
            elif raw[i:i+1] in b' \t\r\n':
                i += 1
            else:
                break
        j = i
        while j < n and raw[j:j+1] not in b' \t\r\n#':
            j += 1
        t = raw[i:j]
        i = j
        return t
    magic = token()
    if magic not in (b'P6', b'P3'):
        raise ValueError("PPM non supporté")
    try:
        width = int(token()); height = int(token()); maxval = int(token())
    except Exception as exc:
        raise ValueError("en-tête PPM invalide") from exc
    _checked_image_size(width, height)
    if not (1 <= maxval <= 65535):
        raise ValueError("valeur max PPM invalide")
    pixels: List[int] = []
    if magic == b'P6':
        while i < n and raw[i:i+1] in b' \t\r\n': i += 1
        samples = 3 * width * height
        if maxval < 256:
            needed = samples
            if i + needed > n: raise ValueError("PPM tronqué")
            data = raw[i:i+needed]
            for j in range(0, len(data), 3):
                r,g,b = data[j], data[j+1], data[j+2]
                if maxval != 255:
                    r = r * 255 // maxval; g = g * 255 // maxval; b = b * 255 // maxval
                pixels.append((r<<16)|(g<<8)|b)
        else:
            needed = samples * 2
            if i + needed > n: raise ValueError("PPM 16 bits tronqué")
            vals = raw[i:i+needed]
            for j in range(0, len(vals), 6):
                r = (vals[j]<<8)|vals[j+1]; g = (vals[j+2]<<8)|vals[j+3]; b = (vals[j+4]<<8)|vals[j+5]
                r = r * 255 // maxval; g = g * 255 // maxval; b = b * 255 // maxval
                pixels.append((r<<16)|(g<<8)|b)
    else:
        for _ in range(samples):
            try: pixels.append((int(token())*255//maxval)<<16 | (int(token())*255//maxval)<<8 | (int(token())*255//maxval))
            except Exception as exc: raise ValueError("PPM ASCII tronqué") from exc
    return MiniImage(width, height, pixels, source)


def _decode_bmp(raw: bytes, source: str) -> MiniImage:
    if len(raw) < 54 or raw[:2] != b'BM':
        raise ValueError("BMP invalide")
    pixel_offset = struct.unpack_from('<I', raw, 10)[0]
    dib_size = struct.unpack_from('<I', raw, 14)[0]
    if dib_size < 40 or len(raw) < 14 + dib_size:
        raise ValueError("DIB BMP non supporté")
    width = struct.unpack_from('<i', raw, 18)[0]
    height_signed = struct.unpack_from('<i', raw, 22)[0]
    planes = struct.unpack_from('<H', raw, 26)[0]
    bpp = struct.unpack_from('<H', raw, 28)[0]
    compression = struct.unpack_from('<I', raw, 30)[0]
    if width <= 0 or height_signed == 0 or planes != 1 or compression != 0 or bpp not in (24, 32):
        raise ValueError("BMP supporté uniquement en 24/32 bits non compressé")
    height = abs(height_signed)
    _checked_image_size(width, height)
    row_stride = ((width * bpp + 31) // 32) * 4
    if pixel_offset + row_stride * height > len(raw):
        raise ValueError("BMP tronqué")
    pixels = [0] * (width * height)
    top_down = height_signed < 0
    bytespp = bpp // 8
    for sy in range(height):
        dy = sy if top_down else height - 1 - sy
        off = pixel_offset + sy * row_stride
        for x in range(width):
            b,g,r = raw[off + x*bytespp:off + x*bytespp + 3]
            pixels[dy*width + x] = (r<<16)|(g<<8)|b
    return MiniImage(width, height, pixels, source)


def _decode_png(raw: bytes, source: str) -> MiniImage:
    if raw[:8] != b'\x89PNG\r\n\x1a\n':
        raise ValueError("PNG invalide")
    pos = 8; idat = bytearray(); palette = None; trns = None
    width=height=bit_depth=color_type=None; interlace=0
    while pos + 8 <= len(raw):
        length = struct.unpack_from('>I', raw, pos)[0]; pos += 4
        if pos + 4 + length + 4 > len(raw): raise ValueError("PNG tronqué")
        ctype = raw[pos:pos+4]; pos += 4; data = raw[pos:pos+length]; pos += length
        crc = raw[pos:pos+4]; pos += 4
        if ctype == b'IHDR':
            if length != 13: raise ValueError("IHDR PNG invalide")
            width,height,bit_depth,color_type,compression,filter_method,interlace = struct.unpack('>IIBBBBB', data)
            if compression != 0 or filter_method != 0 or interlace != 0:
                raise ValueError("PNG compressé/interlacé non supporté")
            _checked_image_size(width,height)
            if bit_depth != 8 or color_type not in (0,2,3,4,6):
                raise ValueError("PNG: seuls les images 8 bits non interlacées sont supportées")
        elif ctype == b'PLTE':
            if len(data) % 3: raise ValueError("palette PNG invalide")
            palette = [tuple(data[i:i+3]) for i in range(0,len(data),3)]
        elif ctype == b'tRNS':
            trns = bytes(data)
        elif ctype == b'IDAT':
            idat += data
        elif ctype == b'IEND':
            break
    if width is None or height is None: raise ValueError("PNG sans IHDR")
    channels = {0:1,2:3,3:1,4:2,6:4}[color_type]
    stride = width * channels
    expected = height * (stride + 1)
    try: decoded = zlib.decompress(bytes(idat))
    except Exception as exc: raise ValueError(f"décompression PNG impossible: {exc}") from exc
    if len(decoded) != expected: raise ValueError("données PNG incomplètes")
    rows = []; prev = bytearray(stride); p = 0
    for _y in range(height):
        f = decoded[p]; p += 1
        cur = bytearray(decoded[p:p+stride]); p += stride
        if f == 1:
            for x in range(stride): cur[x] = (cur[x] + (cur[x-channels] if x >= channels else 0)) & 255
        elif f == 2:
            for x in range(stride): cur[x] = (cur[x] + prev[x]) & 255
        elif f == 3:
            for x in range(stride): cur[x] = (cur[x] + ((prev[x] + (cur[x-channels] if x >= channels else 0)) // 2)) & 255
        elif f == 4:
            for x in range(stride):
                a = cur[x-channels] if x >= channels else 0; b = prev[x]; c = prev[x-channels] if x >= channels else 0
                pa = abs(b-c); pb = abs(a-c); pc = abs(a+b-2*c)
                pr = a if pa <= pb and pa <= pc else (b if pb <= pc else c)
                cur[x] = (cur[x] + pr) & 255
        elif f != 0:
            raise ValueError(f"filtre PNG inconnu: {f}")
        rows.append(cur); prev = cur
    pixels=[]
    for row in rows:
        if color_type == 0:
            for v in row: pixels.append((v<<16)|(v<<8)|v)
        elif color_type == 2:
            for i in range(0,len(row),3):
                r,g,b=row[i:i+3]; pixels.append((r<<16)|(g<<8)|b)
        elif color_type == 3:
            if palette is None: raise ValueError("PNG palette manquante")
            for idx in row:
                if idx >= len(palette): raise ValueError("index palette PNG invalide")
                r,g,b=palette[idx]; pixels.append((r<<16)|(g<<8)|b)
        elif color_type == 4:
            for i in range(0,len(row),2):
                v=row[i]; pixels.append((v<<16)|(v<<8)|v)
        else: # 6 RGBA
            for i in range(0,len(row),4):
                r,g,b,a=row[i:i+4]
                # SoftwareRenderer ne gère pas alpha dans la v1 : composition sur fond noir.
                r=r*a//255; g=g*a//255; b=b*a//255
                pixels.append((r<<16)|(g<<8)|b)
    return MiniImage(width,height,pixels,source)


def decode_image_bytes(raw: bytes, source: str = "") -> MiniImage:
    raw = bytes(raw)
    if raw.startswith(b'\x89PNG\r\n\x1a\n'): return _decode_png(raw, source)
    if raw[:2] == b'BM': return _decode_bmp(raw, source)
    if raw[:2] in (b'P6', b'P3'): return _decode_ppm(raw, source)
    raise ValueError("format d'image non supporté (PNG, BMP 24/32 bits ou PPM attendu)")


class ImageManager:
    """Handles d'images appartenant à un processus VM32."""
    def __init__(self):
        self._lock = threading.RLock()
        self._next = 1
        self._images: Dict[int, MiniImage] = {}
    def load(self, path: str, raw: bytes) -> int:
        image = decode_image_bytes(raw, path)
        with self._lock:
            handle = self._next; self._next += 1; self._images[handle] = image
            return handle
    def get(self, handle: int) -> MiniImage:
        with self._lock:
            image = self._images.get(int(handle))
            if image is None: raise KeyError(f"handle image invalide: {handle}")
            return image
    def free(self, handle: int) -> bool:
        with self._lock:
            return self._images.pop(int(handle), None) is not None
    def clear(self) -> None:
        with self._lock: self._images.clear()
    def size(self) -> int:
        with self._lock: return len(self._images)


class SoftwareRenderer:
    """Moteur de rendu 2D logiciel indépendant de toute plateforme.

    Le renderer ne crée aucune fenêtre et ne connaît ni Windows, ni Linux,
    ni Linux, ni macOS. Il produit simplement un framebuffer RGB en mémoire.
    Les backends de plateforme ne servent qu'à présenter ce framebuffer.
    """

    # Police bitmap 5x7 compacte, volontairement intégrée à miniOS.
    FONT = {
        " ": (0, 0, 0, 0, 0, 0, 0),
        "A": (14, 17, 17, 31, 17, 17, 17), "B": (30, 17, 17, 30, 17, 17, 30),
        "C": (14, 17, 16, 16, 16, 17, 14), "D": (30, 17, 17, 17, 17, 17, 30),
        "E": (31, 16, 16, 30, 16, 16, 31), "F": (31, 16, 16, 30, 16, 16, 16),
        "G": (14, 17, 16, 23, 17, 17, 14), "H": (17, 17, 17, 31, 17, 17, 17),
        "I": (31, 4, 4, 4, 4, 4, 31), "J": (7, 2, 2, 2, 2, 18, 12),
        "K": (17, 18, 20, 24, 20, 18, 17), "L": (16, 16, 16, 16, 16, 16, 31),
        "M": (17, 27, 21, 21, 17, 17, 17), "N": (17, 25, 21, 19, 17, 17, 17),
        "O": (14, 17, 17, 17, 17, 17, 14), "P": (30, 17, 17, 30, 16, 16, 16),
        "Q": (14, 17, 17, 17, 21, 18, 13), "R": (30, 17, 17, 30, 20, 18, 17),
        "S": (15, 16, 16, 14, 1, 1, 30), "T": (31, 4, 4, 4, 4, 4, 4),
        "U": (17, 17, 17, 17, 17, 17, 14), "V": (17, 17, 17, 17, 17, 10, 4),
        "W": (17, 17, 17, 21, 21, 21, 10), "X": (17, 17, 10, 4, 10, 17, 17),
        "Y": (17, 17, 10, 4, 4, 4, 4), "Z": (31, 1, 2, 4, 8, 16, 31),
        "0": (14, 17, 19, 21, 25, 17, 14), "1": (4, 12, 4, 4, 4, 4, 14),
        "2": (14, 17, 1, 2, 4, 8, 31), "3": (30, 1, 1, 14, 1, 1, 30),
        "4": (2, 6, 10, 18, 31, 2, 2), "5": (31, 16, 16, 30, 1, 1, 30),
        "6": (14, 16, 16, 30, 17, 17, 14), "7": (31, 1, 2, 4, 8, 8, 8),
        "8": (14, 17, 17, 14, 17, 17, 14), "9": (14, 17, 17, 15, 1, 1, 14),
        ".": (0, 0, 0, 0, 0, 12, 12), ",": (0, 0, 0, 0, 0, 12, 8),
        ":": (0, 12, 12, 0, 12, 12, 0), ";": (0, 12, 12, 0, 12, 8, 16),
        "!": (4, 4, 4, 4, 4, 0, 4), "?": (14, 17, 1, 2, 4, 0, 4),
        "-": (0, 0, 0, 31, 0, 0, 0), "_": (0, 0, 0, 0, 0, 0, 31),
        "/": (1, 2, 4, 8, 16, 0, 0), "\\": (16, 8, 4, 2, 1, 0, 0),
        "+": (0, 4, 4, 31, 4, 4, 0), "=": (0, 0, 31, 0, 31, 0, 0),
        "(": (2, 4, 8, 8, 8, 4, 2), ")": (8, 4, 2, 2, 2, 4, 8),
        "[": (14, 8, 8, 8, 8, 8, 14), "]": (14, 2, 2, 2, 2, 2, 14),
        "'": (4, 4, 8, 0, 0, 0, 0), '"': (10, 10, 0, 0, 0, 0, 0),
        "*": (0, 4, 21, 14, 21, 4, 0), "#": (10, 31, 10, 10, 31, 10, 0),
        "<": (2, 4, 8, 16, 8, 4, 2), ">": (8, 4, 2, 1, 2, 4, 8),
        "|": (4, 4, 4, 4, 4, 4, 4), "%": (17, 2, 4, 8, 16, 17, 0),
    }

    def __init__(self, width: int, height: int, background: int = 0x000000):
        self.width = max(1, int(width))
        self.height = max(1, int(height))
        self.pixels: List[int] = [int(background) & 0xFFFFFF] * (self.width * self.height)
        self.frame_count = 0
        self.draw_calls = 0
        self.dirty = True

    @staticmethod
    def _rgb_tuple(color: int) -> Tuple[int, int, int]:
        color = int(color) & 0xFFFFFF
        return ((color >> 16) & 0xFF, (color >> 8) & 0xFF, color & 0xFF)

    def resize(self, width: int, height: int, background: int = 0x000000):
        width = max(1, int(width)); height = max(1, int(height))
        if width == self.width and height == self.height:
            return
        old_w, old_h, old = self.width, self.height, self.pixels
        self.width, self.height = width, height
        self.pixels = [int(background) & 0xFFFFFF] * (width * height)
        copy_w, copy_h = min(old_w, width), min(old_h, height)
        for y in range(copy_h):
            self.pixels[y * width:y * width + copy_w] = old[y * old_w:y * old_w + copy_w]
        self.dirty = True

    def _inside(self, x: int, y: int) -> bool:
        return 0 <= x < self.width and 0 <= y < self.height

    def pixel(self, x: int, y: int, color: int):
        x, y = int(x), int(y)
        if self._inside(x, y):
            self.pixels[y * self.width + x] = int(color) & 0xFFFFFF
            self.draw_calls += 1
            self.dirty = True

    def clear(self, color: int):
        color = int(color) & 0xFFFFFF
        self.pixels[:] = [color] * len(self.pixels)
        self.draw_calls += 1
        self.dirty = True

    def rect(self, x: int, y: int, w: int, h: int, color: int, fill: bool = True):
        x, y, w, h = int(x), int(y), int(w), int(h)
        if w == 0 or h == 0:
            return
        if w < 0: x, w = x + w, -w
        if h < 0: y, h = y + h, -h
        color = int(color) & 0xFFFFFF
        if fill:
            x0, y0 = max(0, x), max(0, y)
            x1, y1 = min(self.width, x + w), min(self.height, y + h)
            if x0 < x1 and y0 < y1:
                row = [color] * (x1 - x0)
                for yy in range(y0, y1):
                    start = yy * self.width + x0
                    self.pixels[start:start + (x1 - x0)] = row
        else:
            self.line(x, y, x + w - 1, y, color)
            self.line(x, y, x, y + h - 1, color)
            self.line(x + w - 1, y, x + w - 1, y + h - 1, color)
            self.line(x, y + h - 1, x + w - 1, y + h - 1, color)
        self.draw_calls += 1
        self.dirty = True

    def line(self, x1: int, y1: int, x2: int, y2: int, color: int, width: int = 1):
        x1, y1, x2, y2 = int(x1), int(y1), int(x2), int(y2)
        color = int(color) & 0xFFFFFF
        width = max(1, int(width))
        dx, sx = abs(x2 - x1), 1 if x1 < x2 else -1
        dy, sy = -abs(y2 - y1), 1 if y1 < y2 else -1
        err = dx + dy
        radius = width // 2
        while True:
            for ox in range(-radius, radius + 1):
                for oy in range(-radius, radius + 1):
                    self.pixel(x1 + ox, y1 + oy, color)
            if x1 == x2 and y1 == y2:
                break
            e2 = 2 * err
            if e2 >= dy:
                err += dy; x1 += sx
            if e2 <= dx:
                err += dx; y1 += sy
        self.draw_calls += 1

    def circle(self, cx: int, cy: int, r: int, color: int, fill: bool = True):
        cx, cy, r = int(cx), int(cy), abs(int(r))
        if r <= 0:
            self.pixel(cx, cy, color); return
        color = int(color) & 0xFFFFFF
        rr = r * r
        if fill:
            for yy in range(-r, r + 1):
                xx = int((max(0, rr - yy * yy)) ** 0.5)
                x0, x1 = cx - xx, cx + xx
                x0c, x1c = max(0, x0), min(self.width - 1, x1)
                if x0c <= x1c and 0 <= cy + yy < self.height:
                    start = (cy + yy) * self.width + x0c
                    self.pixels[start:start + x1c - x0c + 1] = [color] * (x1c - x0c + 1)
        else:
            x, y, d = r, 0, 1 - r
            while x >= y:
                for px, py in ((cx+x,cy+y),(cx+y,cy+x),(cx-y,cy+x),(cx-x,cy+y),
                              (cx-x,cy-y),(cx-y,cy-x),(cx+y,cy-x),(cx+x,cy-y)):
                    self.pixel(px, py, color)
                y += 1
                if d <= 0: d += 2*y + 1
                else: x -= 1; d += 2*(y-x) + 1
        self.draw_calls += 1; self.dirty = True

    def text(self, x: int, y: int, text: str, color: int, scale: int = 2):
        x0, y0 = int(x), int(y)
        scale = max(1, int(scale))
        cursor_x = x0
        color = int(color) & 0xFFFFFF
        for ch in str(text):
            if ch == "\n":
                cursor_x = x0; y0 += 8 * scale; continue
            glyph = self.FONT.get(ch, self.FONT.get(ch.upper(), self.FONT["?"]))
            for row, bits in enumerate(glyph):
                for col in range(5):
                    if bits & (1 << (4 - col)):
                        for sy in range(scale):
                            yy = y0 + row * scale + sy
                            if 0 <= yy < self.height:
                                start = max(0, cursor_x + col * scale)
                                end = min(self.width, cursor_x + (col + 1) * scale)
                                if start < end:
                                    self.pixels[yy * self.width + start:yy * self.width + end] = [color] * (end - start)
            cursor_x += 6 * scale
        self.draw_calls += 1; self.dirty = True


    def image_draw(self, image: MiniImage, x: int, y: int):
        x, y = int(x), int(y)
        for sy in range(image.height):
            dy = y + sy
            if dy < 0 or dy >= self.height: continue
            sx0 = max(0, -x); sx1 = min(image.width, self.width - x)
            if sx0 >= sx1: continue
            src = sy * image.width + sx0
            dst = dy * self.width + x + sx0
            self.pixels[dst:dst + (sx1 - sx0)] = image.pixels[src:src + (sx1 - sx0)]
        self.draw_calls += 1; self.dirty = True

    def image_draw_scaled(self, image: MiniImage, x: int, y: int, w: int, h: int):
        x, y, w, h = int(x), int(y), int(w), int(h)
        if w <= 0 or h <= 0: return
        for dy in range(max(0, y), min(self.height, y + h)):
            sy = min(image.height - 1, max(0, ((dy - y) * image.height) // h))
            for dx in range(max(0, x), min(self.width, x + w)):
                sx = min(image.width - 1, max(0, ((dx - x) * image.width) // w))
                self.pixels[dy * self.width + dx] = image.pixels[sy * image.width + sx]
        self.draw_calls += 1; self.dirty = True

    def to_ppm(self) -> bytes:
        body = bytearray(len(self.pixels) * 3)
        j = 0
        for color in self.pixels:
            body[j] = (color >> 16) & 0xFF
            body[j + 1] = (color >> 8) & 0xFF
            body[j + 2] = color & 0xFF
            j += 3
        header = f"P6\n{self.width} {self.height}\n255\n".encode("ascii")
        return header + bytes(body)

    def stats(self) -> Dict[str, Any]:
        return {
            "width": self.width,
            "height": self.height,
            "pixels": self.width * self.height,
            "frame_count": self.frame_count,
            "draw_calls": self.draw_calls,
            "dirty": self.dirty,
        }



class GraphicsBackend:
    """Interface graphique indépendante de toute bibliothèque graphique Python."""
    name = "none"

    def window(self, title: str, width: int, height: int, pid: int) -> int:
        raise RuntimeError("aucun backend graphique natif disponible")
    def clear(self, wid: int, color: int): pass
    def pixel(self, wid: int, x: int, y: int, color: int): pass
    def rect(self, wid: int, x: int, y: int, w: int, h: int, color: int, fill: bool = True): pass
    def line(self, wid: int, x1: int, y1: int, x2: int, y2: int, color: int, width: int = 1): pass
    def circle(self, wid: int, x: int, y: int, r: int, color: int, fill: bool = True): pass
    def text(self, wid: int, x: int, y: int, text: str, color: int, size: int = 16): pass
    def present(self, wid: int): pass
    def image_draw(self, wid: int, image: MiniImage, x: int, y: int): pass
    def image_draw_scaled(self, wid: int, image: MiniImage, x: int, y: int, w: int, h: int): pass
    def minimize(self, wid: int): pass
    def close(self, wid: int): pass
    def _install_close_callback(self, wid: int, callback): pass
    def key_down(self, wid: int, key: str) -> bool: return False
    def key_pressed(self, wid: int, key: str) -> bool: return False
    def text_input(self, wid: int, action: str = "get") -> str: return ""
    def mouse_x(self, wid: int) -> int: return 0
    def mouse_y(self, wid: int) -> int: return 0
    def mouse_down(self, wid: int, button: int) -> bool: return False
    def close_requested(self, wid: int) -> bool: return False
    def alive(self, wid: int) -> bool: return False
    def debug_info(self, wid: int) -> Dict[str, Any]: return {}
    def pump_events(self): pass
    def shutdown(self): pass


# ----------------------------------------------------------------
# Win32 backend natif
# ----------------------------------------------------------------
# Ce backend est volontairement basé uniquement sur ctypes + Win32 API :
# aucune dépendance Python externe et aucun toolkit graphique.
if sys.platform == "win32":
    from ctypes import wintypes

    _LRESULT = getattr(ctypes, "c_ssize_t", ctypes.c_longlong)
    _LPARAM = getattr(ctypes, "c_ssize_t", ctypes.c_longlong)   # LONG_PTR, signé, 64 bits sur Windows x64
    _WPARAM = getattr(ctypes, "c_size_t", ctypes.c_ulonglong)  # ULONG_PTR, non signé, 64 bits sur Windows x64
    _WNDPROC = getattr(ctypes, "WINFUNCTYPE", ctypes.CFUNCTYPE)(_LRESULT, wintypes.HWND, wintypes.UINT, _WPARAM, _LPARAM)

    class _POINT(ctypes.Structure):
        _fields_ = [("x", ctypes.c_long), ("y", ctypes.c_long)]

    class _RECT(ctypes.Structure):
        _fields_ = [("left", ctypes.c_long), ("top", ctypes.c_long), ("right", ctypes.c_long), ("bottom", ctypes.c_long)]

    class _PAINTSTRUCT(ctypes.Structure):
        _fields_ = [
            ("hdc", wintypes.HDC), ("fErase", wintypes.BOOL), ("rcPaint", _RECT),
            ("fRestore", wintypes.BOOL), ("fIncUpdate", wintypes.BOOL),
            ("rgbReserved", ctypes.c_byte * 32)
        ]

    class _WNDCLASSEXW(ctypes.Structure):
        _fields_ = [
            ("cbSize", wintypes.UINT), ("style", wintypes.UINT), ("lpfnWndProc", ctypes.c_void_p),
            ("cbClsExtra", ctypes.c_int), ("cbWndExtra", ctypes.c_int), ("hInstance", wintypes.HINSTANCE),
            ("hIcon", wintypes.HICON), ("hCursor", wintypes.HCURSOR), ("hbrBackground", wintypes.HBRUSH),
            ("lpszMenuName", wintypes.LPCWSTR), ("lpszClassName", wintypes.LPCWSTR), ("hIconSm", wintypes.HICON)
        ]

    class _BITMAPINFOHEADER(ctypes.Structure):
        _fields_ = [
            ("biSize", wintypes.DWORD), ("biWidth", wintypes.LONG), ("biHeight", wintypes.LONG),
            ("biPlanes", wintypes.WORD), ("biBitCount", wintypes.WORD), ("biCompression", wintypes.DWORD),
            ("biSizeImage", wintypes.DWORD), ("biXPelsPerMeter", wintypes.LONG), ("biYPelsPerMeter", wintypes.LONG),
            ("biClrUsed", wintypes.DWORD), ("biClrImportant", wintypes.DWORD)
        ]

    class _RGBQUAD(ctypes.Structure):
        _fields_ = [("rgbBlue", ctypes.c_ubyte), ("rgbGreen", ctypes.c_ubyte), ("rgbRed", ctypes.c_ubyte), ("rgbReserved", ctypes.c_ubyte)]

    class _BITMAPINFO(ctypes.Structure):
        _fields_ = [("bmiHeader", _BITMAPINFOHEADER), ("bmiColors", _RGBQUAD * 1)]


class Win32GraphicsBackend(GraphicsBackend):
    """Backend graphique natif Windows.

    Le rendu est produit par :
      MiniLang -> SoftwareRenderer -> framebuffer CPU -> DIB 32 bits -> Win32.

    Aucun tkinter, pygame, Pillow ou autre paquet n'est utilisé.
    """
    name = "software-renderer+win32"

    # Fenêtre sans barre de titre native : le moteur dessine sa propre barre de titre.
    WS_OVERLAPPEDWINDOW = 0x00CF0000
    # Windows : aucune barre de titre native.
    # La seule barre visible est celle dessinée par miniOS dans le framebuffer.
    # WS_POPUP supprime le chrome Windows (titre, boutons, bordure native).
    WS_CUSTOMWINDOW = 0x80000000  # WS_POPUP
    WS_EX_APPWINDOW = 0x00040000
    WS_VISIBLE = 0x10000000
    CS_HREDRAW = 0x0002
    CS_VREDRAW = 0x0001
    COLOR_WINDOW = 5
    SW_SHOW = 5
    SW_MINIMIZE = 6
    PM_REMOVE = 0x0001
    WM_NULL = 0x0000
    WM_PAINT = 0x000F
    WM_CLOSE = 0x0010
    WM_DESTROY = 0x0002
    WM_SIZE = 0x0005
    WM_ERASEBKGND = 0x0014
    WM_KEYDOWN = 0x0100
    WM_KEYUP = 0x0101
    WM_CHAR = 0x0102
    WM_SYSKEYDOWN = 0x0104
    WM_SYSKEYUP = 0x0105
    WM_MOUSEMOVE = 0x0200
    WM_MOUSELEAVE = 0x02A3
    WM_LBUTTONDOWN = 0x0201
    WM_LBUTTONUP = 0x0202
    WM_RBUTTONDOWN = 0x0204
    WM_RBUTTONUP = 0x0205
    WM_MBUTTONDOWN = 0x0207
    WM_MBUTTONUP = 0x0208
    VK_ESCAPE = 0x1B
    VK_RETURN = 0x0D
    VK_SPACE = 0x20
    VK_LEFT = 0x25
    VK_UP = 0x26
    VK_RIGHT = 0x27
    VK_DOWN = 0x28
    VK_SHIFT = 0x10
    VK_CONTROL = 0x11
    VK_ALT = 0x12
    VK_TAB = 0x09
    VK_BACK = 0x08
    VK_DELETE = 0x2E
    DIB_RGB_COLORS = 0
    SRCCOPY = 0x00CC0020
    TITLEBAR_H = 32
    BUTTON_W = 44

    _class_name = "miniOSNativeGraphics_v1"

    def __init__(self):
        if sys.platform != "win32":
            raise RuntimeError("backend Win32 demandé hors de Windows")
        try:
            self.user32 = ctypes.WinDLL("user32", use_last_error=True)
            self.gdi32 = ctypes.WinDLL("gdi32", use_last_error=True)
            self.kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
        except Exception as exc:
            raise RuntimeError(f"API Win32 indisponible: {exc}") from exc

        # GetModuleHandleW appartient à kernel32.dll, pas à user32.dll.
        # Python 3.14 expose correctement les DLL Win32, mais appeler la
        # mauvaise DLL provoque : 'function GetModuleHandleW not found'.
        self.kernel32.GetModuleHandleW.argtypes = [wintypes.LPCWSTR]
        self.kernel32.GetModuleHandleW.restype = wintypes.HINSTANCE
        self.user32.RegisterClassExW.argtypes = [ctypes.POINTER(_WNDCLASSEXW)]
        self.user32.RegisterClassExW.restype = wintypes.ATOM
        self.user32.UnregisterClassW.argtypes = [wintypes.LPCWSTR, wintypes.HINSTANCE]
        self.user32.UnregisterClassW.restype = wintypes.BOOL
        self.user32.CreateWindowExW.argtypes = [wintypes.DWORD, wintypes.LPCWSTR, wintypes.LPCWSTR, wintypes.DWORD, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, wintypes.HWND, wintypes.HMENU, wintypes.HINSTANCE, wintypes.LPVOID]
        self.user32.CreateWindowExW.restype = wintypes.HWND
        self.user32.ShowWindow.argtypes = [wintypes.HWND, ctypes.c_int]
        self.user32.UpdateWindow.argtypes = [wintypes.HWND]
        self.user32.ReleaseCapture.argtypes = []
        self.user32.ReleaseCapture.restype = wintypes.BOOL
        self.user32.SendMessageW.argtypes = [wintypes.HWND, wintypes.UINT, _WPARAM, _LPARAM]
        self.user32.SendMessageW.restype = _LRESULT
        # DefWindowProcW utilise HWND, UINT, WPARAM (ULONG_PTR), LPARAM (LONG_PTR).
        # Sans prototype explicite, ctypes convertit LPARAM en entier C long 32 bits
        # sur certains Python/Windows x64, ce qui provoque :
        #   OverflowError: int too long to convert
        self.user32.DefWindowProcW.argtypes = [wintypes.HWND, wintypes.UINT, _WPARAM, _LPARAM]
        self.user32.DefWindowProcW.restype = _LRESULT
        self.user32.SetForegroundWindow.argtypes = [wintypes.HWND]
        self.user32.SetFocus.argtypes = [wintypes.HWND]
        self.user32.GetAsyncKeyState.argtypes = [ctypes.c_int]
        self.user32.GetAsyncKeyState.restype = ctypes.c_short
        self.user32.DestroyWindow.argtypes = [wintypes.HWND]
        self.user32.DestroyWindow.restype = wintypes.BOOL
        self.user32.PeekMessageW.argtypes = [ctypes.POINTER(wintypes.MSG), wintypes.HWND, wintypes.UINT, wintypes.UINT, wintypes.UINT]
        self.user32.PeekMessageW.restype = wintypes.BOOL
        self.user32.TranslateMessage.argtypes = [ctypes.POINTER(wintypes.MSG)]
        self.user32.DispatchMessageW.argtypes = [ctypes.POINTER(wintypes.MSG)]
        self.user32.InvalidateRect.argtypes = [wintypes.HWND, ctypes.POINTER(_RECT), wintypes.BOOL]
        self.user32.InvalidateRect.restype = wintypes.BOOL
        self.user32.BeginPaint.argtypes = [wintypes.HWND, ctypes.POINTER(_PAINTSTRUCT)]
        self.user32.BeginPaint.restype = wintypes.HDC
        self.user32.EndPaint.argtypes = [wintypes.HWND, ctypes.POINTER(_PAINTSTRUCT)]
        self.user32.GetClientRect.argtypes = [wintypes.HWND, ctypes.POINTER(_RECT)]
        self.user32.GetClientRect.restype = wintypes.BOOL
        self.user32.AdjustWindowRectEx.argtypes = [ctypes.POINTER(_RECT), wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
        self.user32.AdjustWindowRectEx.restype = wintypes.BOOL

        self.gdi32.StretchDIBits.argtypes = [wintypes.HDC, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_void_p, ctypes.POINTER(_BITMAPINFO), wintypes.UINT, wintypes.DWORD]
        self.gdi32.StretchDIBits.restype = ctypes.c_int

        self.hinstance = self.kernel32.GetModuleHandleW(None)
        self.windows: Dict[int, Dict[str, Any]] = {}
        self._hwnd_to_wid: Dict[int, int] = {}
        self.next_id = 1
        self._registered = False
        self._wndproc = _WNDPROC(self._wnd_proc)
        self._register_class()

    def _register_class(self):
        cls = _WNDCLASSEXW()
        cls.cbSize = ctypes.sizeof(_WNDCLASSEXW)
        cls.style = self.CS_HREDRAW | self.CS_VREDRAW
        cls.lpfnWndProc = ctypes.cast(self._wndproc, ctypes.c_void_p)
        cls.hInstance = self.hinstance
        cls.hCursor = self.user32.LoadCursorW(None, ctypes.c_void_p(32512))  # IDC_ARROW
        cls.hbrBackground = ctypes.c_void_p(self.COLOR_WINDOW + 1)
        cls.lpszClassName = self._class_name
        atom = self.user32.RegisterClassExW(ctypes.byref(cls))
        if not atom:
            error = ctypes.get_last_error()
            if error != 1410:  # ERROR_CLASS_ALREADY_EXISTS
                raise RuntimeError(f"RegisterClassExW échoué (code={error})")
        self._registered = True

    @staticmethod
    def _signed_word(value: int) -> int:
        value &= 0xFFFF
        return value - 0x10000 if value & 0x8000 else value

    @classmethod
    def _xy_from_lparam(cls, value: int) -> Tuple[int, int]:
        return cls._signed_word(value), cls._signed_word(value >> 16)

    def _get(self, wid: int) -> Dict[str, Any]:
        item = self.windows.get(int(wid))
        if item is None:
            raise RuntimeError(f"fenêtre graphique inconnue: {wid}")
        if not item.get("alive", False):
            raise RuntimeError("fenêtre graphique fermée")
        return item

    def _key_name(self, vk: int) -> str:
        vk = int(vk)
        special = {
            self.VK_ESCAPE: "ESC", self.VK_RETURN: "ENTER", self.VK_SPACE: "SPACE",
            self.VK_LEFT: "LEFT", self.VK_RIGHT: "RIGHT", self.VK_UP: "UP", self.VK_DOWN: "DOWN",
            self.VK_SHIFT: "SHIFT", self.VK_CONTROL: "CTRL", self.VK_ALT: "ALT",
            self.VK_TAB: "TAB", self.VK_BACK: "BACKSPACE", self.VK_DELETE: "DELETE",
        }
        if vk in special:
            return special[vk]
        if 0x30 <= vk <= 0x39 or 0x41 <= vk <= 0x5A:
            return chr(vk)
        if 0x70 <= vk <= 0x7B:
            return f"F{vk - 0x6F}"
        return f"VK_{vk:02X}"

    @staticmethod
    def _renderer_bgra(renderer: SoftwareRenderer) -> bytes:
        out = bytearray(renderer.width * renderer.height * 4)
        j = 0
        for color in renderer.pixels:
            out[j] = color & 0xFF
            out[j + 1] = (color >> 8) & 0xFF
            out[j + 2] = (color >> 16) & 0xFF
            out[j + 3] = 0
            j += 4
        return bytes(out)

    def _chrome(self, width: int, title: str, hover_control: Optional[str]) -> SoftwareRenderer:
        chrome = SoftwareRenderer(max(1, int(width)), self.TITLEBAR_H, 0x181A20)
        chrome.rect(0, 0, chrome.width, self.TITLEBAR_H, 0x181A20)
        # Fine ligne inférieure.
        chrome.rect(0, self.TITLEBAR_H - 1, chrome.width, 1, 0x30343D)
        close_x = max(0, chrome.width - self.BUTTON_W)
        min_x = max(0, chrome.width - 2 * self.BUTTON_W)
        if hover_control == "close":
            chrome.rect(close_x, 0, self.BUTTON_W, self.TITLEBAR_H, 0xB3261E)
        else:
            chrome.rect(close_x, 0, self.BUTTON_W, self.TITLEBAR_H, 0x242831)
        if hover_control == "minimize":
            chrome.rect(min_x, 0, self.BUTTON_W, self.TITLEBAR_H, 0x343943)
        else:
            chrome.rect(min_x, 0, self.BUTTON_W, self.TITLEBAR_H, 0x242831)
        # Bouton minimiser : trait horizontal.
        chrome.line(min_x + 14, 21, min_x + 30, 21, 0xF2F2F2, 2)
        # Bouton fermer : X.
        cx = close_x + self.BUTTON_W // 2
        chrome.line(cx - 7, 10, cx + 7, 24, 0xFFFFFF, 2)
        chrome.line(cx + 7, 10, cx - 7, 24, 0xFFFFFF, 2)
        # Titre bitmap intégré du SoftwareRenderer.
        chrome.text(10, 10, str(title)[:48], 0xE6EAF0, 2)
        return chrome

    def _compose_bgra(self, item: Dict[str, Any]) -> bytes:
        renderer = item["renderer"]
        chrome = self._chrome(renderer.width, item.get("title", "miniOS"), item.get("hover_control"))
        top = self._renderer_bgra(chrome)
        body = self._renderer_bgra(renderer)
        item["frame_width"] = renderer.width
        item["frame_height"] = renderer.height + self.TITLEBAR_H
        return top + body

    def _paint(self, item: Dict[str, Any], hdc: Any):
        buf = item.get("last_bgra")
        renderer = item.get("renderer")
        if not buf or renderer is None:
            return
        rc = _RECT()
        self.user32.GetClientRect(item["hwnd"], ctypes.byref(rc))
        cw = max(1, int(rc.right - rc.left)); ch = max(1, int(rc.bottom - rc.top))
        frame_w = max(1, int(item.get("frame_width", renderer.width)))
        frame_h = max(1, int(item.get("frame_height", renderer.height + self.TITLEBAR_H)))
        bmi = _BITMAPINFO()
        bmi.bmiHeader.biSize = ctypes.sizeof(_BITMAPINFOHEADER)
        bmi.bmiHeader.biWidth = frame_w
        bmi.bmiHeader.biHeight = -frame_h  # DIB top-down
        bmi.bmiHeader.biPlanes = 1
        bmi.bmiHeader.biBitCount = 32
        bmi.bmiHeader.biCompression = 0  # BI_RGB
        bmi.bmiHeader.biSizeImage = len(buf)
        raw = ctypes.create_string_buffer(buf)
        self.gdi32.StretchDIBits(
            hdc, 0, 0, cw, ch, 0, 0, frame_w, frame_h,
            ctypes.cast(raw, ctypes.c_void_p), ctypes.byref(bmi), self.DIB_RGB_COLORS, self.SRCCOPY
        )

    def _wnd_proc(self, hwnd, msg, wparam, lparam):
        wid = self._hwnd_to_wid.get(int(hwnd))
        item = self.windows.get(wid) if wid is not None else None
        try:
            if msg == self.WM_ERASEBKGND:
                return 1
            if item is not None:
                if msg == self.WM_PAINT:
                    ps = _PAINTSTRUCT()
                    hdc = self.user32.BeginPaint(hwnd, ctypes.byref(ps))
                    try:
                        self._paint(item, hdc)
                    finally:
                        self.user32.EndPaint(hwnd, ctypes.byref(ps))
                    return 0
                if msg == self.WM_CLOSE:
                    if item.get("alive", False):
                        item["close_requested"] = True
                        item["alive"] = False
                        cb = item.get("on_close")
                        if cb:
                            try: cb()
                            except Exception: pass
                        try: self.user32.DestroyWindow(hwnd)
                        except Exception: pass
                    return 0
                if msg == self.WM_SIZE and item.get("alive", False):
                    w = max(1, lparam & 0xFFFF); h = max(1, (lparam >> 16) & 0xFFFF)
                    content_h = max(1, h - self.TITLEBAR_H)
                    try:
                        item["renderer"].resize(w, content_h)
                        item["frame_width"] = w
                        item["frame_height"] = content_h + self.TITLEBAR_H
                        item["last_bgra"] = self._compose_bgra(item)
                    except Exception:
                        pass
                    return 0
                if msg in (self.WM_KEYDOWN, self.WM_SYSKEYDOWN) and item.get("alive", False):
                    key_name = self._key_name(wparam)
                    if key_name not in item["keys"]:
                        item["pressed_keys"].add(key_name)
                    item["keys"].add(key_name)
                    return 0
                if msg == self.WM_CHAR and item.get("alive", False):
                    # WM_CHAR contient le caractère réellement produit par la
                    # disposition/clavier Windows (y compris les accents).
                    code = int(wparam)
                    high = item.get("pending_high_surrogate")
                    if 0xD800 <= code <= 0xDBFF:
                        item["pending_high_surrogate"] = code
                        return 0
                    if 0xDC00 <= code <= 0xDFFF and high is not None:
                        codepoint = 0x10000 + ((high - 0xD800) << 10) + (code - 0xDC00)
                        item["pending_high_surrogate"] = None
                        ch = chr(codepoint)
                    else:
                        item["pending_high_surrogate"] = None
                        ch = chr(code) if 0 <= code <= 0x10FFFF else ""
                    if item.get("text_input_enabled", False) and ch:
                        if ch == "\b":
                            if item["text_buffer"]:
                                item["text_buffer"].pop()
                        elif ch == "\r":
                            item["text_buffer"].append("\n")
                        elif ch == "\t":
                            item["text_buffer"].append("\t")
                        elif ch >= " " and ch != "\x7f":
                            item["text_buffer"].append(ch)
                    return 0
                if msg in (self.WM_KEYUP, self.WM_SYSKEYUP):
                    item["keys"].discard(self._key_name(wparam))
                    return 0
                if msg == self.WM_MOUSEMOVE and item.get("alive", False):
                    raw_x, raw_y = self._xy_from_lparam(lparam)
                    hover = None
                    if 0 <= raw_y < self.TITLEBAR_H:
                        width = item["renderer"].width
                        if width - self.BUTTON_W <= raw_x < width:
                            hover = "close"
                        elif width - 2 * self.BUTTON_W <= raw_x < width - self.BUTTON_W:
                            hover = "minimize"
                    if hover != item.get("hover_control"):
                        item["hover_control"] = hover
                        try:
                            item["last_bgra"] = self._compose_bgra(item)
                            self.user32.InvalidateRect(hwnd, None, False)
                        except Exception:
                            pass
                    item["mouse_x"], item["mouse_y"] = raw_x, raw_y - self.TITLEBAR_H
                    return 0
                if msg == self.WM_MOUSELEAVE and item.get("alive", False):
                    if item.get("hover_control") is not None:
                        item["hover_control"] = None
                        item["last_bgra"] = self._compose_bgra(item)
                        self.user32.InvalidateRect(hwnd, None, False)
                    return 0
                mouse_events = {
                    self.WM_LBUTTONDOWN: (1, True), self.WM_LBUTTONUP: (1, False),
                    self.WM_RBUTTONDOWN: (3, True), self.WM_RBUTTONUP: (3, False),
                    self.WM_MBUTTONDOWN: (2, True), self.WM_MBUTTONUP: (2, False),
                }
                if msg in mouse_events and item.get("alive", False):
                    button, down = mouse_events[msg]
                    raw_x, raw_y = self._xy_from_lparam(lparam)
                    if down and raw_y < self.TITLEBAR_H:
                        width = item["renderer"].width
                        if width - self.BUTTON_W <= raw_x < width:
                            item["close_requested"] = True
                            item["alive"] = False
                            cb = item.get("on_close")
                            if cb:
                                try: cb()
                                except Exception: pass
                            try: self.user32.DestroyWindow(hwnd)
                            except Exception: pass
                            return 0
                        if width - 2 * self.BUTTON_W <= raw_x < width - self.BUTTON_W:
                            try: self.user32.ShowWindow(hwnd, self.SW_MINIMIZE)
                            except Exception: pass
                            return 0
                        # Zone titre : déplacer la fenêtre comme une barre de titre.
                        try:
                            self.user32.ReleaseCapture()
                            self.user32.SendMessageW(hwnd, 0x00A1, 2, 0)  # WM_NCLBUTTONDOWN / HTCAPTION
                        except Exception:
                            pass
                        return 0
                    item["mouse_x"], item["mouse_y"] = raw_x, raw_y - self.TITLEBAR_H
                    if down: item["buttons"].add(button)
                    else: item["buttons"].discard(button)
                    return 0
        except Exception:
            # Une erreur dans la boucle native ne doit jamais remonter dans le
            # callback Win32 et provoquer un crash du processus Python.
            return 0
        if msg == self.WM_DESTROY:
            return 0
        return self.user32.DefWindowProcW(hwnd, msg, wparam, lparam)

    def window(self, title: str, width: int, height: int, pid: int) -> int:
        width = max(160, min(int(width), 4096)); height = max(80, min(int(height), 4096))
        style = self.WS_CUSTOMWINDOW
        # Avec WS_POPUP, width/height sont directement la taille de la surface
        # cliente : aucune marge ni barre native Windows n'est ajoutée.
        frame_width = width
        frame_height = height + self.TITLEBAR_H
        win = self.user32.CreateWindowExW(
            self.WS_EX_APPWINDOW, self._class_name, str(title), style,
            100, 100, frame_width, frame_height,
            None, None, self.hinstance, None
        )
        if not win:
            error = ctypes.get_last_error()
            raise RuntimeError(f"CreateWindowExW échoué (code={error})")
        wid = self.next_id; self.next_id += 1
        renderer = SoftwareRenderer(width, height)
        item = {
            "hwnd": win, "renderer": renderer, "pid": int(pid), "title": str(title),
            "keys": set(), "pressed_keys": set(), "buttons": set(), "mouse_x": 0, "mouse_y": 0,
            "text_input_enabled": False, "text_buffer": [], "pending_high_surrogate": None,
            "close_requested": False, "alive": True, "on_close": None,
            "hover_control": None, "last_bgra": b"",
            "frame_width": width, "frame_height": height + self.TITLEBAR_H,
            # Chrome natif Windows désactivé : la barre miniOS est l'unique barre.
        }
        item["last_bgra"] = self._compose_bgra(item)
        self.windows[wid] = item
        self._hwnd_to_wid[int(win)] = wid
        self.user32.ShowWindow(win, self.SW_SHOW)
        self.user32.UpdateWindow(win)
        self.user32.SetForegroundWindow(win)
        self.user32.SetFocus(win)
        return wid

    def _renderer(self, wid: int) -> SoftwareRenderer:
        return self._get(wid)["renderer"]
    def clear(self, wid: int, color: int): self._renderer(wid).clear(color)
    def pixel(self, wid: int, x: int, y: int, color: int): self._renderer(wid).pixel(x, y, color)
    def rect(self, wid: int, x: int, y: int, w: int, h: int, color: int, fill: bool = True): self._renderer(wid).rect(x, y, w, h, color, fill)
    def line(self, wid: int, x1: int, y1: int, x2: int, y2: int, color: int, width: int = 1): self._renderer(wid).line(x1, y1, x2, y2, color, width)
    def circle(self, wid: int, x: int, y: int, r: int, color: int, fill: bool = True): self._renderer(wid).circle(x, y, r, color, fill)
    def text(self, wid: int, x: int, y: int, text: str, color: int, size: int = 16):
        scale = max(1, int(round(max(1, int(size)) / 7.0)))
        self._renderer(wid).text(x, y, text, color, scale)
    def image_draw(self, wid: int, image: MiniImage, x: int, y: int):
        self._renderer(wid).image_draw(image, x, y)
    def image_draw_scaled(self, wid: int, image: MiniImage, x: int, y: int, w: int, h: int):
        self._renderer(wid).image_draw_scaled(image, x, y, w, h)
    def present(self, wid: int):
        item = self._get(wid); renderer = item["renderer"]
        item["last_bgra"] = self._compose_bgra(item)
        renderer.frame_count += 1; renderer.dirty = False
        self.user32.InvalidateRect(item["hwnd"], None, False)

    def debug_info(self, wid: int) -> Dict[str, Any]:
        item = self._get(wid); renderer = item["renderer"]
        rc = _RECT(); self.user32.GetClientRect(item["hwnd"], ctypes.byref(rc))
        return {"title": str(item.get("title", "(Win32)")), "width": int(item["renderer"].width), "height": int(item["renderer"].height),
                "alive": bool(item.get("alive")), "close_requested": bool(item.get("close_requested")),
                "custom_controls": True, "hover_control": item.get("hover_control"),
                "mouse_x": int(item.get("mouse_x",0)), "mouse_y": int(item.get("mouse_y",0)),
                "keys": sorted(str(k) for k in item.get("keys",set())),
                "pressed_keys": sorted(str(k) for k in item.get("pressed_keys",set())),
                "buttons": sorted(int(b) for b in item.get("buttons",set())), "renderer": renderer.stats()}

    def minimize(self, wid: int):
        item = self._get(wid)
        if not item.get("alive"):
            return
        self.user32.ShowWindow(item["hwnd"], self.SW_MINIMIZE)

    def close(self, wid: int):
        item = self.windows.pop(int(wid), None)
        if item:
            item["alive"] = False
            hwnd = item.get("hwnd")
            self._hwnd_to_wid.pop(int(hwnd), None)
            try: self.user32.DestroyWindow(hwnd)
            except Exception: pass

    def _install_close_callback(self, wid: int, callback): self._get(wid)["on_close"] = callback
    def _vk_from_key(self, key: str) -> Optional[int]:
        q = str(key).upper().strip()
        aliases = {
            "ESC": self.VK_ESCAPE, "ESCAPE": self.VK_ESCAPE,
            "ENTER": self.VK_RETURN, "RETURN": self.VK_RETURN,
            "SPACE": self.VK_SPACE, "SPACEBAR": self.VK_SPACE,
            "LEFT": self.VK_LEFT, "ARROWLEFT": self.VK_LEFT,
            "RIGHT": self.VK_RIGHT, "ARROWRIGHT": self.VK_RIGHT,
            "UP": self.VK_UP, "ARROWUP": self.VK_UP,
            "DOWN": self.VK_DOWN, "ARROWDOWN": self.VK_DOWN,
            "SHIFT": self.VK_SHIFT, "CTRL": self.VK_CONTROL,
            "CONTROL": self.VK_CONTROL, "ALT": self.VK_ALT,
            "TAB": self.VK_TAB, "BACKSPACE": self.VK_BACK,
            "BACK": self.VK_BACK, "DELETE": self.VK_DELETE,
            "DEL": self.VK_DELETE,
        }
        if q in aliases:
            return aliases[q]
        if len(q) == 1 and (q.isalpha() or q.isdigit()):
            return ord(q)
        if len(q) >= 2 and q.startswith("F") and q[1:].isdigit():
            n = int(q[1:])
            if 1 <= n <= 24:
                return 0x70 + (n - 1)
        return None

    def key_down(self, wid: int, key: str) -> bool:
        item = self._get(wid)
        q = str(key).upper().strip()

        # Détection par état matériel. Cela évite de rater une touche lorsque
        # WM_KEYDOWN/WM_KEYUP est généré entre deux tours de la boucle VM32.
        # C'est également indépendant du fait que le focus ait temporairement
        # changé pendant le traitement des messages Win32.
        vk = self._vk_from_key(q)
        if vk is not None:
            try:
                if int(self.user32.GetAsyncKeyState(int(vk))) & 0x8000:
                    return True
            except Exception:
                pass

        # File d'événements Win32 conservée comme second chemin (utile notamment
        # pour les touches spéciales lorsque le backend a déjà reçu l'événement).
        return q in {str(k).upper() for k in item.get("keys", set())}
    def key_pressed(self, wid: int, key: str) -> bool:
        item = self._get(wid)
        q = str(key).upper().strip()
        if q in {str(k).upper() for k in item.get("pressed_keys", set())}:
            item["pressed_keys"].discard(q)
            return True
        return False
    def text_input(self, wid: int, action: str = "get") -> str:
        item = self._get(wid)
        mode = str(action or "get").strip().lower()
        if mode in ("start", "on", "begin"):
            item["text_input_enabled"] = True
            item["text_buffer"] = []
            item["pending_high_surrogate"] = None
            try:
                self.user32.SetFocus(item["hwnd"])
            except Exception:
                pass
            return ""
        if mode in ("stop", "off", "end"):
            item["text_input_enabled"] = False
            item["pending_high_surrogate"] = None
            return "".join(item.get("text_buffer", []))
        if mode in ("clear", "reset"):
            item["text_buffer"] = []
            return ""
        return "".join(item.get("text_buffer", []))
    def mouse_x(self, wid: int) -> int: return int(self._get(wid)["mouse_x"])
    def mouse_y(self, wid: int) -> int: return int(self._get(wid)["mouse_y"])
    def mouse_down(self, wid: int, button: int) -> bool: return int(button) in self._get(wid)["buttons"]
    def close_requested(self, wid: int) -> bool: return bool(self._get(wid)["close_requested"])
    def alive(self, wid: int) -> bool:
        item = self.windows.get(int(wid)); return bool(item and item.get("alive"))

    def pump_events(self):
        msg = wintypes.MSG()
        while self.user32.PeekMessageW(ctypes.byref(msg), None, 0, 0, self.PM_REMOVE):
            self.user32.TranslateMessage(ctypes.byref(msg))
            self.user32.DispatchMessageW(ctypes.byref(msg))

    def shutdown(self):
        for wid in list(self.windows):
            try: self.close(wid)
            except Exception: pass



# ----------------------------------------------------------------
# Linux X11 backend natif (ctypes)
# ----------------------------------------------------------------
if sys.platform.startswith("linux"):
    class _XImage(ctypes.Structure):
        pass
    class _XImageFns(ctypes.Structure):
        pass
    # Layout public XImage (libX11/Xlib.h). Les pointeurs sont 64 bits sur
    # les plateformes modernes; la structure est utilisée uniquement pour
    # récupérer les propriétés créées par XCreateImage.
    _XImage._fields_ = [
        ("width", ctypes.c_int), ("height", ctypes.c_int),
        ("xoffset", ctypes.c_int), ("format", ctypes.c_int),
        ("data", ctypes.c_void_p), ("byte_order", ctypes.c_int),
        ("bitmap_unit", ctypes.c_int), ("bitmap_bit_order", ctypes.c_int),
        ("bitmap_pad", ctypes.c_int), ("depth", ctypes.c_int),
        ("bytes_per_line", ctypes.c_int), ("bits_per_pixel", ctypes.c_int),
        ("red_mask", ctypes.c_ulong), ("green_mask", ctypes.c_ulong),
        ("blue_mask", ctypes.c_ulong), ("obdata", ctypes.c_void_p),
    ]

    class _X11KeyEvent(ctypes.Structure):
        _fields_ = [("type", ctypes.c_int), ("serial", ctypes.c_ulong), ("send_event", ctypes.c_int),
                    ("display", ctypes.c_void_p), ("window", ctypes.c_ulong), ("root", ctypes.c_ulong),
                    ("subwindow", ctypes.c_ulong), ("time", ctypes.c_ulong), ("x", ctypes.c_int),
                    ("y", ctypes.c_int), ("x_root", ctypes.c_int), ("y_root", ctypes.c_int),
                    ("state", ctypes.c_uint), ("keycode", ctypes.c_uint), ("same_screen", ctypes.c_int)]
    class _X11ButtonEvent(ctypes.Structure):
        _fields_ = [("type", ctypes.c_int), ("serial", ctypes.c_ulong), ("send_event", ctypes.c_int),
                    ("display", ctypes.c_void_p), ("window", ctypes.c_ulong), ("root", ctypes.c_ulong),
                    ("subwindow", ctypes.c_ulong), ("time", ctypes.c_ulong), ("x", ctypes.c_int),
                    ("y", ctypes.c_int), ("x_root", ctypes.c_int), ("y_root", ctypes.c_int),
                    ("state", ctypes.c_uint), ("button", ctypes.c_uint), ("same_screen", ctypes.c_int)]
    class _X11MotionEvent(ctypes.Structure):
        _fields_ = [("type", ctypes.c_int), ("serial", ctypes.c_ulong), ("send_event", ctypes.c_int),
                    ("display", ctypes.c_void_p), ("window", ctypes.c_ulong), ("root", ctypes.c_ulong),
                    ("subwindow", ctypes.c_ulong), ("time", ctypes.c_ulong), ("x", ctypes.c_int),
                    ("y", ctypes.c_int), ("x_root", ctypes.c_int), ("y_root", ctypes.c_int),
                    ("state", ctypes.c_uint), ("is_hint", ctypes.c_char), ("same_screen", ctypes.c_int)]
    class _X11ConfigureEvent(ctypes.Structure):
        _fields_ = [("type", ctypes.c_int), ("serial", ctypes.c_ulong), ("send_event", ctypes.c_int),
                    ("display", ctypes.c_void_p), ("event", ctypes.c_ulong), ("window", ctypes.c_ulong),
                    ("x", ctypes.c_int), ("y", ctypes.c_int), ("width", ctypes.c_int),
                    ("height", ctypes.c_int), ("border_width", ctypes.c_int), ("above", ctypes.c_ulong),
                    ("override_redirect", ctypes.c_int)]
    class _X11ClientMessageData(ctypes.Union):
        _fields_ = [("l", ctypes.c_long * 5), ("b", ctypes.c_char * 20), ("s", ctypes.c_short * 10)]
    class _X11ClientMessageEvent(ctypes.Structure):
        _fields_ = [("type", ctypes.c_int), ("serial", ctypes.c_ulong), ("send_event", ctypes.c_int),
                    ("display", ctypes.c_void_p), ("window", ctypes.c_ulong), ("message_type", ctypes.c_ulong),
                    ("format", ctypes.c_int), ("data", _X11ClientMessageData)]
    class _X11ExposeEvent(ctypes.Structure):
        _fields_ = [("type", ctypes.c_int), ("serial", ctypes.c_ulong), ("send_event", ctypes.c_int),
                    ("display", ctypes.c_void_p), ("window", ctypes.c_ulong), ("x", ctypes.c_int),
                    ("y", ctypes.c_int), ("width", ctypes.c_int), ("height", ctypes.c_int), ("count", ctypes.c_int)]
    class _X11Event(ctypes.Union):
        _fields_ = [("type", ctypes.c_int), ("xkey", _X11KeyEvent), ("xbutton", _X11ButtonEvent),
                    ("xmotion", _X11MotionEvent), ("xconfigure", _X11ConfigureEvent),
                    ("xclient", _X11ClientMessageEvent), ("xexpose", _X11ExposeEvent), ("pad", ctypes.c_long * 24)]

    class X11GraphicsBackend(GraphicsBackend):
        """Backend X11 natif, sans toolkit Python externe."""
        name = "software-renderer+x11"
        LSBFirst = 0; ZPixmap = 2
        KeyPress = 2; KeyRelease = 3; ButtonPress = 4; ButtonRelease = 5; MotionNotify = 6
        Expose = 12; ConfigureNotify = 22; ClientMessage = 33
        KeyPressMask = 1 << 0; KeyReleaseMask = 1 << 1; ButtonPressMask = 1 << 2; ButtonReleaseMask = 1 << 3
        PointerMotionMask = 1 << 6; ExposureMask = 1 << 15; StructureNotifyMask = 1 << 17
        EventMask = KeyPressMask | KeyReleaseMask | ButtonPressMask | ButtonReleaseMask | PointerMotionMask | ExposureMask | StructureNotifyMask
        XK_ESCAPE = 0xFF1B
        Button1 = 1; Button2 = 2; Button3 = 3

        def __init__(self):
            lib = ctypes.util.find_library("X11") or "libX11.so.6"
            try: self.x11 = ctypes.CDLL(lib)
            except OSError as exc: raise RuntimeError(f"libX11 indisponible: {exc}") from exc
            x = self.x11
            x.XOpenDisplay.argtypes = [ctypes.c_char_p]; x.XOpenDisplay.restype = ctypes.c_void_p
            x.XDefaultScreen.argtypes = [ctypes.c_void_p]; x.XDefaultScreen.restype = ctypes.c_int
            x.XRootWindow.argtypes = [ctypes.c_void_p, ctypes.c_int]; x.XRootWindow.restype = ctypes.c_ulong
            x.XDefaultVisual.argtypes = [ctypes.c_void_p, ctypes.c_int]; x.XDefaultVisual.restype = ctypes.c_void_p
            x.XDefaultDepth.argtypes = [ctypes.c_void_p, ctypes.c_int]; x.XDefaultDepth.restype = ctypes.c_int
            x.XCreateSimpleWindow.argtypes = [ctypes.c_void_p, ctypes.c_ulong, ctypes.c_int, ctypes.c_int, ctypes.c_uint, ctypes.c_uint, ctypes.c_uint, ctypes.c_ulong, ctypes.c_ulong]
            x.XCreateSimpleWindow.restype = ctypes.c_ulong
            x.XSelectInput.argtypes = [ctypes.c_void_p, ctypes.c_ulong, ctypes.c_long]
            x.XStoreName.argtypes = [ctypes.c_void_p, ctypes.c_ulong, ctypes.c_char_p]
            x.XMapWindow.argtypes = [ctypes.c_void_p, ctypes.c_ulong]
            x.XFlush.argtypes = [ctypes.c_void_p]
            x.XPending.argtypes = [ctypes.c_void_p]; x.XPending.restype = ctypes.c_int
            x.XNextEvent.argtypes = [ctypes.c_void_p, ctypes.POINTER(_X11Event)]
            x.XCreateGC.argtypes = [ctypes.c_void_p, ctypes.c_ulong, ctypes.c_ulong, ctypes.c_void_p]; x.XCreateGC.restype = ctypes.c_void_p
            x.XFreeGC.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
            x.XPutImage.argtypes = [ctypes.c_void_p, ctypes.c_ulong, ctypes.c_void_p, ctypes.POINTER(_XImage), ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_uint, ctypes.c_uint]
            x.XCreateImage.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_uint, ctypes.c_int, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint, ctypes.c_uint, ctypes.c_int, ctypes.c_int]; x.XCreateImage.restype = ctypes.POINTER(_XImage)
            x.XDestroyImage.argtypes = [ctypes.POINTER(_XImage)]; x.XDestroyImage.restype = ctypes.c_int
            x.XDestroyWindow.argtypes = [ctypes.c_void_p, ctypes.c_ulong]
            x.XIconifyWindow.argtypes = [ctypes.c_void_p, ctypes.c_ulong, ctypes.c_int]
            x.XInternAtom.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_int]; x.XInternAtom.restype = ctypes.c_ulong
            x.XSetWMProtocols.argtypes = [ctypes.c_void_p, ctypes.c_ulong, ctypes.POINTER(ctypes.c_ulong), ctypes.c_int]
            x.XLookupKeysym.argtypes = [ctypes.POINTER(_X11KeyEvent), ctypes.c_int]; x.XLookupKeysym.restype = ctypes.c_ulong
            x.XLookupString.argtypes = [ctypes.POINTER(_X11KeyEvent), ctypes.c_char_p, ctypes.c_int, ctypes.POINTER(ctypes.c_ulong), ctypes.c_void_p]; x.XLookupString.restype = ctypes.c_int
            self.display = x.XOpenDisplay(None)
            if not self.display: raise RuntimeError("DISPLAY/X11 indisponible")
            self.screen = x.XDefaultScreen(self.display)
            self.root = x.XRootWindow(self.display, self.screen)
            self.visual = x.XDefaultVisual(self.display, self.screen)
            self.depth = x.XDefaultDepth(self.display, self.screen)
            self.windows: Dict[int, Dict[str, Any]] = {}; self.next_id=1
            self._wm_delete = x.XInternAtom(self.display, b"WM_DELETE_WINDOW", False)

        @staticmethod
        def _mask_shift(mask: int) -> int:
            if not mask: return 0
            shift=0
            while ((mask >> shift) & 1) == 0: shift += 1
            return shift
        @staticmethod
        def _scale(v: int, bits: int) -> int:
            return (int(v) * ((1 << bits) - 1) + 127) // 255 if bits else 0
        def _pixel_value(self, color: int, image: _XImage) -> int:
            r,g,b=(color>>16)&255,(color>>8)&255,color&255
            val=0
            im=image.contents if hasattr(image, "contents") else image
            for c,mask in ((r,int(im.red_mask)),(g,int(im.green_mask)),(b,int(im.blue_mask))):
                if mask:
                    bits=mask.bit_count(); shift=self._mask_shift(mask)
                    val |= (self._scale(c,bits) << shift) & mask
            return val
        def _encode_pixels(self, renderer: SoftwareRenderer, image: _XImage) -> ctypes.Array:
            im=image.contents if hasattr(image, "contents") else image
            bpp=max(1, (int(im.bits_per_pixel)+7)//8); stride=max(1,int(im.bytes_per_line)); total=stride*renderer.height
            buf=ctypes.create_string_buffer(total)
            order="little" if int(im.byte_order)==self.LSBFirst else "big"
            base=ctypes.addressof(buf)
            for y in range(renderer.height):
                row=renderer.pixels[y*renderer.width:(y+1)*renderer.width]; off=y*stride
                for x,color in enumerate(row):
                    pv=self._pixel_value(color,image); raw=int(pv).to_bytes(bpp,order,signed=False)
                    start=off+x*bpp
                    if start+bpp <= total:
                        ctypes.memmove(base+start, raw, bpp)
            return buf
        def _rebuild_image(self,item):
            x=self.x11; renderer=item["renderer"]; old=item.get("image")
            if old:
                try:
                    old.contents.data=None; x.XDestroyImage(old)
                except Exception: pass
            initial=ctypes.create_string_buffer(max(1, renderer.width*renderer.height*4))
            img=x.XCreateImage(self.display,self.visual,self.depth,self.ZPixmap,0,ctypes.cast(initial,ctypes.c_char_p),renderer.width,renderer.height,32,0)
            if not img: raise RuntimeError("XCreateImage a échoué")
            item["image"]=img
            encoded=self._encode_pixels(renderer,img)
            img.contents.data=ctypes.cast(encoded,ctypes.c_void_p)
            item["buffer"]=encoded
        def _get(self,wid):
            item=self.windows.get(int(wid))
            if not item or not item.get("alive"): raise RuntimeError("fenêtre graphique fermée")
            return item
        def window(self,title,width,height,pid):
            w=max(160,min(int(width),4096)); h=max(80,min(int(height),4096)); x=self.x11
            hwnd=x.XCreateSimpleWindow(self.display,self.root,100,100,w,h,1,0,0)
            if not hwnd: raise RuntimeError("XCreateSimpleWindow a échoué")
            x.XSelectInput(self.display,hwnd,self.EventMask); x.XStoreName(self.display,hwnd,str(title).encode("utf-8",errors="replace"))
            prot=(ctypes.c_ulong*self._one())(self._wm_delete); x.XSetWMProtocols(self.display,hwnd,prot,1)
            gc=x.XCreateGC(self.display,hwnd,0,None)
            wid=self.next_id; self.next_id+=1
            item={"xwindow":hwnd,"gc":gc,"renderer":SoftwareRenderer(w,h),"pid":int(pid),"title":str(title),"keys":set(),"pressed_keys":set(),"buttons":set(),"mouse_x":0,"mouse_y":0,"text_input_enabled":False,"text_buffer":[],"close_requested":False,"alive":True,"on_close":None,"image":None,"buffer":None}
            self.windows[wid]=item; self._rebuild_image(item); x.XMapWindow(self.display,hwnd); x.XFlush(self.display); return wid
        @staticmethod
        def _one(): return 1
        def clear(self,wid,color): self._get(wid)["renderer"].clear(color)
        def pixel(self,wid,xv,yv,color): self._get(wid)["renderer"].pixel(xv,yv,color)
        def rect(self,wid,xv,yv,w,h,color,fill=True): self._get(wid)["renderer"].rect(xv,yv,w,h,color,fill)
        def line(self,wid,x1,y1,x2,y2,color,width=1): self._get(wid)["renderer"].line(x1,y1,x2,y2,color,width)
        def circle(self,wid,xv,yv,r,color,fill=True): self._get(wid)["renderer"].circle(xv,yv,r,color,fill)
        def text(self,wid,xv,yv,text,color,size=16):
            scale=max(1,int(round(max(1,int(size))/7.0))); self._get(wid)["renderer"].text(xv,yv,text,color,scale)
        def image_draw(self,wid,image,x,y): self._get(wid)["renderer"].image_draw(image,x,y)
        def image_draw_scaled(self,wid,image,x,y,w,h): self._get(wid)["renderer"].image_draw_scaled(image,x,y,w,h)
        def present(self,wid):
            item=self._get(wid); self._rebuild_image(item); x=self.x11; img=item["image"]
            x.XPutImage(self.display,item["xwindow"],item["gc"],img,0,0,0,0,item["renderer"].width,item["renderer"].height); x.XFlush(self.display)
            item["renderer"].frame_count+=1; item["renderer"].dirty=False
        def minimize(self,wid):
            item=self._get(wid); self.x11.XIconifyWindow(self.display,item["xwindow"],self.screen); self.x11.XFlush(self.display)
        def close(self,wid):
            item=self.windows.pop(int(wid),None)
            if not item: return
            item["alive"]=False; hwnd=item["xwindow"]
            try: item["image"].contents.data=None; self.x11.XDestroyImage(item["image"])
            except Exception: pass
            try: self.x11.XFreeGC(self.display,item["gc"]); self.x11.XDestroyWindow(self.display,hwnd); self.x11.XFlush(self.display)
            except Exception: pass
        def _install_close_callback(self,wid,callback): self._get(wid)["on_close"]=callback
        def key_down(self,wid,key):
            item=self._get(wid); q=str(key).upper();
            aliases={"ESC":"ESC","ESCAPE":"ESC","ENTER":"ENTER","SPACE":"SPACE","LEFT":"LEFT","RIGHT":"RIGHT","UP":"UP","DOWN":"DOWN"}
            return q in {aliases.get(str(k).upper(),str(k).upper()) for k in item["keys"]}
        def key_pressed(self,wid,key):
            item=self._get(wid); q=str(key).upper();
            if q in {str(k).upper() for k in item.get("pressed_keys",set())}:
                item["pressed_keys"].discard(q)
                return True
            return False
        def text_input(self,wid,action="get"):
            item=self._get(wid); mode=str(action or "get").strip().lower()
            if mode in ("start","on","begin"):
                item["text_input_enabled"]=True; item["text_buffer"]=[]; return ""
            if mode in ("stop","off","end"):
                item["text_input_enabled"]=False; return "".join(item.get("text_buffer",[]))
            if mode in ("clear","reset"):
                item["text_buffer"]=[]; return ""
            return "".join(item.get("text_buffer",[]))
        def mouse_x(self,wid): return int(self._get(wid)["mouse_x"])
        def mouse_y(self,wid): return int(self._get(wid)["mouse_y"])
        def mouse_down(self,wid,button): return int(button) in self._get(wid)["buttons"]
        def close_requested(self,wid): return bool(self._get(wid)["close_requested"])
        def alive(self,wid): return bool(self.windows.get(int(wid),{}).get("alive",False))
        def _key_name(self,ks):
            ks=int(ks); special={self.XK_ESCAPE:"ESC",0xFF0D:"ENTER",0x20:"SPACE",0xFF51:"LEFT",0xFF52:"UP",0xFF53:"RIGHT",0xFF54:"DOWN"}
            if ks in special: return special[ks]
            if 0xFFBE<=ks<=0xFFD9: return f"F{ks-0xFFBD}"
            try:
                if 32<=ks<127: return chr(ks).upper()
            except Exception: pass
            return f"KEY_{ks:X}"
        def pump_events(self):
            x=self.x11
            while x.XPending(self.display)>0:
                ev=_X11Event(); x.XNextEvent(self.display,ctypes.byref(ev)); typ=int(ev.type)
                wid=None
                window_id=None
                if typ in (self.KeyPress,self.KeyRelease): window_id=int(ev.xkey.window)
                elif typ in (self.ButtonPress,self.ButtonRelease): window_id=int(ev.xbutton.window)
                elif typ==self.MotionNotify: window_id=int(ev.xmotion.window)
                elif typ==self.ConfigureNotify: window_id=int(ev.xconfigure.window)
                elif typ==self.Expose: window_id=int(ev.xexpose.window)
                elif typ==self.ClientMessage: window_id=int(ev.xclient.window)
                for k,v in self.windows.items():
                    if int(v["xwindow"])==window_id: wid=k; break
                if wid is None: continue
                item=self.windows.get(wid)
                if not item: continue
                if typ==self.ClientMessage and int(ev.xclient.message_type)==int(self._wm_delete):
                    item["close_requested"]=True; item["alive"]=False; self.windows.pop(wid,None)
                    cb=item.get("on_close")
                    if cb:
                        try: cb()
                        except Exception: pass
                    try: x.XDestroyWindow(self.display,item["xwindow"]); x.XFlush(self.display)
                    except Exception: pass
                elif typ==self.KeyPress:
                    keysym = int(x.XLookupKeysym(ctypes.byref(ev.xkey),0))
                    key_name = self._key_name(keysym)
                    if key_name not in item["keys"]:
                        item["pressed_keys"].add(key_name)
                    item["keys"].add(key_name)
                    if item.get("text_input_enabled", False):
                        if keysym == 0xFF08:
                            if item["text_buffer"]: item["text_buffer"].pop()
                        elif keysym == 0xFF0D:
                            item["text_buffer"].append("\n")
                        else:
                            # XLookupString respecte la disposition/locale X11 et
                            # permet d'obtenir le caractère réellement saisi, pas
                            # seulement le KeySym ASCII.
                            raw = ctypes.create_string_buffer(16)
                            ks_out = ctypes.c_ulong(0)
                            n = int(x.XLookupString(ctypes.byref(ev.xkey), raw, 15, ctypes.byref(ks_out), None))
                            if n > 0:
                                try:
                                    item["text_buffer"].append(raw.raw[:n].decode("utf-8"))
                                except UnicodeDecodeError:
                                    item["text_buffer"].append(raw.raw[:n].decode("latin-1", errors="replace"))
                elif typ==self.KeyRelease:
                    item["keys"].discard(self._key_name(x.XLookupKeysym(ctypes.byref(ev.xkey),0)))
                elif typ==self.MotionNotify:
                    item["mouse_x"],item["mouse_y"]=int(ev.xmotion.x),int(ev.xmotion.y)
                elif typ in (self.ButtonPress,self.ButtonRelease):
                    b=int(ev.xbutton.button); item["mouse_x"],item["mouse_y"]=int(ev.xbutton.x),int(ev.xbutton.y)
                    if typ==self.ButtonPress: item["buttons"].add(b)
                    else: item["buttons"].discard(b)
                elif typ==self.ConfigureNotify:
                    nw,nh=max(1,int(ev.xconfigure.width)),max(1,int(ev.xconfigure.height))
                    if nw!=item["renderer"].width or nh!=item["renderer"].height:
                        item["renderer"].resize(nw,nh); self._rebuild_image(item)
                elif typ==self.Expose:
                    try:
                        self._rebuild_image(item); x.XPutImage(self.display,item["xwindow"],item["gc"],item["image"],0,0,0,0,item["renderer"].width,item["renderer"].height); x.XFlush(self.display)
                    except Exception: pass
        def debug_info(self,wid):
            item=self._get(wid); r=item["renderer"]
            return {"title":item["title"],"width":r.width,"height":r.height,"alive":item["alive"],"close_requested":item["close_requested"],"mouse_x":item["mouse_x"],"mouse_y":item["mouse_y"],"keys":sorted(item["keys"]),"buttons":sorted(item["buttons"]),"renderer":r.stats(),"native":"X11"}
        def shutdown(self):
            for wid in list(self.windows): self.close(wid)
            if self.display:
                try: self.x11.XCloseDisplay(self.display)
                except Exception: pass


class _NSPoint(ctypes.Structure):
    _fields_ = [("x", ctypes.c_double), ("y", ctypes.c_double)]
class _NSSize(ctypes.Structure):
    _fields_ = [("width", ctypes.c_double), ("height", ctypes.c_double)]
class _NSRect(ctypes.Structure):
    _fields_ = [("origin", _NSPoint), ("size", _NSSize)]

# ----------------------------------------------------------------
# macOS Cocoa backend natif (Objective-C runtime + CoreGraphics, ctypes)
# ----------------------------------------------------------------
class CocoaGraphicsBackend(GraphicsBackend):
    """Backend macOS natif. Nécessite un processus Python macOS avec AppKit."""
    name = "software-renderer+cocoa"
    def __init__(self):
        if sys.platform != "darwin": raise RuntimeError("backend Cocoa demandé hors macOS")
        try:
            self.objc=ctypes.CDLL(ctypes.util.find_library("objc") or "/usr/lib/libobjc.A.dylib")
            self.appkit=ctypes.CDLL("/System/Library/Frameworks/AppKit.framework/AppKit")
            self.cg=ctypes.CDLL("/System/Library/Frameworks/CoreGraphics.framework/CoreGraphics")
        except Exception as exc: raise RuntimeError(f"AppKit/Objective-C indisponible: {exc}") from exc
        self.objc.objc_getClass.argtypes=[ctypes.c_char_p]; self.objc.objc_getClass.restype=ctypes.c_void_p
        self.objc.sel_registerName.argtypes=[ctypes.c_char_p]; self.objc.sel_registerName.restype=ctypes.c_void_p
        self.objc.objc_msgSend.restype=ctypes.c_void_p
        self.windows={}; self.next_id=1
        self._msg=self._make_msg
        self._setup_cg()
        self._setup_app()
    def _setup_cg(self):
        self.cg.CGColorSpaceCreateDeviceRGB.restype=ctypes.c_void_p
        self.cg.CGDataProviderCreateWithData.argtypes=[ctypes.c_void_p,ctypes.c_void_p,ctypes.c_size_t,ctypes.c_void_p]; self.cg.CGDataProviderCreateWithData.restype=ctypes.c_void_p
        self.cg.CGImageCreate.argtypes=[ctypes.size_t,ctypes.size_t,ctypes.size_t,ctypes.size_t,ctypes.size_t,ctypes.c_void_p,ctypes.c_uint32,ctypes.c_void_p,ctypes.c_void_p,ctypes.c_bool,ctypes.c_int]; self.cg.CGImageCreate.restype=ctypes.c_void_p
        self.cg.CGImageRelease.argtypes=[ctypes.c_void_p]
        self.cg.CGColorSpaceRelease.argtypes=[ctypes.c_void_p]
        self.cg.CGDataProviderRelease.argtypes=[ctypes.c_void_p]
    def _make_msg(self,obj,selector,restype=ctypes.c_void_p,argtypes=(),args=()):
        sel=self.objc.sel_registerName(selector.encode("utf-8")); proto=ctypes.CFUNCTYPE(restype,ctypes.c_void_p,ctypes.c_void_p,*argtypes); fn=proto(self.objc.objc_msgSend); return fn(obj,sel,*args)
    def _cls(self,name): return self.objc.objc_getClass(name.encode())
    @staticmethod
    def _nsrect(x,y,w,h):
        return _NSRect(_NSPoint(float(x),float(y)), _NSSize(float(w),float(h)))
    @staticmethod
    def _nssize(w,h):
        return _NSSize(float(w),float(h))
    def _setup_app(self):
        NSApp=self._msg(self._cls("NSApplication"),"sharedApplication")
        self.app=NSApp
        self._msg(self.app,"setActivationPolicy:",None,(ctypes.c_long,),args=(0,))
        try:
            self._msg(self.app,"finishLaunching")
        except Exception:
            pass
        self._msg(self.app,"activateIgnoringOtherApps:",None,(ctypes.c_bool,),args=(True,))
        # Apple virtual key codes.  Ne pas déduire le code d'une lettre avec
        # ord('A'): les claviers macOS utilisent un mapping physique différent.
        self._keycodes = {
            "A":0,"S":1,"D":2,"F":3,"H":4,"G":5,"Z":6,"X":7,"C":8,"V":9,
            "B":11,"Q":12,"W":13,"E":14,"R":15,"Y":16,"T":17,"1":18,"2":19,
            "3":20,"4":21,"6":22,"5":23,"=":24,"9":25,"7":26,"-":27,"8":28,"0":29,
            "]":30,"O":31,"U":32,"[":33,"I":34,"P":35,"L":37,"J":38,"K":40,
            ";":41,"\\":42,",":43,"/":44,"N":45,"M":46,".":47,"`":50,
            "ENTER":36,"RETURN":36,"TAB":48,"SPACE":49,"BACKSPACE":51,"ESC":53,
            "ESCAPE":53,"SHIFT":56,"CTRL":59,"CONTROL":59,"ALT":58,"OPTION":58,
            "LEFT":123,"RIGHT":124,"DOWN":125,"UP":126,"DELETE":117,"DEL":117,
            "F1":122,"F2":120,"F3":99,"F4":118,"F5":96,"F6":97,"F7":98,"F8":100,
            "F9":101,"F10":109,"F11":103,"F12":111,
        }
        # NSEvent.type values. Le masque est volontairement large pour que
        # clavier/souris/fermeture soient pompés par miniOS lui-même.
        self._event_mask = ctypes.c_ulonglong(
            (1 << 1) | (1 << 2) | (1 << 3) | (1 << 4) | (1 << 5) |
            (1 << 6) | (1 << 7) | (1 << 10) | (1 << 11) | (1 << 12) |
            (1 << 25) | (1 << 26) | (1 << 27)
        ).value
        self._etype = {
            "left_down":1,"left_up":2,"right_down":3,"right_up":4,
            "moved":5,"key_down":10,"key_up":11,"flags":12,
            "other_down":25,"other_up":26,"other_dragged":27,
        }
    def _make_image(self,renderer,item):
        # macOS bitmap: little-endian BGRA, premultiplied alpha.
        buf=bytearray(renderer.width*renderer.height*4)
        j=0
        for c in renderer.pixels:
            buf[j]=c&255; buf[j+1]=(c>>8)&255; buf[j+2]=(c>>16)&255; buf[j+3]=255; j+=4
        item["buffer"]=ctypes.create_string_buffer(bytes(buf))
        cs=self.cg.CGColorSpaceCreateDeviceRGB(); provider=self.cg.CGDataProviderCreateWithData(None,ctypes.cast(item["buffer"],ctypes.c_void_p),len(buf),None)
        # kCGImageAlphaPremultipliedLast = 1, kCGBitmapByteOrder32Little = 0x2000
        image=self.cg.CGImageCreate(renderer.width,renderer.height,8,32,renderer.width*4,cs,0x2002,provider,None,True,0)
        self.cg.CGColorSpaceRelease(cs); self.cg.CGDataProviderRelease(provider)
        if not image: raise RuntimeError("CGImageCreate a échoué")
        return image
    def _set_image(self,item):
        old_cg = item.get("cgimage")
        old_nsimage = item.get("nsimage")
        image=self._make_image(item["renderer"],item)
        NSImage=self._cls("NSImage"); nsimg=self._msg(self._msg(NSImage,"alloc"),"initWithCGImage:size:",argtypes=(ctypes.c_void_p,_NSSize),args=(image,self._nssize(item["renderer"].width,item["renderer"].height)))
        self._msg(item["image_view"],"setImage:",None,(ctypes.c_void_p,),args=(nsimg,))
        item["nsimage"]=nsimg; item["cgimage"]=image
        # initWithCGImage:size: renvoie un objet retenu par nous. NSImageView
        # retient aussi sa nouvelle image. On libère donc notre ancienne
        # référence après le remplacement pour éviter une fuite à chaque frame.
        if old_nsimage:
            try: self._msg(old_nsimage,"release")
            except Exception: pass
        if old_cg:
            try: self.cg.CGImageRelease(old_cg)
            except Exception: pass
    def _get(self,wid):
        item=self.windows.get(int(wid));
        if not item or not item.get("alive"): raise RuntimeError("fenêtre graphique fermée")
        return item
    def window(self,title,width,height,pid):
        w=max(160,min(int(width),4096)); h=max(80,min(int(height),4096)); rect=self._nsrect(100,100,w,h)
        NSWindow=self._cls("NSWindow"); style=(1<<0)|(1<<1)|(1<<2)|(1<<3)
        win=self._msg(self._msg(NSWindow,"alloc"),"initWithContentRect:styleMask:backing:defer:",argtypes=(_NSRect,ctypes.c_ulong,ctypes.c_ulong,ctypes.c_bool),args=(rect,style,2,False))
        if not win: raise RuntimeError("NSWindow n'a pas pu être créée")
        self._msg(win,"setTitle:",None,(ctypes.c_void_p,),args=(self._nsstring(str(title)),))
        NSImageView=self._cls("NSImageView"); iv=self._msg(self._msg(NSImageView,"alloc"),"initWithFrame:",argtypes=(_NSRect,),args=(self._nsrect(0,0,w,h),))
        self._msg(iv,"setImageScaling:",None,(ctypes.c_long,),args=(3,))
        self._msg(win,"setContentView:",None,(ctypes.c_void_p,),args=(iv,))
        self._msg(win,"makeKeyAndOrderFront:",None,(ctypes.c_void_p,),args=(None,))
        self._msg(self.app,"activateIgnoringOtherApps:",None,(ctypes.c_bool,),args=(True,))
        wid=self.next_id; self.next_id+=1; item={"window":win,"image_view":iv,"renderer":SoftwareRenderer(w,h),"title":str(title),"pid":int(pid),"alive":True,"close_requested":False,"keys":set(),"pressed_keys":set(),"key_prev_state":set(),"buttons":set(),"mouse_x":0,"mouse_y":0,"text_input_enabled":False,"text_buffer":[],"buffer":None,"nsimage":None,"cgimage":None}
        self.windows[wid]=item; self._set_image(item); return wid
    def _nsstring(self,s): return self._msg(self._cls("NSString"),"stringWithUTF8String:",argtypes=(ctypes.c_char_p,),args=(str(s).encode("utf-8"),))
    def clear(self,wid,color): self._get(wid)["renderer"].clear(color)
    def pixel(self,wid,x,y,color): self._get(wid)["renderer"].pixel(x,y,color)
    def rect(self,wid,x,y,w,h,color,fill=True): self._get(wid)["renderer"].rect(x,y,w,h,color,fill)
    def line(self,wid,x1,y1,x2,y2,color,width=1): self._get(wid)["renderer"].line(x1,y1,x2,y2,color,width)
    def circle(self,wid,x,y,r,color,fill=True): self._get(wid)["renderer"].circle(x,y,r,color,fill)
    def text(self,wid,x,y,text,color,size=16): self._get(wid)["renderer"].text(x,y,text,color,max(1,int(round(max(1,int(size))/7.0))))
    def image_draw(self,wid,image,x,y): self._get(wid)["renderer"].image_draw(image,x,y)
    def image_draw_scaled(self,wid,image,x,y,w,h): self._get(wid)["renderer"].image_draw_scaled(image,x,y,w,h)
    def present(self,wid):
        item=self._get(wid); self._set_image(item); item["renderer"].frame_count+=1; item["renderer"].dirty=False
    def minimize(self,wid): self._msg(self._get(wid)["window"],"miniaturize:",None,(ctypes.c_void_p,),args=(None,))
    def close(self,wid):
        item=self.windows.pop(int(wid),None)
        if item:
            item["alive"]=False
            try: self._msg(item["window"],"close")
            except Exception: pass
    def _install_close_callback(self,wid,callback): self._get(wid)["on_close"]=callback
    def _key_state_cocoa(self,wid,key):
        q=str(key).upper().strip()
        kc=getattr(self,"_keycodes",{}).get(q)
        if kc is None and len(q)==1:
            # Lettres non présentes dans le mapping physique ne doivent pas
            # être converties arbitrairement en code ASCII.
            kc=getattr(self,"_keycodes",{}).get(q)
        if kc is None: return False
        try:
            self.cg.CGEventSourceKeyState.argtypes=[ctypes.c_int,ctypes.c_uint16]; self.cg.CGEventSourceKeyState.restype=ctypes.c_bool
            return bool(self.cg.CGEventSourceKeyState(1,ctypes.c_uint16(kc)))
        except Exception: return False
    def key_down(self,wid,key):
        return self._key_state_cocoa(wid,key)
    def key_pressed(self,wid,key):
        item=self._get(wid); q=str(key).upper()
        current=self._key_state_cocoa(wid,q)
        previous=q in item.get("key_prev_state",set())
        if current: item.setdefault("key_prev_state",set()).add(q)
        else: item.setdefault("key_prev_state",set()).discard(q)
        return bool(current and not previous)
    def text_input(self,wid,action="get"):
        item=self._get(wid); mode=str(action or "get").strip().lower()
        if mode in ("start","on","begin"):
            item["text_input_enabled"]=True; item["text_buffer"]=[]; return ""
        if mode in ("stop","off","end"):
            item["text_input_enabled"]=False; return "".join(item.get("text_buffer",[]))
        if mode in ("clear","reset"):
            item["text_buffer"]=[]; return ""
        return "".join(item.get("text_buffer",[]))
    def _mouse_position_cocoa(self,wid):
        item=self._get(wid)
        try:
            # NSEvent.mouseLocation est déjà exprimé dans le repère écran Cocoa.
            point=self._msg(self._cls("NSEvent"),"mouseLocation",restype=_NSPoint)
            local=self._msg(item["window"],"convertPointFromScreen:",restype=_NSPoint,argtypes=(_NSPoint,),args=(point,))
            item["mouse_x"]=int(round(local.x))
            item["mouse_y"]=int(round(float(item["renderer"].height)-float(local.y)))
        except Exception:
            pass
        return int(item["mouse_x"]), int(item["mouse_y"])
    def mouse_x(self,wid): return self._mouse_position_cocoa(wid)[0]
    def mouse_y(self,wid): return self._mouse_position_cocoa(wid)[1]
    def mouse_down(self,wid,button):
        try:
            self.cg.CGEventSourceButtonState.argtypes=[ctypes.c_int,ctypes.c_uint32]; self.cg.CGEventSourceButtonState.restype=ctypes.c_bool
            return bool(self.cg.CGEventSourceButtonState(1,max(0,int(button)-1)))
        except Exception: return False
    def close_requested(self,wid):
        item=self.windows.get(int(wid));
        if not item: return True
        try:
            visible=bool(self._msg(item["window"],"isVisible",restype=ctypes.c_bool))
            if not visible: item["close_requested"]=True; item["alive"]=False
        except Exception: pass
        return bool(item["close_requested"])
    def alive(self,wid): return bool(self.windows.get(int(wid),{}).get("alive",False))
    def _event_key_name(self,key_code):
        q=int(key_code)
        reverse={v:k for k,v in self._keycodes.items()}
        return reverse.get(q,f"KEY_{q:02X}")
    def _event_window_item(self,event):
        try:
            ew=self._msg(event,"window",restype=ctypes.c_void_p)
        except Exception:
            return None
        if not ew:
            return None
        for item in self.windows.values():
            ptr=int(ctypes.cast(item["window"],ctypes.c_void_p).value or 0)
            if ptr==int(ew):
                return item
        return None
    def _event_chars(self,event):
        try:
            chars=self._msg(event,"charactersIgnoringModifiers",restype=ctypes.c_void_p)
            if not chars:
                return ""
            raw=self._msg(chars,"UTF8String",restype=ctypes.c_char_p)
            return raw.decode("utf-8",errors="replace") if raw else ""
        except Exception:
            return ""
    def _mark_closed(self,item):
        if not item.get("alive",False):
            return
        item["close_requested"]=True; item["alive"]=False
        cb=item.get("on_close")
        if cb:
            try: cb()
            except Exception: pass
    def pump_events(self):
        # Boucle Cocoa explicitement pilotée par miniOS. Aucun toolkit Python.
        mode=self._nsstring("NSDefaultRunLoopMode")
        until=self._msg(self._cls("NSDate"),"dateWithTimeIntervalSinceNow:",argtypes=(ctypes.c_double,),args=(0.0,))
        while True:
            try:
                event=self._msg(self.app,"nextEventMatchingMask:untilDate:inMode:dequeue:",restype=ctypes.c_void_p,argtypes=(ctypes.c_ulonglong,ctypes.c_void_p,ctypes.c_void_p,ctypes.c_bool),args=(self._event_mask,until,mode,True))
            except Exception:
                break
            if not event:
                break
            try:
                et=int(self._msg(event,"type",restype=ctypes.c_ulong))
            except Exception:
                et=-1
            item=self._event_window_item(event)
            if item is not None:
                if et==self._etype["key_down"]:
                    try: kc=int(self._msg(event,"keyCode",restype=ctypes.c_ushort))
                    except Exception: kc=-1
                    name=self._event_key_name(kc)
                    if name not in item["keys"]: item["pressed_keys"].add(name)
                    item["keys"].add(name)
                    if item.get("text_input_enabled",False):
                        if kc==self._keycodes.get("BACKSPACE",51):
                            if item["text_buffer"]: item["text_buffer"].pop()
                        elif kc==self._keycodes.get("ENTER",36):
                            item["text_buffer"].append("\n")
                        else:
                            chars=self._event_chars(event)
                            if chars: item["text_buffer"].append(chars)
                elif et==self._etype["key_up"]:
                    try: kc=int(self._msg(event,"keyCode",restype=ctypes.c_ushort))
                    except Exception: kc=-1
                    item["keys"].discard(self._event_key_name(kc))
                elif et in (self._etype["moved"],self._etype["other_dragged"]):
                    try:
                        pt=self._msg(event,"locationInWindow",restype=_NSPoint)
                        item["mouse_x"]=int(round(pt.x)); item["mouse_y"]=int(round(float(item["renderer"].height)-float(pt.y)))
                    except Exception: pass
                elif et in (self._etype["left_down"],self._etype["right_down"],self._etype["other_down"],self._etype["left_up"],self._etype["right_up"],self._etype["other_up"]):
                    try:
                        pt=self._msg(event,"locationInWindow",restype=_NSPoint)
                        item["mouse_x"]=int(round(pt.x)); item["mouse_y"]=int(round(float(item["renderer"].height)-float(pt.y)))
                    except Exception: pass
                    if et==self._etype["left_down"]: item["buttons"].add(1)
                    elif et==self._etype["left_up"]: item["buttons"].discard(1)
                    elif et==self._etype["right_down"]: item["buttons"].add(3)
                    elif et==self._etype["right_up"]: item["buttons"].discard(3)
                    elif et==self._etype["other_down"]: item["buttons"].add(2)
                    elif et==self._etype["other_up"]: item["buttons"].discard(2)
            try:
                self._msg(self.app,"sendEvent:",None,(ctypes.c_void_p,),args=(event,))
            except Exception:
                pass
        for item in list(self.windows.values()):
            try:
                if not bool(self._msg(item["window"],"isVisible",restype=ctypes.c_bool)):
                    self._mark_closed(item)
            except Exception:
                pass
    def debug_info(self,wid):
        item=self._get(wid); r=item["renderer"]
        return {"title":item["title"],"width":r.width,"height":r.height,"alive":item["alive"],"close_requested":item["close_requested"],"native":"Cocoa/AppKit","renderer":r.stats()}
    def shutdown(self):
        for wid in list(self.windows): self.close(wid)


minios_ios_graphics_host = None

def set_ios_graphics_host(host) -> None:
    """Installe le pont UIKit fourni par l'application hôte iOS."""
    global minios_ios_graphics_host
    minios_ios_graphics_host = host


class IOSHostGraphicsBackend(GraphicsBackend):
    """Pont graphique UIKit pour un hôte iOS.

    Le cœur miniOS reste identique. Sur iOS, l'application native hôte fournit
    l'affichage UIKit et reçoit un framebuffer RGBA depuis SoftwareRenderer.
    Le host doit exposer : window, present, minimize, close, close_requested,
    pump_events, key_down, mouse_x, mouse_y et mouse_down.
    """
    name = "software-renderer+ios-host"
    def __init__(self):
        host=globals().get("minios_ios_graphics_host")
        if host is None:
            raise RuntimeError("backend UIKit indisponible: miniOS doit être hébergé dans une application iOS")
        self.host=host
        self.windows={}; self.next_id=1
    def window(self,title,width,height,pid):
        wid=self.next_id; self.next_id+=1; renderer=SoftwareRenderer(int(width),int(height));
        host_id=self.host.window(str(title),int(width),int(height),renderer, int(pid)); self.windows[wid]={"host_id":host_id,"renderer":renderer,"alive":True,"close_requested":False,"title":str(title),"pid":int(pid)}; return wid
    def _get(self,wid):
        item=self.windows.get(int(wid));
        if not item or not item["alive"]: raise RuntimeError("fenêtre graphique fermée")
        return item
    def clear(self,wid,c): self._get(wid)["renderer"].clear(c)
    def pixel(self,wid,x,y,c): self._get(wid)["renderer"].pixel(x,y,c)
    def rect(self,wid,x,y,w,h,c,fill=True): self._get(wid)["renderer"].rect(x,y,w,h,c,fill)
    def line(self,wid,x1,y1,x2,y2,c,width=1): self._get(wid)["renderer"].line(x1,y1,x2,y2,c,width)
    def circle(self,wid,x,y,r,c,fill=True): self._get(wid)["renderer"].circle(x,y,r,c,fill)
    def text(self,wid,x,y,text,c,size=16): self._get(wid)["renderer"].text(x,y,text,c,max(1,int(round(max(1,int(size))/7.0))))
    def image_draw(self,wid,image,x,y): self._get(wid)["renderer"].image_draw(image,x,y)
    def image_draw_scaled(self,wid,image,x,y,w,h): self._get(wid)["renderer"].image_draw_scaled(image,x,y,w,h)
    def present(self,wid):
        item=self._get(wid)
        r=item["renderer"]
        # Le host natif reçoit un tampon RGBA portable. Les pixels internes
        # miniOS restent en 0xRRGGBB ; aucune dépendance graphique Python.
        rgba=bytearray(len(r.pixels)*4)
        j=0
        for color in r.pixels:
            rgba[j]=(color >> 16) & 0xFF
            rgba[j+1]=(color >> 8) & 0xFF
            rgba[j+2]=color & 0xFF
            rgba[j+3]=0xFF
            j+=4
        self.host.present(item["host_id"],bytes(rgba),r.width,r.height)
        r.frame_count+=1; r.dirty=False
    def minimize(self,wid): self.host.minimize(self._get(wid)["host_id"])
    def close(self,wid):
        item=self.windows.pop(int(wid),None)
        if item:
            item["alive"]=False; self.host.close(item["host_id"])
    def key_down(self,wid,key): return bool(self.host.key_down(self._get(wid)["host_id"],str(key)))
    def key_pressed(self,wid,key):
        host_id = self._get(wid)["host_id"]
        fn = getattr(self.host, "key_pressed", None)
        return bool(fn(host_id, str(key))) if fn is not None else False
    def text_input(self,wid,action="get"):
        host_id = self._get(wid)["host_id"]
        fn = getattr(self.host, "text_input", None)
        return str(fn(host_id, str(action))) if fn is not None else ""
    def mouse_x(self,wid): return int(self.host.mouse_x(self._get(wid)["host_id"]))
    def mouse_y(self,wid): return int(self.host.mouse_y(self._get(wid)["host_id"]))
    def mouse_down(self,wid,b): return bool(self.host.mouse_down(self._get(wid)["host_id"],int(b)))
    def close_requested(self,wid): return bool(self._get(wid)["close_requested"] or self.host.close_requested(self._get(wid)["host_id"]))
    def alive(self,wid): return bool(self.windows.get(int(wid),{}).get("alive",False))
    def pump_events(self): self.host.pump_events()
    def debug_info(self,wid):
        i=self._get(wid); return {"title":i["title"],"width":i["renderer"].width,"height":i["renderer"].height,"alive":i["alive"],"close_requested":i["close_requested"],"native":"UIKit host","renderer":i["renderer"].stats()}
    def shutdown(self):
        for wid in list(self.windows):
            try:self.close(wid)
            except Exception:pass


class UnsupportedNativeBackend(GraphicsBackend):
    """Réserve l'architecture pour les backends natifs futurs."""
    name = "native-unavailable"
    def __init__(self, platform_name: str):
        self.platform_name = platform_name
    def window(self, title: str, width: int, height: int, pid: int) -> int:
        raise RuntimeError(
            f"backend graphique natif non implémenté pour {self.platform_name}; "
            "le moteur de rendu est indépendant, mais ce backend plateforme reste à développer"
        )


class GraphicsManager:
    """Pont thread-safe entre VM32 et le backend graphique natif."""

    def __init__(self, os_ref: Any):
        self.os_ref = os_ref
        self.backend: Optional[GraphicsBackend] = None
        self.active_by_pid: Dict[int, int] = {}
        self.logical_alive_by_pid: Dict[int, bool] = {}
        self.close_requested_by_pid: Dict[int, bool] = {}
        self._queue: "queue.Queue[Any]" = queue.Queue()
        self._main_thread: Optional[threading.Thread] = None
        self._ready = threading.Event()
        self._start_error: Optional[BaseException] = None
        self._lock = threading.RLock()
        self._stopping = False
        self._mainloop_running = False
        self._debug_by_pid: Dict[int, Dict[str, Any]] = {}

    @staticmethod
    def platform_backend_name() -> str:
        if sys.platform == "win32": return "Win32 natif (ctypes)"
        if sys.platform.startswith("linux"): return "X11 natif (ctypes)"
        if sys.platform == "darwin": return "Cocoa natif (ctypes)"
        if sys.platform in ("ios", "tvos"): return "UIKit via hôte iOS"
        return f"backend natif à définir ({sys.platform})"

    def _create_backend(self) -> GraphicsBackend:
        if sys.platform == "win32":
            return Win32GraphicsBackend()
        if sys.platform.startswith("linux"):
            return X11GraphicsBackend()
        if sys.platform == "darwin":
            return CocoaGraphicsBackend()
        if sys.platform in ("ios", "tvos"):
            return IOSHostGraphicsBackend()
        return UnsupportedNativeBackend(self.platform_backend_name())

    def _pump_queue(self):
        if self.backend is None:
            return
        for _ in range(256):
            try: request = self._queue.get_nowait()
            except queue.Empty: break
            op, args, kwargs, done, holder = request
            try:
                if op == "__quit__":
                    self._stopping = True
                    holder["result"] = None
                else:
                    holder["result"] = getattr(self.backend, op)(*args, **kwargs)
            except BaseException as exc:
                holder["error"] = exc
            finally:
                done.set()

    def run_mainloop(self) -> bool:
        if threading.current_thread() is not threading.main_thread():
            raise RuntimeError("le moteur graphique doit être démarré sur le thread principal")
        with self._lock:
            if self._mainloop_running: return True
            self._stopping = False; self._start_error = None
            try:
                self.backend = self._create_backend()
                self._main_thread = threading.current_thread()
                self._mainloop_running = True; self._ready.set()
            except BaseException as exc:
                self._start_error = exc; self._ready.set(); self.backend = None
                return False
        try:
            while not self._stopping:
                self._pump_queue()
                if self.backend is not None:
                    try: self.backend.pump_events()
                    except BaseException:
                        # Le backend ne doit pas pouvoir tuer miniOS.
                        pass
                time.sleep(0.001)
            return True
        finally:
            with self._lock:
                self._mainloop_running = False; self._stopping = True
            try:
                if self.backend is not None: self.backend.shutdown()
            except Exception: pass
            with self._lock:
                self.backend = None
                self.active_by_pid.clear(); self.logical_alive_by_pid.clear(); self.close_requested_by_pid.clear()
            self._ready.set()

    def _ensure_backend(self) -> GraphicsBackend:
        if self._start_error is not None:
            raise RuntimeError(f"backend graphique indisponible: {self._start_error}") from self._start_error
        if self.backend is None or not self._mainloop_running:
            raise RuntimeError("moteur graphique non démarré")
        return self.backend

    def _process_debug_event(self, pid: int, tag: str, message: str):
        try:
            proc = self.os_ref.processes.get(int(pid))
            if proc is not None and getattr(proc, "debug", False): proc.debug_event(tag, message)
        except Exception: pass

    def _record_debug(self, pid: int, op: str, duration_ms: float, error: Optional[BaseException] = None):
        pid = int(pid)
        with self._lock:
            d = self._debug_by_pid.setdefault(pid, {"calls":0,"errors":0,"presents":0,"windows_created":0,"last_op":"","last_error":"","last_duration_ms":0.0,"total_time_ms":0.0,"recent":[],"first_call_at":time.time(),"last_call_at":time.time()})
            d["calls"] += 1; d["last_op"] = str(op); d["last_duration_ms"] = float(duration_ms); d["total_time_ms"] += float(duration_ms); d["last_call_at"] = time.time()
            if op == "present": d["presents"] += 1
            if op == "window": d["windows_created"] += 1
            if error is not None:
                d["errors"] += 1; d["last_error"] = f"{type(error).__name__}: {error}"
            entry = {"op": str(op), "ms": round(float(duration_ms), 3)}
            if error is not None: entry["error"] = d["last_error"]
            d["recent"].append(entry)
            if len(d["recent"]) > 20: del d["recent"][:-20]

    def _call_pid(self, pid: int, op: str, *args, **kwargs):
        self._process_debug_event(pid, "GFX", f"APPEL {op} args={args!r} kwargs={kwargs!r}")
        started = time.perf_counter()
        try: result = self._call(op, *args, **kwargs)
        except BaseException as exc:
            self._record_debug(pid, op, (time.perf_counter()-started)*1000.0, exc)
            self._process_debug_event(pid, "GFX", f"ERREUR {op}: {type(exc).__name__}: {exc}"); raise
        self._record_debug(pid, op, (time.perf_counter()-started)*1000.0)
        self._process_debug_event(pid, "GFX", f"OK {op}"); return result

    def _call(self, op: str, *args, **kwargs):
        backend = self._ensure_backend()
        if threading.current_thread() is self._main_thread:
            return getattr(backend, op)(*args, **kwargs)
        done = threading.Event(); holder: Dict[str, Any] = {}
        self._queue.put((op, args, kwargs, done, holder))
        while not done.wait(timeout=0.05):
            if self._stopping: raise RuntimeError(f"moteur graphique arrêté pendant '{op}'")
        if "error" in holder: raise holder["error"]
        return holder.get("result")

    def _active(self, pid: int) -> int:
        pid=int(pid)
        with self._lock:
            wid=self.active_by_pid.get(pid); alive=bool(self.logical_alive_by_pid.get(pid,False))
        if not wid or not alive: raise RuntimeError("aucune fenêtre graphique active; utilisez window() d'abord")
        return wid

    def _window_is_closed(self, pid: int) -> bool:
        with self._lock: return not bool(self.logical_alive_by_pid.get(int(pid),False))

    def _call_active(self, pid: int, op: str, default: Any, *args, **kwargs):
        try: wid=self._active(pid)
        except RuntimeError: return default
        try: return self._call_pid(pid, op, wid, *args, **kwargs)
        except BaseException:
            if self._window_is_closed(pid): return default
            raise

    def window(self, title: str, width: int, height: int, pid: int) -> int:
        pid=int(pid); old=self.active_by_pid.pop(pid,None); self.logical_alive_by_pid[pid]=False; self.close_requested_by_pid[pid]=False
        if old and self.backend is not None:
            try: self._call_pid(pid,"close",old)
            except Exception: pass
        wid=int(self._call_pid(pid,"window",title,width,height,pid)); self.active_by_pid[pid]=wid; self.logical_alive_by_pid[pid]=True
        def mark_closed():
            with self._lock:
                self.logical_alive_by_pid[pid]=False; self.close_requested_by_pid[pid]=True; self.active_by_pid.pop(pid,None)
        try: self._call_pid(pid,"_install_close_callback",wid,mark_closed)
        except Exception:
            with self._lock: self.logical_alive_by_pid[pid]=False
            raise
        return wid

    def clear(self, pid: int, color: int): self._call_active(pid,"clear",None,color)
    def pixel(self, pid: int, x: int, y: int, color: int): self._call_active(pid,"pixel",None,x,y,color)
    def rect(self, pid: int, x: int, y: int, w: int, h: int, color: int): self._call_active(pid,"rect",None,x,y,w,h,color,True)
    def line(self, pid: int, x1: int, y1: int, x2: int, y2: int, color: int): self._call_active(pid,"line",None,x1,y1,x2,y2,color)
    def circle(self, pid: int, x: int, y: int, r: int, color: int): self._call_active(pid,"circle",None,x,y,r,color,True)
    def text(self, pid: int, x: int, y: int, value: str, color: int): self._call_active(pid,"text",None,x,y,value,color)
    def present(self, pid: int): self._call_active(pid,"present",None)

    def minimize(self, pid: int):
        self._call_active(int(pid), "minimize", None)

    def close(self,pid:int):
        pid=int(pid)
        with self._lock:
            self.logical_alive_by_pid[pid]=False; self.close_requested_by_pid.setdefault(pid,False); wid=self.active_by_pid.pop(pid,None)
        if wid and self.backend is not None and self._mainloop_running:
            try: self._call_pid(pid,"close",wid)
            except Exception: pass
    def key_down(self,pid:int,key:str)->bool: return bool(self._call_active(pid,"key_down",False,key))
    def text_input(self,pid:int,action:str="get")->str: return str(self._call_active(pid,"text_input","",action))
    def key_pressed(self,pid:int,key:str)->bool: return bool(self._call_active(pid,"key_pressed",False,key))
    def mouse_x(self,pid:int)->int: return int(self._call_active(pid,"mouse_x",0))
    def mouse_y(self,pid:int)->int: return int(self._call_active(pid,"mouse_y",0))
    def mouse_down(self,pid:int,button:int)->bool: return bool(self._call_active(pid,"mouse_down",False,button))
    def close_requested(self,pid:int)->bool: return bool(self.close_requested_by_pid.get(int(pid),False))
    def alive(self,pid:int)->bool:
        with self._lock: return bool(self.logical_alive_by_pid.get(int(pid),False))

    def debug_snapshot(self,pid:int)->Dict[str,Any]:
        pid=int(pid)
        with self._lock:
            stats=dict(self._debug_by_pid.get(pid,{})); stats["recent"]=list(self._debug_by_pid.get(pid,{}).get("recent",[])); wid=self.active_by_pid.get(pid); logical_alive=bool(self.logical_alive_by_pid.get(pid,False)); close_requested=bool(self.close_requested_by_pid.get(pid,False)); queue_size=self._queue.qsize(); mainloop=bool(self._mainloop_running); main_thread=self._main_thread.name if self._main_thread is not None else None
        info={"backend": self.backend.name if self.backend is not None else self.platform_backend_name(), "mainloop":mainloop, "main_thread":main_thread, "current_thread":threading.current_thread().name, "queue_size":queue_size, "window_id":wid, "logical_alive":logical_alive, "close_requested":close_requested, "stats":stats}
        if wid and self.backend is not None and mainloop:
            try: info["window"]=self._call("debug_info",wid)
            except Exception as exc: info["window_error"]=f"{type(exc).__name__}: {exc}"
        return info

    def request_quit_mainloop(self):
        if self.backend is None or not self._mainloop_running: return
        with self._lock: self._stopping=True
        self._queue.put(("__quit__",(),{},threading.Event(),{}))

    def shutdown(self):
        with self._lock: self._stopping=True


class NetworkSocketManager:
    """Gestionnaire de sockets réseau appartenant aux processus VM32.

    Les applications n'accèdent jamais directement aux sockets Python : elles
    manipulent des handles miniOS. Aucun exécutable réseau de l'hôte n'est lancé.
    """
    def __init__(self):
        self._lock = threading.RLock()
        self._next_handle = 1
        self._sockets: Dict[int, Tuple[int, socket.socket, str]] = {}

    def open(self, pid: int, sock: socket.socket, kind: str) -> int:
        with self._lock:
            handle = self._next_handle
            self._next_handle += 1
            self._sockets[handle] = (int(pid), sock, kind)
            return handle

    def get(self, pid: int, handle: int, expected_kind: Optional[str] = None) -> socket.socket:
        with self._lock:
            item = self._sockets.get(int(handle))
            if item is None:
                raise RuntimeError(f"handle réseau invalide: {handle}")
            owner, sock, kind = item
            if owner != int(pid):
                raise PermissionError("ce socket appartient à un autre processus")
            if expected_kind is not None and kind != expected_kind:
                raise RuntimeError(f"type de socket incorrect: attendu {expected_kind}, obtenu {kind}")
            return sock

    def close(self, pid: int, handle: int) -> bool:
        with self._lock:
            item = self._sockets.get(int(handle))
            if item is None:
                return False
            owner, sock, _kind = item
            if owner != int(pid):
                return False
            self._sockets.pop(int(handle), None)
        try:
            sock.close()
        except OSError:
            pass
        return True

    def close_all(self, pid: int) -> None:
        with self._lock:
            handles = [h for h, (owner, _sock, _kind) in self._sockets.items() if owner == int(pid)]
        for handle in handles:
            self.close(pid, handle)

    def describe(self) -> List[Tuple[int, int, str]]:
        with self._lock:
            return [(h, owner, kind) for h, (owner, _sock, kind) in self._sockets.items()]

NETWORK_SOCKETS = NetworkSocketManager()


def _network_local_addresses() -> List[str]:
    """Retourne les adresses locales connues sans lancer de programme externe."""
    seen: List[str] = []

    def add(addr: str):
        if addr and addr not in seen:
            seen.append(addr)

    add("127.0.0.1")
    try:
        add("::1")
    except Exception:
        pass

    try:
        hostname = socket.gethostname()
        infos = socket.getaddrinfo(hostname, None, socket.AF_UNSPEC, socket.SOCK_STREAM)
        for info in infos:
            add(info[4][0])
    except OSError:
        pass

    # Détermine l'adresse utilisée pour sortir vers Internet sans envoyer de paquet.
    for target in (("1.1.1.1", 53), ("8.8.8.8", 53)):
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            sock.settimeout(0.5)
            sock.connect(target)
            add(sock.getsockname()[0])
            break
        except OSError:
            pass
        finally:
            sock.close()
    return seen


def _network_interfaces() -> List[str]:
    """Retourne les noms d'interfaces via l'API socket Python standard."""
    try:
        return [name for _idx, name in socket.if_nameindex()]
    except (AttributeError, OSError):
        return []


def _host_ip_addresses() -> List[str]:
    return _network_local_addresses()


def _host_internet_check(timeout: float = 3.0) -> Tuple[bool, str]:
    """Vérifie Internet par socket TCP, sans outil externe."""
    targets = [("1.1.1.1", 443), ("8.8.8.8", 53)]
    last_error = "inconnu"
    for host, port in targets:
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        try:
            sock.settimeout(timeout)
            sock.connect((host, port))
            return True, f"connexion TCP vers {host}:{port} OK"
        except OSError as exc:
            last_error = str(exc)
        finally:
            sock.close()
    return False, last_error


def _icmp_checksum(data: bytes) -> int:
    if len(data) & 1:
        data += b"\x00"
    total = 0
    for i in range(0, len(data), 2):
        total += (data[i] << 8) | data[i + 1]
        total = (total & 0xFFFF) + (total >> 16)
    return (~total) & 0xFFFF


def _icmp_ping_socket(addr: str, ident: int, seq: int, timeout: float, use_dgram: bool) -> Tuple[bool, float, str]:
    """Ping ICMP avec socket Python; DGRAM est privilégié sur Linux quand permis."""
    sock = None
    try:
        sock_type = socket.SOCK_DGRAM if use_dgram else socket.SOCK_RAW
        sock = socket.socket(socket.AF_INET, sock_type, socket.IPPROTO_ICMP)
        sock.settimeout(timeout)
        payload = struct.pack(">d", time.time()) + b"miniOS-ping"
        header = struct.pack(">BBHHH", 8, 0, 0, ident, seq)
        checksum = _icmp_checksum(header + payload)
        packet = struct.pack(">BBHHH", 8, 0, checksum, ident, seq) + payload
        started = time.perf_counter()
        sock.sendto(packet, (addr, 1))
        while True:
            data, sender = sock.recvfrom(65535)
            # Linux SOCK_DGRAM ICMP peut livrer directement l'en-tête ICMP;
            # SOCK_RAW livre l'en-tête IPv4 puis l'en-tête ICMP.
            offsets = (0, (data[0] & 0x0F) * 4) if data else (0,)
            for offset in offsets:
                if len(data) < offset + 8:
                    continue
                try:
                    icmp_type, _code, _checksum, rid, rseq = struct.unpack(
                        ">BBHHH", data[offset:offset + 8]
                    )
                except struct.error:
                    continue
                if icmp_type == 0 and rid == ident and rseq == seq:
                    elapsed = (time.perf_counter() - started) * 1000.0
                    return True, elapsed, sender[0]
    except PermissionError:
        return False, 0.0, "permission ICMP insuffisante"
    except socket.timeout:
        return False, 0.0, "délai dépassé"
    except OSError as exc:
        return False, 0.0, str(exc)
    finally:
        if sock is not None:
            sock.close()
    return False, 0.0, "aucune réponse ICMP"


def _windows_icmp_ping(addr: str, ident: int, seq: int, timeout_ms: int) -> Tuple[bool, float, str]:
    """Ping Windows via l'API IP Helper directement, sans ping.exe."""
    if os.name != "nt":
        return False, 0.0, "API Windows indisponible"
    try:
        import ctypes
        from ctypes import wintypes
        iphlpapi = ctypes.WinDLL("iphlpapi.dll")
        IcmpCreateFile = iphlpapi.IcmpCreateFile
        IcmpCreateFile.restype = wintypes.HANDLE
        IcmpSendEcho = iphlpapi.IcmpSendEcho
        IcmpSendEcho.argtypes = [
            wintypes.HANDLE, wintypes.DWORD, ctypes.c_void_p, ctypes.c_ubyte,
            ctypes.c_void_p, ctypes.c_void_p, wintypes.DWORD, wintypes.DWORD
        ]
        IcmpSendEcho.restype = wintypes.DWORD
        IcmpCloseHandle = iphlpapi.IcmpCloseHandle
        IcmpCloseHandle.argtypes = [wintypes.HANDLE]
        IcmpCloseHandle.restype = wintypes.BOOL

        class IP_OPTION_INFORMATION(ctypes.Structure):
            _fields_ = [
                ("Ttl", ctypes.c_ubyte),
                ("Tos", ctypes.c_ubyte),
                ("Flags", ctypes.c_ubyte),
                ("OptionsSize", ctypes.c_ubyte),
                ("OptionsData", ctypes.c_void_p),
            ]

        class ICMP_ECHO_REPLY(ctypes.Structure):
            _fields_ = [
                ("Address", wintypes.DWORD),
                ("Status", wintypes.DWORD),
                ("RTT", wintypes.DWORD),
                ("DataSize", wintypes.WORD),
                ("Reserved", wintypes.WORD),
                ("Data", ctypes.c_void_p),
                ("Options", IP_OPTION_INFORMATION),
            ]

        handle = IcmpCreateFile()
        if handle == wintypes.HANDLE(-1).value:
            return False, 0.0, "IcmpCreateFile a échoué"
        try:
            import struct as _struct
            packed_addr = socket.inet_aton(addr)
            ip_u32 = _struct.unpack("!I", packed_addr)[0]
            payload = b"miniOS-ping"
            send_buf = ctypes.create_string_buffer(payload)
            reply_buf = ctypes.create_string_buffer(ctypes.sizeof(ICMP_ECHO_REPLY) + len(payload) + 64)
            started = time.perf_counter()
            reply_count = IcmpSendEcho(
                handle, ip_u32, ctypes.byref(send_buf), len(payload),
                None, ctypes.byref(reply_buf), ctypes.sizeof(reply_buf), timeout_ms
            )
            if reply_count:
                reply = ICMP_ECHO_REPLY.from_buffer(reply_buf)
                if reply.Status == 0:
                    return True, float(reply.RTT), addr
                return False, 0.0, f"statut ICMP Windows: {reply.Status}"
            return False, 0.0, "aucune réponse ICMP"
        finally:
            IcmpCloseHandle(handle)
    except Exception as exc:
        return False, 0.0, f"ICMP Windows indisponible: {exc}"


def _host_ping(target: str, timeout_ms: int = 2000) -> Tuple[bool, float, str]:
    """Ping ICMP sans lancer de programme externe."""
    target = target.strip()
    if not target:
        return False, 0.0, "hôte vide"
    try:
        addr = socket.gethostbyname(target)
    except OSError as exc:
        return False, 0.0, f"résolution impossible: {exc}"

    timeout = max(0.05, min(10.0, timeout_ms / 1000.0))
    ident = os.getpid() & 0xFFFF
    seq = int(time.time() * 1000) & 0xFFFF

    if os.name == "nt":
        ok, latency, detail = _windows_icmp_ping(addr, ident, seq, timeout_ms)
        if ok or "aucune réponse" in detail or "statut ICMP" in detail:
            return ok, latency, detail

    # Sous Linux, ICMP datagram est souvent utilisable sans privilèges spéciaux.
    ok, latency, detail = _icmp_ping_socket(addr, ident, seq, timeout, use_dgram=True)
    if ok:
        return ok, latency, detail
    # Dernier essai avec raw socket, lorsque le système autorise CAP_NET_RAW.
    ok2, latency2, detail2 = _icmp_ping_socket(addr, ident, seq, timeout, use_dgram=False)
    if ok2:
        return ok2, latency2, detail2
    return False, 0.0, detail2 if detail2 else detail


def _host_dns_resolve(host: str) -> List[str]:
    """Résout un nom ou une adresse via le résolveur socket Python."""
    seen: List[str] = []
    infos = socket.getaddrinfo(host, None, socket.AF_UNSPEC, socket.SOCK_STREAM)
    for info in infos:
        addr = info[4][0]
        if addr not in seen:
            seen.append(addr)
    return seen


def _linux_proc_net(kind: str) -> List[Dict[str, str]]:
    """Lit les sockets Linux depuis /proc, sans appeler netstat/ss."""
    path = f"/proc/net/{kind}"
    rows: List[Dict[str, str]] = []
    try:
        lines = Path(path).read_text(encoding="ascii", errors="replace").splitlines()[1:]
    except (OSError, NameError):
        return rows
    for line in lines:
        parts = line.split()
        if len(parts) < 4:
            continue
        local_hex, remote_hex, state = parts[1], parts[2], parts[3]
        def decode_ep(ep: str) -> str:
            host_hex, port_hex = ep.split(":")
            port = int(port_hex, 16)
            if kind.endswith("6"):
                try:
                    raw = bytes.fromhex(host_hex)
                    ip = socket.inet_ntop(socket.AF_INET6, raw)
                except Exception:
                    ip = "?"
            else:
                raw = bytes.fromhex(host_hex)
                ip = socket.inet_ntoa(raw[::-1])
            return f"{ip}:{port}"
        try:
            rows.append({"local": decode_ep(local_hex), "remote": decode_ep(remote_hex), "state": state})
        except Exception:
            continue
    return rows


def _network_netstat_rows() -> List[Dict[str, str]]:
    """Retourne les connexions TCP/UDP disponibles sans programme externe."""
    if os.path.exists("/proc/net/tcp"):
        rows = []
        state_names = {
            "01": "ESTABLISHED", "02": "SYN_SENT", "03": "SYN_RECV", "04": "FIN_WAIT1",
            "05": "FIN_WAIT2", "06": "TIME_WAIT", "07": "CLOSE", "08": "CLOSE_WAIT",
            "09": "LAST_ACK", "0A": "LISTEN", "0B": "CLOSING", "0C": "NEW_SYN_RECV",
        }
        for kind in ("tcp", "tcp6", "udp", "udp6"):
            for row in _linux_proc_net(kind):
                row["proto"] = "tcp" if kind.startswith("tcp") else "udp"
                row["state"] = state_names.get(row["state"], row["state"])
                rows.append(row)
        return rows
    return []


def _network_route_rows() -> List[str]:
    """Retourne une table de routage raisonnable sans exécuter route/ip."""
    rows: List[str] = []
    proc = "/proc/net/route"
    if os.path.exists(proc):
        try:
            lines = Path(proc).read_text(encoding="ascii", errors="replace").splitlines()[1:]
            rows.append("Iface\tDestination\tGateway\tMask\tFlags")
            for line in lines:
                parts = line.split()
                if len(parts) < 8:
                    continue
                iface, dest, gateway, flags, mask = parts[0], parts[1], parts[2], parts[3], parts[7]
                def ipv4(hexv: str) -> str:
                    raw = bytes.fromhex(hexv)
                    return socket.inet_ntoa(raw[::-1])
                try:
                    rows.append(f"{iface}\t{ipv4(dest)}\t{ipv4(gateway)}\t{ipv4(mask)}\t{flags}")
                except Exception:
                    rows.append(f"{iface}\t{dest}\t{gateway}\t{mask}\t{flags}")
        except OSError:
            pass
    if not rows:
        # Fallback multiplateforme basé uniquement sur les primitives socket.
        for addr in _network_local_addresses():
            rows.append(f"local\t{addr}")
    return rows


class Syscalls:
    # ABI MiniLang/VM32 : R1..R5 = arguments, R0 = valeur de retour.
    WRITE = 1
    EXIT = 2
    PRINT_INT = 3
    ALLOC = 4
    FREE = 5
    PRINT_STR = 6
    INPUT_STR = 7
    INPUT_INT = 8
    STR_LEN = 9
    STR_CONCAT = 10
    STR_EQ = 11
    STR_TO_INT = 12
    INT_TO_STR = 13
    SYSTEM_GET = 14
    ENV_GET = 15
    ENV_SET = 16
    FILE_READ = 17
    FILE_WRITE = 18
    FILE_APPEND = 19
    FILE_EXISTS = 20
    FILE_ISDIR = 21
    MKDIR = 22
    FILE_DELETE = 23
    FILE_COPY = 24
    FILE_MOVE = 25
    SHELL = 26
    RUN = 27
    SLEEP = 28
    TIME = 29
    TIME_MS = 30
    RANDOM = 31
    RANDOM_RANGE = 32
    ARGC = 33
    ARG = 34
    CWD = 35
    CHDIR = 36
    LIST = 37
    ARRAY_NEW = 38
    ARRAY_LEN = 39
    ARRAY_GET = 40
    ARRAY_SET = 41
    READ_MEM8 = 42
    READ_MEM32 = 43
    WRITE_MEM8 = 44
    WRITE_MEM32 = 45
    FILE_SIZE = 46
    FILE_READ_BYTE = 47
    FILE_WRITE_BYTE = 48
    STR_SUBSTR = 49
    STR_REPLACE = 50
    STR_CONTAINS = 51
    STR_STARTS = 52
    STR_ENDS = 53
    STR_LOWER = 54
    STR_UPPER = 55
    STR_TRIM = 56
    CHR = 57
    ORD = 58
    NET_PING = 59
    PID = 60
    PROGRAM = 61
    HOSTNAME = 62
    MEM_TOTAL = 63
    MEM_FREE = 64
    STR_CHAR = 65
    ARRAY_GET_STR = 66
    IMPORT_HOST = 67
    EXPORT_HOST = 68
    HOST_EXISTS = 69
    EXEC_CAPTURE = 70
    HOST_READ = 71
    HOST_WRITE = 72
    HOST_APPEND = 73
    HOST_DELETE = 74
    HOST_MKDIR = 75
    HOST_LIST = 76
    HOST_ISDIR = 77
    HOST_SIZE = 78
    ARRAY_SET_STR = 79
    STR_SPLIT = 80
    STR_JOIN = 81
    GFX_WINDOW = 82
    GFX_CLEAR = 83
    GFX_PIXEL = 84
    GFX_RECT = 85
    GFX_LINE = 86
    GFX_CIRCLE = 87
    GFX_TEXT = 88
    GFX_PRESENT = 89
    GFX_CLOSE = 90
    GFX_MINIMIZE = 116
    GFX_KEY_DOWN = 91
    GFX_KEY_PRESSED = 117
    GFX_TEXT_INPUT = 118
    GFX_MOUSE_X = 92
    GFX_MOUSE_Y = 93
    GFX_MOUSE_DOWN = 94
    GFX_CLOSE_REQUESTED = 95
    GFX_ALIVE = 96
    GFX_RGB = 97
    PRINT_STR_END = 98
    VALUE_PRINT = 99
    VALUE_TO_STR = 100
    VALUE_ADD = 101
    VALUE_EQ = 102
    HTTP_GET = 103
    HTTP_POST = 104
    HTTP_DOWNLOAD = 105
    DNS_RESOLVE = 106
    TCP_CONNECT = 107
    TCP_SEND = 108
    TCP_RECV = 109
    TCP_CLOSE = 110
    TCP_IS_OPEN = 111
    UDP_OPEN = 112
    UDP_SEND = 113
    UDP_RECV = 114
    UDP_CLOSE = 115
    GFX_IMAGE_LOAD = 119
    GFX_IMAGE_DRAW = 120
    GFX_IMAGE_DRAW_SCALED = 121
    GFX_IMAGE_WIDTH = 122
    GFX_IMAGE_HEIGHT = 123
    GFX_IMAGE_FREE = 124

    @staticmethod
    def _require_os(cpu):
        os_ref = getattr(cpu, "os_ref", None)
        if os_ref is None:
            raise RuntimeError("runtime miniOS indisponible")
        return os_ref

    @staticmethod
    def _read_cstring(cpu, ptr: int) -> str:
        ptr = int(ptr)
        if ptr < 0 or ptr >= len(cpu.memory):
            raise RuntimeError(f"pointeur chaîne invalide: 0x{ptr:08X}")
        end = ptr
        while end < len(cpu.memory) and cpu.memory[end] != 0:
            end += 1
        if end >= len(cpu.memory):
            raise RuntimeError("chaîne VM32 non terminée")
        return bytes(cpu.memory[ptr:end]).decode("utf-8", errors="replace")

    @staticmethod
    def _is_string_value(cpu, value: int) -> bool:
        try:
            ptr = int(value) & WORD_MASK
        except Exception:
            return False
        if ptr <= 0 or ptr >= len(cpu.memory):
            return False
        if getattr(cpu, "data_start", 0) <= ptr < getattr(cpu, "data_end", 0):
            try:
                Syscalls._read_cstring(cpu, ptr)
                return True
            except Exception:
                return False
        mm = getattr(cpu, "memory_manager", None)
        if mm is not None and mm.kinds.get(ptr) == "string":
            try:
                Syscalls._read_cstring(cpu, ptr)
                return True
            except Exception:
                return False
        return False

    @staticmethod
    def _value_to_text(cpu, value: int) -> str:
        return Syscalls._read_cstring(cpu, value) if Syscalls._is_string_value(cpu, value) else str(s32(value))

    @staticmethod
    def _write_cstring(cpu, value: Any) -> int:
        text_value = str(value)
        raw = text_value.encode("utf-8") + b"\x00"
        ptr = getattr(cpu, "memory_manager").alloc(len(raw), kind="string", gc_cpu=cpu)
        if ptr + len(raw) > len(cpu.memory):
            raise MemoryError("mémoire VM32 insuffisante pour la chaîne")
        cpu.memory[ptr:ptr + len(raw)] = raw
        return ptr

    @staticmethod
    def _path(cpu, value: Any) -> str:
        os_ref = Syscalls._require_os(cpu)
        process = getattr(cpu, "process", None)
        cwd = getattr(process, "cwd", os_ref.cwd) if process else os_ref.cwd
        return os_ref.resolve(str(value), cwd)

    @staticmethod
    def _text_file(cpu, path: str) -> str:
        os_ref = Syscalls._require_os(cpu)
        data = os_ref.disk.read(path)
        if isinstance(data, bytes):
            return decode_text_bytes(data)
        return str(data)

    @staticmethod
    def _network_timeout(cpu, reg: int, default: float = 15.0) -> float:
        raw = s32(cpu.reg[reg])
        if raw <= 0:
            return default
        return min(float(raw), 120.0)

    @staticmethod
    def _http_get(url: str, timeout: float) -> Tuple[int, Dict[str, str], bytes]:
        req = urllib.request.Request(
            url,
            headers={
                "User-Agent": "miniOS/0.5",
                "Accept": "*/*",
            },
            method="GET",
        )
        with urllib.request.urlopen(req, timeout=timeout) as response:
            status = int(getattr(response, "status", 200))
            headers = {k.lower(): v for k, v in response.headers.items()}
            body = response.read()
        return status, headers, body

    @staticmethod
    def _http_post(url: str, body: bytes, content_type: str, timeout: float) -> Tuple[int, Dict[str, str], bytes]:
        req = urllib.request.Request(
            url,
            data=body,
            headers={
                "User-Agent": "miniOS/0.5",
                "Accept": "*/*",
                "Content-Type": content_type or "text/plain; charset=utf-8",
            },
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=timeout) as response:
            status = int(getattr(response, "status", 200))
            headers = {k.lower(): v for k, v in response.headers.items()}
            result = response.read()
        return status, headers, result

    @staticmethod
    def _http_error(exc: Exception, url: str) -> RuntimeError:
        if isinstance(exc, urllib.error.HTTPError):
            return RuntimeError(f"HTTP {exc.code} pour {url}")
        if isinstance(exc, urllib.error.URLError):
            reason = getattr(exc, "reason", exc)
            return RuntimeError(f"connexion impossible vers {url}: {reason}")
        return RuntimeError(f"erreur réseau pour {url}: {exc}")

    @staticmethod
    def handle(cpu: CPU, num: int):
        if num == Syscalls.WRITE:
            ptr, length = cpu.reg[0], cpu.reg[1]
            if ptr + length > len(cpu.memory):
                raise RuntimeError("WRITE invalide")
            data = bytes(cpu.memory[ptr:ptr + length])
            sys.stdout.write(data.decode("utf-8", errors="replace")); sys.stdout.flush()
        elif num == Syscalls.EXIT:
            cpu.exit_code = s32(cpu.reg[0]); cpu.halted = True
        elif num == Syscalls.PRINT_INT:
            print(s32(cpu.reg[0]))
        elif num == Syscalls.ALLOC:
            ptr = getattr(cpu, "memory_manager").alloc(cpu.reg[0])
            cpu.reg[0] = ptr
        elif num == Syscalls.FREE:
            # FREE ne prend qu'un pointeur en entrée (R0) mais doit aussi
            # définir explicitement sa valeur de retour. Sinon R0 conserve
            # l'adresse libérée, ce qui peut faire apparaître un handle
            # mémoire (ex: 1048576) comme résultat de free()/sysf("free", ...).
            freed = getattr(cpu, "memory_manager").free(cpu.reg[0])
            # Convention MiniLang : 0 = succès, valeur non nulle = erreur.
            cpu.reg[0] = 0 if freed else 1
        elif num == Syscalls.PRINT_STR:
            sys.stdout.write(Syscalls._read_cstring(cpu, cpu.reg[0])); sys.stdout.flush()
            sys.stdout.write("\n")
        elif num == Syscalls.PRINT_STR_END:
            # R0 = valeur chaîne, R1 = fin de ligne personnalisée.
            sys.stdout.write(Syscalls._read_cstring(cpu, cpu.reg[0]))
            sys.stdout.write(Syscalls._read_cstring(cpu, cpu.reg[1]))
            sys.stdout.flush()
        elif num == Syscalls.VALUE_PRINT:
            sys.stdout.write(Syscalls._value_to_text(cpu, cpu.reg[0]))
            sys.stdout.write("\n")
            sys.stdout.flush()
        elif num == Syscalls.VALUE_TO_STR:
            value = cpu.reg[0]
            cpu.reg[0] = value if Syscalls._is_string_value(cpu, value) else Syscalls._write_cstring(cpu, str(s32(value)))
        elif num == Syscalls.VALUE_ADD:
            a, b = cpu.reg[1], cpu.reg[2]
            if Syscalls._is_string_value(cpu, a) or Syscalls._is_string_value(cpu, b):
                cpu.reg[0] = Syscalls._write_cstring(cpu, Syscalls._value_to_text(cpu, a) + Syscalls._value_to_text(cpu, b))
            else:
                cpu.reg[0] = (s32(a) + s32(b)) & WORD_MASK
        elif num == Syscalls.VALUE_EQ:
            a, b = cpu.reg[1], cpu.reg[2]
            if Syscalls._is_string_value(cpu, a) or Syscalls._is_string_value(cpu, b):
                cpu.reg[0] = int(Syscalls._value_to_text(cpu, a) == Syscalls._value_to_text(cpu, b))
            else:
                cpu.reg[0] = int(s32(a) == s32(b))
        elif num == Syscalls.INPUT_STR:
            prompt = "" if cpu.reg[1] == 0 else Syscalls._read_cstring(cpu, cpu.reg[1])
            process = getattr(cpu, "process", None)
            os_ref = Syscalls._require_os(cpu)
            if process: process.state = "WAITING_INPUT"
            try:
                if process is not None and process.stdin_pipe:
                    available, answer = process.read_stdin_line()
                    if not available:
                        raise RuntimeError("entrée standard terminée (EOF)")
                else:
                    with os_ref.console_input_lock:
                        if process and process.stop_event.is_set():
                            raise RuntimeError("processus arrêté pendant la saisie")
                        answer = input(prompt)
                cpu.reg[0] = Syscalls._write_cstring(cpu, answer)
            finally:
                if process and process.state == "WAITING_INPUT":
                    process.state = "RUNNING"
        elif num == Syscalls.INPUT_INT:
            prompt = "" if cpu.reg[1] == 0 else Syscalls._read_cstring(cpu, cpu.reg[1])
            process = getattr(cpu, "process", None)
            os_ref = Syscalls._require_os(cpu)
            if process: process.state = "WAITING_INPUT"
            try:
                if process is not None and process.stdin_pipe:
                    while True:
                        if process.stop_event.is_set():
                            raise RuntimeError("processus arrêté pendant la saisie")
                        available, value_text = process.read_stdin_line()
                        if not available:
                            raise RuntimeError("entrée standard terminée (EOF)")
                        try:
                            cpu.reg[0] = int(value_text.strip(), 0)
                            break
                        except ValueError:
                            print("Valeur invalide: entrez un entier.")
                else:
                    with os_ref.console_input_lock:
                        while True:
                            if process and process.stop_event.is_set():
                                raise RuntimeError("processus arrêté pendant la saisie")
                            try:
                                value = input(prompt); cpu.reg[0] = int(value, 0); break
                            except ValueError:
                                print("Valeur invalide: entrez un entier.")
            finally:
                if process and process.state == "WAITING_INPUT":
                    process.state = "RUNNING"
        elif num == Syscalls.STR_LEN:
            cpu.reg[0] = len(Syscalls._read_cstring(cpu, cpu.reg[1]))
        elif num == Syscalls.STR_CONCAT:
            a = Syscalls._read_cstring(cpu, cpu.reg[1]); b = Syscalls._read_cstring(cpu, cpu.reg[2])
            cpu.reg[0] = Syscalls._write_cstring(cpu, a + b)
        elif num == Syscalls.STR_EQ:
            a = Syscalls._read_cstring(cpu, cpu.reg[1]); b = Syscalls._read_cstring(cpu, cpu.reg[2])
            cpu.reg[0] = 1 if a == b else 0
        elif num == Syscalls.STR_TO_INT:
            raw = Syscalls._read_cstring(cpu, cpu.reg[1]).strip()
            try: cpu.reg[0] = int(raw, 0)
            except ValueError: raise RuntimeError(f"conversion en entier impossible: {raw!r}")
        elif num == Syscalls.INT_TO_STR:
            cpu.reg[0] = Syscalls._write_cstring(cpu, str(s32(cpu.reg[1])))
        elif num == Syscalls.SYSTEM_GET:
            os_ref = Syscalls._require_os(cpu); key = Syscalls._read_cstring(cpu, cpu.reg[1]).lower()
            process = getattr(cpu, "process", None)
            cwd = getattr(process, "cwd", os_ref.cwd) if process else os_ref.cwd
            values = {
                "os.name": "miniOS", "os.version": VERSION, "os.arch": "VM32",
                "user.name": "user", "user.home": "/home/user", "user.dir": cwd,
                "hostname": HOSTNAME, "memory.size": str(len(cpu.memory)),
                "memory.unit": "bytes", "memory.free": str(max(0, len(cpu.memory) - getattr(cpu.memory_manager, 'used', 0))),
                "path": os_ref.env.get("PATH", ""), "shell": "minios-shell",
                "jvm.version": "miniOS-JVM", "minios.version": VERSION,
                "pid": str(getattr(process, "pid", 0)), "program": getattr(process, "name", "program"),
            }
            cpu.reg[0] = Syscalls._write_cstring(cpu, values.get(key, ""))
        elif num == Syscalls.ENV_GET:
            os_ref = Syscalls._require_os(cpu); key = Syscalls._read_cstring(cpu, cpu.reg[1])
            cpu.reg[0] = Syscalls._write_cstring(cpu, os_ref.env.get(key, ""))
        elif num == Syscalls.ENV_SET:
            os_ref = Syscalls._require_os(cpu); key = Syscalls._read_cstring(cpu, cpu.reg[1]); value = Syscalls._read_cstring(cpu, cpu.reg[2])
            os_ref.env[key] = value; cpu.reg[0] = 0
        elif num in (Syscalls.FILE_READ, Syscalls.FILE_WRITE, Syscalls.FILE_APPEND, Syscalls.FILE_EXISTS, Syscalls.FILE_ISDIR, Syscalls.MKDIR, Syscalls.FILE_DELETE, Syscalls.FILE_COPY, Syscalls.FILE_MOVE, Syscalls.FILE_SIZE, Syscalls.FILE_READ_BYTE, Syscalls.FILE_WRITE_BYTE):
            os_ref = Syscalls._require_os(cpu)
            if num == Syscalls.FILE_READ:
                p = Syscalls._path(cpu, Syscalls._read_cstring(cpu, cpu.reg[1])); cpu.reg[0] = Syscalls._write_cstring(cpu, Syscalls._text_file(cpu, p))
            elif num == Syscalls.FILE_WRITE:
                p = Syscalls._path(cpu, Syscalls._read_cstring(cpu, cpu.reg[1])); v = Syscalls._read_cstring(cpu, cpu.reg[2]); os_ref.disk.write(p, v); cpu.reg[0] = 0
            elif num == Syscalls.FILE_APPEND:
                p = Syscalls._path(cpu, Syscalls._read_cstring(cpu, cpu.reg[1])); v = Syscalls._read_cstring(cpu, cpu.reg[2]); os_ref.disk.append(p, v); cpu.reg[0] = 0
            elif num == Syscalls.FILE_EXISTS:
                cpu.reg[0] = 1 if os_ref.disk.exists(Syscalls._path(cpu, Syscalls._read_cstring(cpu, cpu.reg[1]))) else 0
            elif num == Syscalls.FILE_ISDIR:
                cpu.reg[0] = 1 if os_ref.disk.is_dir(Syscalls._path(cpu, Syscalls._read_cstring(cpu, cpu.reg[1]))) else 0
            elif num == Syscalls.MKDIR:
                p = Syscalls._path(cpu, Syscalls._read_cstring(cpu, cpu.reg[1])); recursive = bool(cpu.reg[2]) if cpu.reg[2] else False; os_ref.disk.mkdir(p, parents=recursive); cpu.reg[0] = 0
            elif num == Syscalls.FILE_DELETE:
                p = Syscalls._path(cpu, Syscalls._read_cstring(cpu, cpu.reg[1])); os_ref.disk.delete(p, recursive=bool(cpu.reg[2])); cpu.reg[0] = 0
            elif num == Syscalls.FILE_COPY:
                os_ref.disk.copy(Syscalls._path(cpu, Syscalls._read_cstring(cpu, cpu.reg[1])), Syscalls._path(cpu, Syscalls._read_cstring(cpu, cpu.reg[2]))); cpu.reg[0] = 0
            elif num == Syscalls.FILE_MOVE:
                os_ref.disk.move(Syscalls._path(cpu, Syscalls._read_cstring(cpu, cpu.reg[1])), Syscalls._path(cpu, Syscalls._read_cstring(cpu, cpu.reg[2]))); cpu.reg[0] = 0
            elif num == Syscalls.FILE_SIZE:
                p = Syscalls._path(cpu, Syscalls._read_cstring(cpu, cpu.reg[1])); data = os_ref.disk.read(p); cpu.reg[0] = len(data) if isinstance(data, bytes) else len(str(data).encode())
            elif num == Syscalls.FILE_READ_BYTE:
                p = Syscalls._path(cpu, Syscalls._read_cstring(cpu, cpu.reg[1])); idx = int(cpu.reg[2]); data = os_ref.disk.read(p); raw = data if isinstance(data, bytes) else str(data).encode(); cpu.reg[0] = raw[idx] if 0 <= idx < len(raw) else -1
            elif num == Syscalls.FILE_WRITE_BYTE:
                p = Syscalls._path(cpu, Syscalls._read_cstring(cpu, cpu.reg[1])); idx = int(cpu.reg[2]); val = int(cpu.reg[3]) & 0xFF; data = os_ref.disk.read(p); raw = bytearray(data if isinstance(data, bytes) else str(data).encode());
                if idx < 0: raise RuntimeError("index de fichier négatif")
                if idx >= len(raw): raw.extend(b"\x00" * (idx + 1 - len(raw)))
                raw[idx] = val; os_ref.disk.write(p, bytes(raw)); cpu.reg[0] = 0
        elif num == Syscalls.SHELL:
            os_ref = Syscalls._require_os(cpu); command = Syscalls._read_cstring(cpu, cpu.reg[1]); process = getattr(cpu, "process", None)
            old_cwd = os_ref.cwd
            try:
                if process: os_ref.cwd = process.cwd
                os_ref.execute(command)
            finally:
                os_ref.cwd = old_cwd
            cpu.reg[0] = 0
        elif num == Syscalls.RUN:
            os_ref = Syscalls._require_os(cpu); target = Syscalls._read_cstring(cpu, cpu.reg[1]); extras = []
            for reg in range(2, 6):
                if cpu.reg[reg]: extras.append(Syscalls._read_cstring(cpu, cpu.reg[reg]))
            process = getattr(cpu, "process", None); path = os_ref.search_path(target, getattr(process, "cwd", os_ref.cwd))
            if not path: raise FileNotFoundError(f"programme introuvable: {target}")
            cpu.reg[0] = int(os_ref._run_virtual_mexe(path, quiet=False, args=extras))
        elif num == Syscalls.SLEEP:
            process = getattr(cpu, "process", None)
            delay = max(0, int(cpu.reg[1])) / 1000.0
            if process:
                process.state = "SLEEPING"
                process.stop_event.wait(delay)
                if process.stop_event.is_set():
                    cpu.halted = True
                    return
                process.state = "RUNNING"
            else:
                time.sleep(delay)
            cpu.reg[0] = 0
        elif num == Syscalls.TIME:
            cpu.reg[0] = int(time.time())
        elif num == Syscalls.TIME_MS:
            cpu.reg[0] = int(time.time() * 1000) & WORD_MASK
        elif num == Syscalls.RANDOM:
            import random; n = max(1, int(cpu.reg[1])); cpu.reg[0] = random.randrange(n)
        elif num == Syscalls.RANDOM_RANGE:
            import random; a, b = s32(cpu.reg[1]), s32(cpu.reg[2]); cpu.reg[0] = random.randint(a, b)
        elif num == Syscalls.ARGC:
            cpu.reg[0] = len(getattr(cpu, "argv", []))
        elif num == Syscalls.ARG:
            idx = s32(cpu.reg[1]); argv = getattr(cpu, "argv", []); cpu.reg[0] = Syscalls._write_cstring(cpu, argv[idx] if 0 <= idx < len(argv) else "")
        elif num == Syscalls.CWD:
            process = getattr(cpu, "process", None); os_ref = Syscalls._require_os(cpu); cpu.reg[0] = Syscalls._write_cstring(cpu, getattr(process, "cwd", os_ref.cwd))
        elif num == Syscalls.CHDIR:
            process = getattr(cpu, "process", None); os_ref = Syscalls._require_os(cpu); p = Syscalls._path(cpu, Syscalls._read_cstring(cpu, cpu.reg[1]));
            if not os_ref.disk.is_dir(p): raise NotADirectoryError(p)
            if process: process.cwd = p
            cpu.reg[0] = 0
        elif num == Syscalls.LIST:
            os_ref = Syscalls._require_os(cpu); p = Syscalls._path(cpu, Syscalls._read_cstring(cpu, cpu.reg[1])); items = os_ref.disk.ls(p, getattr(getattr(cpu, "process", None), "cwd", os_ref.cwd)); text_value = "\n".join(name + ("/" if isdir else "") for name, isdir in items); cpu.reg[0] = Syscalls._write_cstring(cpu, text_value)
        elif num == Syscalls.ARRAY_NEW:
            n = max(0, int(cpu.reg[1])); ptr = getattr(cpu, "memory_manager").alloc((n + 1) * 4, kind="refs", gc_cpu=cpu); cpu.write32(ptr, n);
            for i in range(n): cpu.write32(ptr + 4 + i * 4, 0)
            cpu.reg[0] = ptr
        elif num == Syscalls.ARRAY_LEN:
            ptr = int(cpu.reg[1]); cpu.reg[0] = cpu.read32(ptr)
        elif num == Syscalls.ARRAY_GET:
            ptr, idx = int(cpu.reg[1]), s32(cpu.reg[2]); ln = cpu.read32(ptr);
            if idx < 0 or idx >= ln: raise IndexError("index de tableau hors limites")
            cpu.reg[0] = cpu.read32(ptr + 4 + idx * 4)
        elif num == Syscalls.ARRAY_GET_STR:
            ptr, idx = int(cpu.reg[1]), s32(cpu.reg[2]); ln = cpu.read32(ptr);
            if idx < 0 or idx >= ln: raise IndexError("index de tableau hors limites")
            value_ptr = cpu.read32(ptr + 4 + idx * 4)
            # Vérification minimale : la cellule doit pointer vers une chaîne C valide.
            Syscalls._read_cstring(cpu, value_ptr)
            cpu.reg[0] = value_ptr
        elif num == Syscalls.ARRAY_SET:
            ptr, idx, val = int(cpu.reg[1]), s32(cpu.reg[2]), cpu.reg[3]; ln = cpu.read32(ptr);
            if idx < 0 or idx >= ln: raise IndexError("index de tableau hors limites")
            cpu.write32(ptr + 4 + idx * 4, val); cpu.reg[0] = val
        elif num in (Syscalls.READ_MEM8, Syscalls.READ_MEM32, Syscalls.WRITE_MEM8, Syscalls.WRITE_MEM32):
            addr = int(cpu.reg[1]);
            if num == Syscalls.READ_MEM8: cpu.reg[0] = cpu.memory[addr]
            elif num == Syscalls.READ_MEM32: cpu.reg[0] = cpu.read32(addr)
            elif num == Syscalls.WRITE_MEM8: cpu.memory[addr] = cpu.reg[2] & 0xFF; cpu.reg[0] = cpu.reg[2] & 0xFF
            else: cpu.write32(addr, cpu.reg[2]); cpu.reg[0] = cpu.reg[2]
        elif num in (Syscalls.STR_SUBSTR, Syscalls.STR_REPLACE, Syscalls.STR_CONTAINS, Syscalls.STR_STARTS, Syscalls.STR_ENDS, Syscalls.STR_LOWER, Syscalls.STR_UPPER, Syscalls.STR_TRIM, Syscalls.CHR, Syscalls.ORD, Syscalls.STR_CHAR):
            if num == Syscalls.STR_SUBSTR:
                text_value = Syscalls._read_cstring(cpu, cpu.reg[1]); start = max(0, s32(cpu.reg[2])); ln = s32(cpu.reg[3]); cpu.reg[0] = Syscalls._write_cstring(cpu, text_value[start:] if ln < 0 else text_value[start:start + ln])
            elif num == Syscalls.STR_REPLACE:
                a = Syscalls._read_cstring(cpu, cpu.reg[1]); b = Syscalls._read_cstring(cpu, cpu.reg[2]); c = Syscalls._read_cstring(cpu, cpu.reg[3]); cpu.reg[0] = Syscalls._write_cstring(cpu, a.replace(b, c))
            elif num == Syscalls.STR_CONTAINS:
                a = Syscalls._read_cstring(cpu, cpu.reg[1]); b = Syscalls._read_cstring(cpu, cpu.reg[2]); cpu.reg[0] = int(b in a)
            elif num == Syscalls.STR_STARTS:
                a = Syscalls._read_cstring(cpu, cpu.reg[1]); b = Syscalls._read_cstring(cpu, cpu.reg[2]); cpu.reg[0] = int(a.startswith(b))
            elif num == Syscalls.STR_ENDS:
                a = Syscalls._read_cstring(cpu, cpu.reg[1]); b = Syscalls._read_cstring(cpu, cpu.reg[2]); cpu.reg[0] = int(a.endswith(b))
            elif num == Syscalls.STR_LOWER: cpu.reg[0] = Syscalls._write_cstring(cpu, Syscalls._read_cstring(cpu, cpu.reg[1]).lower())
            elif num == Syscalls.STR_UPPER: cpu.reg[0] = Syscalls._write_cstring(cpu, Syscalls._read_cstring(cpu, cpu.reg[1]).upper())
            elif num == Syscalls.STR_TRIM: cpu.reg[0] = Syscalls._write_cstring(cpu, Syscalls._read_cstring(cpu, cpu.reg[1]).strip())
            elif num == Syscalls.CHR: cpu.reg[0] = Syscalls._write_cstring(cpu, chr(s32(cpu.reg[1]) & 0x10FFFF))
            elif num == Syscalls.ORD:
                text_value = Syscalls._read_cstring(cpu, cpu.reg[1]); cpu.reg[0] = ord(text_value[0]) if text_value else -1
            elif num == Syscalls.STR_CHAR:
                text_value = Syscalls._read_cstring(cpu, cpu.reg[1]); idx = s32(cpu.reg[2])
                if idx < 0 or idx >= len(text_value): raise IndexError("index de chaîne hors limites")
                cpu.reg[0] = Syscalls._write_cstring(cpu, text_value[idx])
        elif num == Syscalls.HTTP_GET:
            url = Syscalls._read_cstring(cpu, cpu.reg[1]).strip()
            timeout = Syscalls._network_timeout(cpu, 2)
            if not url.lower().startswith(("http://", "https://")):
                raise RuntimeError("httpGet() accepte uniquement http:// ou https://")
            try:
                _status, _headers, body = Syscalls._http_get(url, timeout)
            except Exception as exc:
                raise Syscalls._http_error(exc, url) from exc
            # Les chaînes VM32 sont UTF-8 ; cette primitive est destinée au
            # contenu texte. Les octets invalides sont remplacés.
            if len(body) > 4 * 1024 * 1024:
                raise MemoryError("réponse HTTP trop grande pour httpGet() (maximum 4 MiB)")
            cpu.reg[0] = Syscalls._write_cstring(cpu, body.decode("utf-8", errors="replace"))
        elif num == Syscalls.HTTP_POST:
            url = Syscalls._read_cstring(cpu, cpu.reg[1]).strip()
            body = Syscalls._read_cstring(cpu, cpu.reg[2]).encode("utf-8")
            content_type = Syscalls._read_cstring(cpu, cpu.reg[3]) if cpu.reg[3] else "text/plain; charset=utf-8"
            timeout = Syscalls._network_timeout(cpu, 4)
            if not url.lower().startswith(("http://", "https://")):
                raise RuntimeError("httpPost() accepte uniquement http:// ou https://")
            try:
                _status, _headers, response_body = Syscalls._http_post(url, body, content_type, timeout)
            except Exception as exc:
                raise Syscalls._http_error(exc, url) from exc
            if len(response_body) > 4 * 1024 * 1024:
                raise MemoryError("réponse HTTP trop grande pour httpPost() (maximum 4 MiB)")
            cpu.reg[0] = Syscalls._write_cstring(cpu, response_body.decode("utf-8", errors="replace"))
        elif num == Syscalls.HTTP_DOWNLOAD:
            url = Syscalls._read_cstring(cpu, cpu.reg[1]).strip()
            timeout = Syscalls._network_timeout(cpu, 3)
            os_ref = Syscalls._require_os(cpu)
            path = Syscalls._path(cpu, Syscalls._read_cstring(cpu, cpu.reg[2]))
            if not url.lower().startswith(("http://", "https://")):
                raise RuntimeError("httpDownload() accepte uniquement http:// ou https://")
            try:
                _status, _headers, body = Syscalls._http_get(url, timeout)
            except Exception as exc:
                raise Syscalls._http_error(exc, url) from exc
            if len(body) > 8 * 1024 * 1024:
                raise MemoryError("téléchargement trop grand pour httpDownload() (maximum 8 MiB)")
            os_ref.disk.write(path, body)
            cpu.reg[0] = len(body)
        elif num == Syscalls.DNS_RESOLVE:
            host = Syscalls._read_cstring(cpu, cpu.reg[1]).strip()
            if not host:
                raise RuntimeError("dnsResolve() attend un hôte")
            try:
                address = socket.gethostbyname(host)
            except OSError as exc:
                raise RuntimeError(f"résolution DNS impossible pour {host}: {exc}") from exc
            cpu.reg[0] = Syscalls._write_cstring(cpu, address)
        elif num == Syscalls.TCP_CONNECT:
            pid = int(getattr(getattr(cpu, "process", None), "pid", 0))
            host = Syscalls._read_cstring(cpu, cpu.reg[1]).strip()
            port = s32(cpu.reg[2])
            timeout = Syscalls._network_timeout(cpu, 3)
            if not host:
                raise RuntimeError("tcpConnect() attend un hôte")
            if not (1 <= port <= 65535):
                raise ValueError("port TCP invalide (1..65535)")
            sock = socket.create_connection((host, port), timeout=timeout)
            sock.settimeout(None)
            cpu.reg[0] = NETWORK_SOCKETS.open(pid, sock, "tcp")
        elif num == Syscalls.TCP_SEND:
            pid = int(getattr(getattr(cpu, "process", None), "pid", 0))
            handle = s32(cpu.reg[1])
            text_value = Syscalls._read_cstring(cpu, cpu.reg[2])
            sock = NETWORK_SOCKETS.get(pid, handle, "tcp")
            raw = text_value.encode("utf-8")
            sock.sendall(raw)
            cpu.reg[0] = len(raw)
        elif num == Syscalls.TCP_RECV:
            pid = int(getattr(getattr(cpu, "process", None), "pid", 0))
            handle = s32(cpu.reg[1])
            max_bytes = s32(cpu.reg[2]) if s32(cpu.reg[2]) > 0 else 4096
            timeout = Syscalls._network_timeout(cpu, 3, default=15.0)
            max_bytes = min(max_bytes, 4 * 1024 * 1024)
            sock = NETWORK_SOCKETS.get(pid, handle, "tcp")
            sock.settimeout(timeout)
            try:
                data = sock.recv(max_bytes)
            except socket.timeout:
                data = b""
            finally:
                sock.settimeout(None)
            cpu.reg[0] = Syscalls._write_cstring(cpu, data.decode("utf-8", errors="replace"))
        elif num == Syscalls.TCP_CLOSE:
            pid = int(getattr(getattr(cpu, "process", None), "pid", 0))
            cpu.reg[0] = 0 if NETWORK_SOCKETS.close(pid, s32(cpu.reg[1])) else 1
        elif num == Syscalls.TCP_IS_OPEN:
            pid = int(getattr(getattr(cpu, "process", None), "pid", 0))
            try:
                NETWORK_SOCKETS.get(pid, s32(cpu.reg[1]), "tcp")
                cpu.reg[0] = 1
            except Exception:
                cpu.reg[0] = 0
        elif num == Syscalls.UDP_OPEN:
            pid = int(getattr(getattr(cpu, "process", None), "pid", 0))
            sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            cpu.reg[0] = NETWORK_SOCKETS.open(pid, sock, "udp")
        elif num == Syscalls.UDP_SEND:
            pid = int(getattr(getattr(cpu, "process", None), "pid", 0))
            handle = s32(cpu.reg[1])
            host = Syscalls._read_cstring(cpu, cpu.reg[2]).strip()
            port = s32(cpu.reg[3])
            text_value = Syscalls._read_cstring(cpu, cpu.reg[4])
            if not (1 <= port <= 65535):
                raise ValueError("port UDP invalide (1..65535)")
            sock = NETWORK_SOCKETS.get(pid, handle, "udp")
            raw = text_value.encode("utf-8")
            cpu.reg[0] = sock.sendto(raw, (host, port))
        elif num == Syscalls.UDP_RECV:
            pid = int(getattr(getattr(cpu, "process", None), "pid", 0))
            handle = s32(cpu.reg[1])
            max_bytes = s32(cpu.reg[2]) if s32(cpu.reg[2]) > 0 else 4096
            timeout = Syscalls._network_timeout(cpu, 3, default=15.0)
            max_bytes = min(max_bytes, 4 * 1024 * 1024)
            sock = NETWORK_SOCKETS.get(pid, handle, "udp")
            sock.settimeout(timeout)
            try:
                data, _addr = sock.recvfrom(max_bytes)
            except socket.timeout:
                data = b""
            finally:
                sock.settimeout(None)
            cpu.reg[0] = Syscalls._write_cstring(cpu, data.decode("utf-8", errors="replace"))
        elif num == Syscalls.UDP_CLOSE:
            pid = int(getattr(getattr(cpu, "process", None), "pid", 0))
            cpu.reg[0] = 0 if NETWORK_SOCKETS.close(pid, s32(cpu.reg[1])) else 1
        elif num == Syscalls.IMPORT_HOST:
            os_ref = Syscalls._require_os(cpu); host = Syscalls._read_cstring(cpu, cpu.reg[1]); host = os_ref.resolve_host_path(host)
            if not os.path.isfile(host): raise FileNotFoundError(host)
            v = Syscalls._read_cstring(cpu, cpu.reg[2]); cwd = getattr(getattr(cpu, "process", None), "cwd", os_ref.cwd); vp = os_ref.resolve(v, cwd)
            if os_ref.disk.is_dir(vp): vp = vp.rstrip("/") + "/" + os.path.basename(host)
            with open(host, "rb") as f: raw = f.read()
            raw, _ = maybe_decode_rtf(raw); os_ref.disk.write(vp, raw); cpu.reg[0] = 0
        elif num == Syscalls.EXPORT_HOST:
            os_ref = Syscalls._require_os(cpu); v = Syscalls._read_cstring(cpu, cpu.reg[1]); host = os_ref.resolve_host_path(Syscalls._read_cstring(cpu, cpu.reg[2])); cwd = getattr(getattr(cpu, "process", None), "cwd", os_ref.cwd); vp = os_ref.resolve(v, cwd)
            if vp not in os_ref.disk.files: raise FileNotFoundError(vp)
            data = os_ref.disk.read(vp); raw = data if isinstance(data, bytes) else str(data).encode("utf-8"); os.makedirs(os.path.dirname(host) or ".", exist_ok=True)
            with open(host, "wb") as f: f.write(raw)
            cpu.reg[0] = 0
        elif num == Syscalls.HOST_EXISTS:
            os_ref = Syscalls._require_os(cpu); host = os_ref.resolve_host_path(Syscalls._read_cstring(cpu, cpu.reg[1])); cpu.reg[0] = int(os.path.exists(host))
        elif num == Syscalls.EXEC_CAPTURE:
            os_ref = Syscalls._require_os(cpu)
            command = Syscalls._read_cstring(cpu, cpu.reg[1])
            process = getattr(cpu, "process", None)
            old_cwd = os_ref.cwd
            buffer = io.StringIO()
            import contextlib
            try:
                if process:
                    os_ref.cwd = process.cwd
                with contextlib.redirect_stdout(buffer):
                    os_ref.execute(command)
            finally:
                os_ref.cwd = old_cwd
            cpu.reg[0] = Syscalls._write_cstring(cpu, buffer.getvalue())
        elif num == Syscalls.HOST_READ:
            os_ref = Syscalls._require_os(cpu)
            host = os_ref.resolve_host_path(Syscalls._read_cstring(cpu, cpu.reg[1]))
            with open(host, "rb") as f:
                raw = f.read()
            decoded, _ = maybe_decode_rtf(raw)
            cpu.reg[0] = Syscalls._write_cstring(cpu, decoded.decode("utf-8", errors="replace"))
        elif num in (Syscalls.HOST_WRITE, Syscalls.HOST_APPEND):
            os_ref = Syscalls._require_os(cpu)
            host = os_ref.resolve_host_path(Syscalls._read_cstring(cpu, cpu.reg[1]))
            value = Syscalls._read_cstring(cpu, cpu.reg[2]).encode("utf-8")
            os.makedirs(os.path.dirname(host) or ".", exist_ok=True)
            mode = "ab" if num == Syscalls.HOST_APPEND else "wb"
            with open(host, mode) as f:
                f.write(value)
            cpu.reg[0] = 0
        elif num == Syscalls.HOST_DELETE:
            os_ref = Syscalls._require_os(cpu)
            host = os_ref.resolve_host_path(Syscalls._read_cstring(cpu, cpu.reg[1]))
            if os.path.isdir(host):
                os.rmdir(host)
            elif os.path.isfile(host):
                os.remove(host)
            else:
                raise FileNotFoundError(host)
            cpu.reg[0] = 0
        elif num == Syscalls.HOST_MKDIR:
            os_ref = Syscalls._require_os(cpu)
            host = os_ref.resolve_host_path(Syscalls._read_cstring(cpu, cpu.reg[1]))
            os.makedirs(host, exist_ok=True)
            cpu.reg[0] = 0
        elif num == Syscalls.HOST_LIST:
            os_ref = Syscalls._require_os(cpu)
            host = os_ref.resolve_host_path(Syscalls._read_cstring(cpu, cpu.reg[1]))
            names = []
            for name in sorted(os.listdir(host)):
                full = os.path.join(host, name)
                names.append(name + ("/" if os.path.isdir(full) else ""))
            cpu.reg[0] = Syscalls._write_cstring(cpu, "\n".join(names))
        elif num == Syscalls.HOST_ISDIR:
            os_ref = Syscalls._require_os(cpu)
            host = os_ref.resolve_host_path(Syscalls._read_cstring(cpu, cpu.reg[1]))
            cpu.reg[0] = int(os.path.isdir(host))
        elif num == Syscalls.HOST_SIZE:
            os_ref = Syscalls._require_os(cpu)
            host = os_ref.resolve_host_path(Syscalls._read_cstring(cpu, cpu.reg[1]))
            cpu.reg[0] = int(os.path.getsize(host))
        elif num == Syscalls.ARRAY_SET_STR:
            ptr, idx, sptr = int(cpu.reg[1]), s32(cpu.reg[2]), int(cpu.reg[3])
            ln = cpu.read32(ptr)
            if idx < 0 or idx >= ln:
                raise IndexError("index de tableau hors limites")
            Syscalls._read_cstring(cpu, sptr)
            cpu.write32(ptr + 4 + idx * 4, sptr)
            cpu.reg[0] = sptr
        elif num == Syscalls.STR_SPLIT:
            text_value = Syscalls._read_cstring(cpu, cpu.reg[1])
            sep = Syscalls._read_cstring(cpu, cpu.reg[2])
            parts = list(text_value) if sep == "" else text_value.split(sep)
            ptr = getattr(cpu, "memory_manager").alloc((len(parts) + 1) * 4, kind="refs", gc_cpu=cpu)
            cpu.write32(ptr, len(parts))
            for i, part in enumerate(parts):
                sptr = Syscalls._write_cstring(cpu, part)
                cpu.write32(ptr + 4 + i * 4, sptr)
            cpu.reg[0] = ptr
        elif num == Syscalls.STR_JOIN:
            ptr, sep_ptr = int(cpu.reg[1]), int(cpu.reg[2])
            sep = Syscalls._read_cstring(cpu, sep_ptr)
            ln = cpu.read32(ptr)
            parts = []
            for i in range(ln):
                sptr = cpu.read32(ptr + 4 + i * 4)
                parts.append(Syscalls._read_cstring(cpu, sptr))
            cpu.reg[0] = Syscalls._write_cstring(cpu, sep.join(parts))
        elif num == Syscalls.NET_PING:
            os_ref = Syscalls._require_os(cpu)
            host = Syscalls._read_cstring(cpu, cpu.reg[1])
            # Retour MiniLang : 0 = joignable, 1 = échec/délai dépassé.
            result = os_ref.cmd_ping([host], quiet=True)
            cpu.reg[0] = int(result)
        elif num == Syscalls.PID:
            cpu.reg[0] = int(getattr(getattr(cpu, "process", None), "pid", 0))
        elif num == Syscalls.PROGRAM:
            cpu.reg[0] = Syscalls._write_cstring(cpu, getattr(getattr(cpu, "process", None), "name", "program"))
        elif num == Syscalls.HOSTNAME:
            cpu.reg[0] = Syscalls._write_cstring(cpu, HOSTNAME)
        elif num == Syscalls.MEM_TOTAL:
            cpu.reg[0] = len(cpu.memory)
        elif num == Syscalls.MEM_FREE:
            cpu.reg[0] = max(0, len(cpu.memory) - getattr(cpu.memory_manager, 'used', 0))
        elif num == Syscalls.GFX_IMAGE_LOAD:
            process = getattr(cpu, "process", None)
            os_ref = Syscalls._require_os(cpu)
            if process is None: raise RuntimeError("processus VM32 absent")
            path = Syscalls._path(cpu, Syscalls._read_cstring(cpu, cpu.reg[1]))
            raw = os_ref.disk.read(path)
            if not isinstance(raw, bytes): raw = bytes(str(raw), "utf-8")
            try:
                cpu.reg[0] = process.image_manager.load(path, raw)
            except Exception as exc:
                raise RuntimeError(f"imageLoad: {exc}") from exc
        elif num in (Syscalls.GFX_IMAGE_DRAW, Syscalls.GFX_IMAGE_DRAW_SCALED, Syscalls.GFX_IMAGE_WIDTH, Syscalls.GFX_IMAGE_HEIGHT, Syscalls.GFX_IMAGE_FREE):
            process = getattr(cpu, "process", None)
            if process is None: raise RuntimeError("processus VM32 absent")
            handle = int(cpu.reg[1])
            try: image = process.image_manager.get(handle)
            except KeyError as exc: raise RuntimeError(str(exc)) from exc
            if num == Syscalls.GFX_IMAGE_WIDTH:
                cpu.reg[0] = image.width
            elif num == Syscalls.GFX_IMAGE_HEIGHT:
                cpu.reg[0] = image.height
            elif num == Syscalls.GFX_IMAGE_FREE:
                cpu.reg[0] = 0 if process.image_manager.free(handle) else 1
            else:
                os_ref = Syscalls._require_os(cpu); pid = int(getattr(process, "pid", 0)); gfx = getattr(os_ref, "graphics", None)
                if gfx is None: raise RuntimeError("moteur graphique miniOS indisponible")
                if num == Syscalls.GFX_IMAGE_DRAW:
                    gfx.image_draw(pid, image, s32(cpu.reg[2]), s32(cpu.reg[3]))
                else:
                    gfx.image_draw_scaled(pid, image, s32(cpu.reg[2]), s32(cpu.reg[3]), max(1,s32(cpu.reg[4])), max(1,s32(cpu.reg[5])))
                cpu.reg[0] = 0
        elif num == Syscalls.GFX_RGB:
            r = max(0, min(255, s32(cpu.reg[1])))
            g = max(0, min(255, s32(cpu.reg[2])))
            b = max(0, min(255, s32(cpu.reg[3])))
            cpu.reg[0] = (r << 16) | (g << 8) | b
        elif num in (Syscalls.GFX_WINDOW, Syscalls.GFX_CLEAR, Syscalls.GFX_PIXEL, Syscalls.GFX_RECT,
                      Syscalls.GFX_LINE, Syscalls.GFX_CIRCLE, Syscalls.GFX_TEXT, Syscalls.GFX_PRESENT,
                      Syscalls.GFX_CLOSE, Syscalls.GFX_MINIMIZE, Syscalls.GFX_KEY_DOWN, Syscalls.GFX_KEY_PRESSED, Syscalls.GFX_TEXT_INPUT, Syscalls.GFX_MOUSE_X, Syscalls.GFX_MOUSE_Y,
                      Syscalls.GFX_MOUSE_DOWN, Syscalls.GFX_CLOSE_REQUESTED, Syscalls.GFX_ALIVE):
            os_ref = Syscalls._require_os(cpu)
            process = getattr(cpu, "process", None)
            pid = int(getattr(process, "pid", 0))
            gfx = getattr(os_ref, "graphics", None)
            if gfx is None:
                raise RuntimeError("moteur graphique miniOS indisponible")
            if num == Syscalls.GFX_WINDOW:
                title = Syscalls._read_cstring(cpu, cpu.reg[1])
                cpu.reg[0] = gfx.window(title, max(1, s32(cpu.reg[2])), max(1, s32(cpu.reg[3])), pid)
            elif num == Syscalls.GFX_CLEAR:
                gfx.clear(pid, cpu.reg[1]); cpu.reg[0] = 0
            elif num == Syscalls.GFX_PIXEL:
                gfx.pixel(pid, s32(cpu.reg[1]), s32(cpu.reg[2]), cpu.reg[3]); cpu.reg[0] = 0
            elif num == Syscalls.GFX_RECT:
                gfx.rect(pid, s32(cpu.reg[1]), s32(cpu.reg[2]), s32(cpu.reg[3]), s32(cpu.reg[4]), cpu.reg[5]); cpu.reg[0] = 0
            elif num == Syscalls.GFX_LINE:
                gfx.line(pid, s32(cpu.reg[1]), s32(cpu.reg[2]), s32(cpu.reg[3]), s32(cpu.reg[4]), cpu.reg[5]); cpu.reg[0] = 0
            elif num == Syscalls.GFX_CIRCLE:
                gfx.circle(pid, s32(cpu.reg[1]), s32(cpu.reg[2]), s32(cpu.reg[3]), cpu.reg[4]); cpu.reg[0] = 0
            elif num == Syscalls.GFX_TEXT:
                text_value = Syscalls._read_cstring(cpu, cpu.reg[3])
                gfx.text(pid, s32(cpu.reg[1]), s32(cpu.reg[2]), text_value, cpu.reg[4]); cpu.reg[0] = 0
            elif num == Syscalls.GFX_PRESENT:
                gfx.present(pid); cpu.reg[0] = 0
            elif num == Syscalls.GFX_CLOSE:
                gfx.close(pid); cpu.reg[0] = 0
            elif num == Syscalls.GFX_MINIMIZE:
                gfx.minimize(pid); cpu.reg[0] = 0
            elif num == Syscalls.GFX_KEY_DOWN:
                key = Syscalls._read_cstring(cpu, cpu.reg[1]); cpu.reg[0] = 1 if gfx.key_down(pid, key) else 0
            elif num == Syscalls.GFX_KEY_PRESSED:
                key = Syscalls._read_cstring(cpu, cpu.reg[1]); cpu.reg[0] = 1 if gfx.key_pressed(pid, key) else 0
            elif num == Syscalls.GFX_TEXT_INPUT:
                action = Syscalls._read_cstring(cpu, cpu.reg[1]) if cpu.reg[1] else "get"
                cpu.reg[0] = Syscalls._write_cstring(cpu, gfx.text_input(pid, action))
            elif num == Syscalls.GFX_MOUSE_X:
                cpu.reg[0] = gfx.mouse_x(pid)
            elif num == Syscalls.GFX_MOUSE_Y:
                cpu.reg[0] = gfx.mouse_y(pid)
            elif num == Syscalls.GFX_MOUSE_DOWN:
                cpu.reg[0] = 1 if gfx.mouse_down(pid, s32(cpu.reg[1])) else 0
            elif num == Syscalls.GFX_CLOSE_REQUESTED:
                cpu.reg[0] = 1 if gfx.close_requested(pid) else 0
            elif num == Syscalls.GFX_ALIVE:
                cpu.reg[0] = 1 if gfx.alive(pid) else 0
        else:
            raise RuntimeError(f"syscall VM32 inconnue: {num}")


@dataclass
class VirtualProcess:
    pid: int
    name: str
    exe: MEXE
    state: str = "READY"
    exit_code: Optional[int] = None
    started_at: float = field(default_factory=time.time)
    os_ref: Any = None
    argv: List[str] = field(default_factory=list)
    cwd: str = "/home/user"
    stdin_data: Optional[str] = None
    stdin_pos: int = 0
    stdin_pipe: bool = False
    debug: bool = False

    def __post_init__(self):
        self.memory = bytearray(RAM_SIZE)
        self.memory_manager = MemoryManager(RAM_SIZE)
        self.image_manager = ImageManager()
        self.cpu = CPU(self.memory, Syscalls.handle)
        self.cpu.memory_manager = self.memory_manager
        self.cpu.os_ref = self.os_ref
        self.cpu.process = self
        self.cpu.argv = list(self.argv)
        self.cpu.load(self.exe)
        self.cpu.global_base = MiniLangCompiler.GLOBAL_BASE if "MiniLangCompiler" in globals() else 0x00C00000
        self.cpu.global_count = 1024
        self.thread: Optional[threading.Thread] = None
        self.stop_event = threading.Event()
        self.done_event = threading.Event()
        self.error: Optional[BaseException] = None
        self.background = False
        self._lock = threading.RLock()
        self.debug_log_path: Optional[str] = None
        self._debug_file = None
        self._debug_lock = threading.RLock()
        self._debug_recent: List[str] = []
        if self.debug:
            try:
                base = os.path.dirname(self.os_ref.disk.storage_path) if self.os_ref is not None else os.getcwd()
                os.makedirs(base, exist_ok=True)
                safe = re.sub(r"[^A-Za-z0-9_.-]+", "_", self.name)
                self.debug_log_path = os.path.join(base, f"minios_debug_{self.pid}_{safe}.log")
                self._debug_file = open(self.debug_log_path, "w", encoding="utf-8", buffering=1)
                self.cpu.debug_hook = self._debug_cpu_event
                self._debug_write("DEBUG", f"processus créé; pid={self.pid}; nom={self.name}; background={self.background}")
                self._debug_write("DEBUG", f"RAM={RAM_SIZE} octets; code=0x{self.cpu.code_start:04X}-0x{self.cpu.code_end:04X}; data=0x{self.cpu.data_start:04X}-0x{self.cpu.data_end:04X}; entry=0x{self.cpu.pc:04X}")
                self._debug_write("DEBUG", f"argv={self.argv!r}; cwd={self.cwd!r}; stdin_pipe={self.stdin_pipe}")
            except Exception as exc:
                self.debug = False
                self.debug_log_path = None
                self._debug_file = None
                print(f"[DEBUG] impossible d'ouvrir le journal PID={self.pid}: {exc}")

    def _debug_write(self, tag: str, message: str):
        if not self.debug:
            return
        now = time.time()
        stamp = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(now)) + f".{int((now % 1)*1000):03d}"
        line = f"[{stamp}] [{tag}] {message}"
        with self._debug_lock:
            self._debug_recent.append(line)
            if len(self._debug_recent) > 2000:
                del self._debug_recent[:-2000]
            if self._debug_file is not None:
                self._debug_file.write(line + "\n")
                self._debug_file.flush()

    def _debug_cpu_event(self, cpu, event: Dict[str, Any]):
        def regs(values):
            return " ".join(f"R{i}=0x{int(v)&WORD_MASK:08X}({s32(v)})" for i,v in enumerate(values))
        flags = event.get("flags_after", {})
        msg = (
            f"step={event.get('step')} pc=0x{event.get('pc',0):04X}->0x{event.get('pc_after',0):04X} "
            f"op={event.get('opcode_name')} raw={event.get('raw','')} "
            f"SP=0x{event.get('sp_before',0):08X}->0x{event.get('sp_after',0):08X} "
            f"flags={flags} regs_before=[{regs(event.get('regs_before',[]))}] regs_after=[{regs(event.get('regs_after',[]))}]"
        )
        if event.get("syscall"):
            msg += f" syscall={event.get('syscall')}({event.get('syscall_num')})"
        if event.get("type") == "instruction_error":
            msg += f" EXCEPTION={event.get('exception')}"
        self._debug_write("CPU", msg)

    def debug_event(self, tag: str, message: str):
        self._debug_write(str(tag), str(message))

    def _close_debug(self):
        with self._debug_lock:
            if self._debug_file is not None:
                try:
                    self._debug_file.flush()
                    self._debug_file.close()
                except Exception:
                    pass
                self._debug_file = None

    def read_stdin_line(self) -> Tuple[bool, str]:
        """Lit une ligne depuis l'entrée standard pipée du processus.

        Retourne (True, ligne) si une ligne est disponible, sinon (False, "")
        lorsque l'entrée standard est arrivée à EOF.
        """
        if not self.stdin_pipe:
            return False, ""
        data = self.stdin_data or ""
        if self.stdin_pos >= len(data):
            return False, ""
        end = data.find("\n", self.stdin_pos)
        if end < 0:
            line = data[self.stdin_pos:]
            self.stdin_pos = len(data)
        else:
            line = data[self.stdin_pos:end]
            self.stdin_pos = end + 1
        if line.endswith("\r"):
            line = line[:-1]
        return True, line

    @property
    def runtime(self) -> float:
        return max(0.0, time.time() - self.started_at)

    def request_stop(self, code: int = -9):
        with self._lock:
            self.stop_event.set()
            self.cpu.halted = True
            if self.exit_code is None:
                self.exit_code = code
            if self.state not in ("EXITED", "CRASHED"):
                self.state = "KILLED"

    def run_slice(self, quantum: int = VM_TIMESLICE) -> bool:
        """Exécute une tranche d'instructions sans limite cumulée de durée de vie."""
        if self.cpu.halted or self.stop_event.is_set():
            return False
        with self._lock:
            if self.state not in ("RUNNING", "READY", "SLEEPING", "WAITING_INPUT"):
                return False
            self.state = "RUNNING"
        for _ in range(max(1, int(quantum))):
            if self.stop_event.is_set() or self.cpu.halted:
                break
            self.cpu.step()
        if self.cpu.halted or self.stop_event.is_set():
            return False
        return True

    def run(self):
        """Exécution synchrone conservée pour le mode foreground/tests."""
        self.state = "RUNNING"
        try:
            self.exit_code = self.cpu.run()
            if self.state != "KILLED":
                self.state = "EXITED"
            return self.exit_code
        except Exception as exc:
            self.error = exc
            self.state = "CRASHED"
            self._debug_write("CRASH", f"{type(exc).__name__}: {exc}")
            self._debug_write("TRACEBACK", traceback.format_exc().rstrip())
            raise
        finally:
            NETWORK_SOCKETS.close_all(self.pid)
            try: self.image_manager.clear()
            except Exception: pass
            self._close_debug()
            self.done_event.set()
            if self.os_ref is not None:
                try:
                    self.os_ref.graphics.close(self.pid)
                except Exception:
                    pass

    def start_background(self, quantum: int = VM_TIMESLICE):
        """Démarre le processus sur un thread daemon et lui donne des tranches."""
        if self.thread and self.thread.is_alive():
            return
        self.background = True

        def worker():
            self.state = "RUNNING"
            try:
                while not self.stop_event.is_set() and not self.cpu.halted:
                    alive = self.run_slice(quantum)
                    if not alive:
                        break
                    # Laisser respirer le shell et les autres processus.
                    time.sleep(VM_YIELD_SECONDS)
                self._debug_write("PROCESS", f"fin de boucle CPU; halted={self.cpu.halted}; stop={self.stop_event.is_set()}; state={self.state}")
                if self.state == "KILLED" or self.stop_event.is_set():
                    if self.exit_code is None:
                        self.exit_code = -9
                    self.state = "KILLED"
                elif self.cpu.halted:
                    self.exit_code = self.cpu.exit_code
                    self.state = "EXITED"
            except Exception as exc:
                self.error = exc
                self.state = "CRASHED"
                self._debug_write("CRASH", f"{type(exc).__name__}: {exc}")
                self._debug_write("TRACEBACK", traceback.format_exc().rstrip())
            finally:
                self._debug_write("PROCESS", f"fin processus state={self.state} exit_code={self.exit_code} steps={self.cpu.steps} pc=0x{self.cpu.pc:04X}")
                NETWORK_SOCKETS.close_all(self.pid)
                self._close_debug()
                self.done_event.set()
                if self.os_ref is not None:
                    try:
                        self.os_ref.graphics.close(self.pid)
                    except Exception:
                        pass
                if self.error is not None:
                    print(f"[VM32] PID={self.pid} CRASH: {self.error}")
                elif self.state == "EXITED":
                    print(f"[VM32] PID={self.pid} terminé (code={self.exit_code or 0})")
                elif self.state == "KILLED":
                    print(f"[VM32] PID={self.pid} tué")

        self.thread = threading.Thread(target=worker, name=f"miniOS-PID-{self.pid}", daemon=True)
        self.thread.start()


# ================================================================
# Virtual filesystem
# ================================================================

class VirtualDisk:
    """Virtual filesystem persisted on the real host as one atomic JSON file."""
    FORMAT_VERSION = 2

    def __init__(self, storage_path: str = MINIOS_DISK_FILE):
        self.storage_path = os.path.abspath(storage_path)
        self.files: Dict[str, Any] = {}
        self.dirs = set(["/", "/bin", "/path", "/home", "/home/user", "/system", "/tmp", "/dev", "/apps"])
        self.load()

    def _encode_data(self, data: Any) -> Dict[str, Any]:
        if isinstance(data, bytes):
            return {"type": "bytes", "data": base64.b64encode(data).decode("ascii")}
        return {"type": "text", "data": str(data)}

    def _decode_data(self, item: Dict[str, Any]) -> Any:
        if item.get("type") == "bytes":
            return base64.b64decode(item.get("data", ""))
        return item.get("data", "")

    def load(self):
        if not os.path.isfile(self.storage_path):
            self.save()
            return
        try:
            with open(self.storage_path, "r", encoding="utf-8") as f:
                obj = json.load(f)
            disk_format = int(obj.get("format", 1))
            if disk_format not in (1, self.FORMAT_VERSION):
                raise ValueError(f"format de disque inconnu: {disk_format}")
            loaded_dirs = obj.get("dirs", [])
            loaded_files = obj.get("files", {})
            self.dirs = {self.norm(path, "/") for path in loaded_dirs} | {"/"}
            self.files = {self.norm(path, "/"): self._decode_data(item) for path, item in loaded_files.items()}
            # Un chemin ne peut être simultanément un fichier et un répertoire.
            # En cas d'ancien disque incohérent, le type répertoire est prioritaire
            # pour les entrées présentes dans ``dirs`` : le fichier fantôme est
            # retiré pour permettre à ``cd`` et ``ls`` de fonctionner normalement.
            collisions = set(self.files) & self.dirs
            for path in collisions:
                del self.files[path]
            # Toujours restaurer les répertoires système obligatoires.
            self.dirs.update(["/", "/bin", "/path", "/home", "/home/user", "/system", "/tmp", "/dev", "/apps"])
            # Un ancien disque format 1 est automatiquement migré au format actuel.
            if disk_format != self.FORMAT_VERSION:
                self.save()
                print(f"[DISK] disque ancien (format {disk_format}) migré vers le format {self.FORMAT_VERSION}")
        except Exception as e:
            print(f"[DISK] impossible de charger {self.storage_path}: {e}")
            print("[DISK] création d'un nouveau disque virtuel.")
            self.files = {}
            self.dirs = set(["/", "/bin", "/path", "/home", "/home/user", "/system", "/tmp", "/dev", "/apps"])
            self.save()

    def save(self):
        os.makedirs(os.path.dirname(self.storage_path) or ".", exist_ok=True)
        tmp = self.storage_path + ".tmp"
        obj = {
            "format": self.FORMAT_VERSION,
            "version": VERSION,
            "dirs": sorted(self.dirs),
            "files": {path: self._encode_data(data) for path, data in self.files.items()},
        }
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(obj, f, ensure_ascii=False, indent=2)
        os.replace(tmp, self.storage_path)

    def norm(self, path: str, cwd: str = "/home/user") -> str:
        """Normalize every virtual path consistently. Supports /, ., .., ~ and\\ as separator."""
        if path is None:
            return cwd
        path = str(path).strip().replace("\\", "/")
        if path in ("", "."):
            return cwd
        if path == "~":
            path = "/home/user"
        elif path.startswith("~/"):
            path = "/home/user/" + path[2:]
        if not path.startswith("/"):
            path = cwd.rstrip("/") + "/" + path
        parts: List[str] = []
        for part in path.split("/"):
            if part in ("", "."):
                continue
            if part == "..":
                if parts:
                    parts.pop()
            else:
                parts.append(part)
        return "/" + "/".join(parts)

    def parent(self, path: str) -> str:
        path = self.norm(path)
        if path == "/": return "/"
        p = path.rsplit("/", 1)[0]
        return p or "/"

    def mkdir(self, path: str, parents: bool = False):
        p = self.norm(path)
        # Un fichier existant bloque toujours mkdir : un fichier et un répertoire
        # ne peuvent pas partager le même chemin.
        if p in self.files:
            raise FileExistsError(f"Le fichier existe déjà: {p}")
        if p in self.dirs:
            return
        if parents:
            cur = ""
            for part in p.strip("/").split("/"):
                cur += "/" + part
                if cur in self.files:
                    raise FileExistsError(cur)
                self.dirs.add(cur)
        else:
            par = self.parent(p)
            if par not in self.dirs:
                raise FileNotFoundError(par)
            self.dirs.add(p)
        self.save()

    def write(self, path: str, data: Any):
        p = self.norm(path)
        if p in self.dirs:
            raise IsADirectoryError(p)
        if self.parent(p) not in self.dirs:
            raise FileNotFoundError(self.parent(p))
        self.files[p] = data
        self.save()

    def append(self, path: str, data: Any):
        p = self.norm(path)
        if p not in self.files:
            self.write(p, data)
            return
        old = self.files[p]
        if isinstance(old, bytes) or isinstance(data, bytes):
            self.files[p] = bytes(old if isinstance(old, bytes) else str(old).encode("utf-8")) + bytes(data if isinstance(data, bytes) else str(data).encode("utf-8"))
        else:
            self.files[p] = str(old) + str(data)
        self.save()

    def read(self, path: str) -> Any:
        p = self.norm(path)
        if p not in self.files:
            raise FileNotFoundError(p)
        return self.files[p]

    def exists(self, path: str) -> bool:
        p = self.norm(path)
        return p in self.files or p in self.dirs

    def is_dir(self, path: str, cwd: str = "/home/user") -> bool:
        return self.norm(path, cwd) in self.dirs

    def remove_empty_dir(self, path: str, cwd: str = "/home/user"):
        self.delete(self.norm(path, cwd), recursive=False)

    def delete(self, path: str, recursive: bool = False, cwd: str = "/home/user"):
        p = self.norm(path, cwd)
        p = self.norm(path)
        if p in self.files:
            del self.files[p]
            self.save()
            return
        if p not in self.dirs:
            raise FileNotFoundError(p)
        if p == "/":
            raise PermissionError("Impossible de supprimer /")
        children = [x for x in self.files if x.startswith(p.rstrip("/") + "/")] + [x for x in self.dirs if x.startswith(p.rstrip("/") + "/")]
        if children and not recursive:
            raise OSError("Répertoire non vide")
        for x in list(self.files):
            if x == p or x.startswith(p.rstrip("/") + "/"):
                del self.files[x]
        for x in sorted(list(self.dirs), key=len, reverse=True):
            if x == p or x.startswith(p.rstrip("/") + "/"):
                self.dirs.remove(x)
        self.save()

    def ls(self, path: str = ".", cwd: str = "/home/user") -> List[Tuple[str, bool]]:
        p = self.norm(path, cwd)
        if p in self.files:
            return [(p.rsplit("/", 1)[-1], False)]
        if p not in self.dirs:
            raise FileNotFoundError(p)
        prefix = p.rstrip("/") + "/"
        names: Dict[str, bool] = {}
        for d in self.dirs:
            if d.startswith(prefix) and d != p:
                rest = d[len(prefix):]
                if "/" not in rest:
                    names[rest] = True
        for f in self.files:
            if f.startswith(prefix):
                rest = f[len(prefix):]
                if "/" not in rest and rest not in names:
                    names[rest] = False
        return sorted(names.items())

    def copy(self, src: str, dst: str):
        s = self.norm(src); d = self.norm(dst)
        if s in self.files:
            if d in self.dirs:
                d = d.rstrip("/") + "/" + s.rsplit("/", 1)[-1]
            self.write(d, self.files[s])
            return
        if s in self.dirs:
            if d in self.files:
                raise FileExistsError(d)
            if d in self.dirs:
                d = d.rstrip("/") + "/" + s.rsplit("/", 1)[-1]
            self.mkdir(d, parents=True)
            prefix = s.rstrip("/") + "/"
            for fpath, data in list(self.files.items()):
                if fpath.startswith(prefix):
                    rel = fpath[len(prefix):]
                    self.write(d.rstrip("/") + "/" + rel, data)
            return
        raise FileNotFoundError(s)

    def move(self, src: str, dst: str):
        s = self.norm(src)
        self.copy(s, dst)
        self.delete(s, recursive=(s in self.dirs))


# ================================================================
# MiniLang (small compiler)
# ================================================================

class MiniLangCompileError(Exception):
    def __init__(self, message: str, line: int = 0, source_line: str = "", col: int = 0):
        self.message = message
        self.line = line
        self.source_line = source_line
        self.col = col
        prefix = f"Ligne {line}" if line else "MiniLang"
        if col:
            prefix += f", colonne {col}"
        detail = f"\n    > {source_line}" if source_line else ""
        super().__init__(f"{prefix}: {message}{detail}")


@dataclass
class MLToken:
    kind: str
    value: str
    line: int
    col: int
    source: str


class MiniLangLexer:
    MULTI_OPS = [
        "===", "!==", "++", "--", "+=", "-=", "*=", "/=", "%=",
        "==", "!=", "<=", ">=", "&&", "||", "<<", ">>",
    ]
    SINGLE = set("(){}[],;:+-*/%<>=!&|^~")

    def __init__(self, source: str):
        self.source = source
        self.lines = source.splitlines()
        self.i = 0
        self.line = 1
        self.col = 1
        self.paren_depth = 0

    def _line_text(self, line_no: int) -> str:
        if 1 <= line_no <= len(self.lines):
            return self.lines[line_no - 1].rstrip("\\n")
        return ""

    def _error(self, msg: str, line: Optional[int] = None, col: Optional[int] = None):
        ln = line or self.line
        cl = col or self.col
        raise MiniLangCompileError(msg, ln, self._line_text(ln), cl)

    def tokenize(self) -> List[MLToken]:
        src = self.source
        n = len(src)
        out: List[MLToken] = []
        while self.i < n:
            c = src[self.i]
            if c in " \t\r":
                self.i += 1; self.col += 1; continue
            if c == "\n":
                if self.paren_depth == 0:
                    out.append(MLToken("NEWLINE", "\\n", self.line, self.col, self._line_text(self.line)))
                self.i += 1; self.line += 1; self.col = 1; continue

            # Comments: # ... and // ...
            if c == '#':
                while self.i < n and src[self.i] != "\n":
                    self.i += 1; self.col += 1
                continue
            if c == '/' and self.i + 1 < n and src[self.i + 1] == '/':
                while self.i < n and src[self.i] != "\n":
                    self.i += 1; self.col += 1
                continue

            line0, col0 = self.line, self.col

            if c in "'\"":
                quote = c
                j = self.i + 1
                escaped = False
                while j < n:
                    ch = src[j]
                    if escaped:
                        escaped = False
                    elif ch == '\\':
                        escaped = True
                    elif ch == quote:
                        break
                    elif ch == "\n":
                        self._error("chaîne non terminée", line0, col0)
                    j += 1
                if j >= n or src[j] != quote:
                    self._error("chaîne non terminée", line0, col0)
                raw = src[self.i:j + 1]
                try:
                    value = ast.literal_eval(raw)
                except Exception as exc:
                    self._error(f"chaîne invalide : {exc}", line0, col0)
                out.append(MLToken("STRING", value, line0, col0, self._line_text(line0)))
                self.col += len(raw); self.i = j + 1; continue

            if c.isdigit():
                j = self.i
                if src.startswith(("0x", "0X"), j):
                    j += 2
                    start_digits = j
                    while j < n and (src[j].isdigit() or src[j].lower() in "abcdef"):
                        j += 1
                    if j == start_digits:
                        self._error("nombre hexadécimal invalide", line0, col0)
                else:
                    while j < n and src[j].isdigit():
                        j += 1
                raw = src[self.i:j]
                out.append(MLToken("NUMBER", raw, line0, col0, self._line_text(line0)))
                self.col += len(raw); self.i = j; continue

            if c.isalpha() or c == '_':
                j = self.i + 1
                while j < n and (src[j].isalnum() or src[j] == '_'):
                    j += 1
                raw = src[self.i:j]
                out.append(MLToken("IDENT", raw, line0, col0, self._line_text(line0)))
                self.col += len(raw); self.i = j; continue

            matched = False
            for op in self.MULTI_OPS:
                if src.startswith(op, self.i):
                    # === and !== are accepted as aliases but normalized later.
                    value = "==" if op == "===" else ("!=" if op == "!==" else op)
                    out.append(MLToken("OP", value, line0, col0, self._line_text(line0)))
                    self.i += len(op); self.col += len(op); matched = True; break
            if matched:
                continue

            if c in self.SINGLE:
                out.append(MLToken("OP", c, line0, col0, self._line_text(line0)))
                if c == '(':
                    self.paren_depth += 1
                elif c == ')' and self.paren_depth:
                    self.paren_depth -= 1
                self.i += 1; self.col += 1; continue

            self._error(f"caractère non reconnu : {c!r}", line0, col0)

        out.append(MLToken("EOF", "", self.line, self.col, self._line_text(self.line)))
        return out


# -------------------------- AST --------------------------

@dataclass
class MLProgram:
    statements: List[Any]


@dataclass
class MLBlock:
    statements: List[Any]


@dataclass
class MLLet:
    name: str
    expr: Optional[Any]
    token: MLToken


@dataclass
class MLAssign:
    name: str
    op: str
    expr: Any
    token: MLToken


@dataclass
class MLPrint:
    expr: Any
    token: MLToken
    end_expr: Optional[Any] = None
    flush_expr: Optional[Any] = None


@dataclass
class MLExit:
    expr: Any
    token: MLToken


@dataclass
class MLIf:
    cond: Any
    then_block: MLBlock
    else_block: Optional[MLBlock]
    token: MLToken


@dataclass
class MLWhile:
    cond: Any
    body: MLBlock
    token: MLToken


@dataclass
class MLFor:
    init: Optional[Any]
    cond: Optional[Any]
    update: Optional[Any]
    body: MLBlock
    token: MLToken


@dataclass
class MLFunction:
    name: str
    params: List[str]
    body: MLBlock
    token: MLToken


@dataclass
class MLReturn:
    expr: Optional[Any]
    token: MLToken


@dataclass
class MLBreak:
    token: MLToken


@dataclass
class MLContinue:
    token: MLToken


@dataclass
class MLExprStmt:
    expr: Any
    token: MLToken


@dataclass
class MLLiteral:
    value: Any
    token: MLToken


@dataclass
class MLVar:
    name: str
    token: MLToken


@dataclass
class MLUnary:
    op: str
    expr: Any
    prefix: bool
    token: MLToken


@dataclass
class MLBinary:
    op: str
    left: Any
    right: Any
    token: MLToken


@dataclass
class MLCall:
    name: str
    args: List[Any]
    token: MLToken


@dataclass
class MLIndex:
    target: Any
    index: Any
    token: MLToken


@dataclass
class MLIndexAssign:
    target: Any
    index: Any
    op: str
    expr: Any
    token: MLToken


class MiniLangParser:
    KEYWORDS = {
        "let", "if", "else", "while", "for", "function", "return",
        "break", "continue", "print", "exit", "true", "false"
    }

    PRECEDENCE = {
        "||": 1,
        "&&": 2,
        "|": 3,
        "^": 4,
        "&": 5,
        "==": 6, "!=": 6,
        "<": 7, "<=": 7, ">": 7, ">=": 7,
        "<<": 8, ">>": 8,
        "+": 9, "-": 9,
        "*": 10, "/": 10, "%": 10,
    }

    def __init__(self, source: str):
        self.source = source
        self.tokens = MiniLangLexer(source).tokenize()
        self.i = 0

    def peek(self, k: int = 0) -> MLToken:
        return self.tokens[min(self.i + k, len(self.tokens) - 1)]

    def at(self, value: str) -> bool:
        return self.peek().value == value

    def advance(self) -> MLToken:
        t = self.peek()
        if t.kind != "EOF":
            self.i += 1
        return t

    def accept(self, value: str) -> Optional[MLToken]:
        if self.at(value):
            return self.advance()
        return None

    def expect(self, value: str, message: Optional[str] = None) -> MLToken:
        t = self.peek()
        if t.value != value:
            msg = message or f"'{value}' attendu, trouvé {t.value!r}"
            raise MiniLangCompileError(msg, t.line, t.source, t.col)
        return self.advance()

    def separators(self):
        while self.peek().kind == "NEWLINE" or self.at(";"):
            self.advance()

    def parse(self) -> MLProgram:
        stmts = []
        self.separators()
        while self.peek().kind != "EOF":
            stmts.append(self.parse_statement(top_level=True))
            self.separators()
        if not stmts:
            t = self.peek()
            raise MiniLangCompileError("source vide : rien à compiler", t.line, t.source, t.col)
        return MLProgram(stmts)

    def parse_statement(self, top_level: bool = False, for_header: bool = False):
        t = self.peek()
        if t.kind == "EOF":
            raise MiniLangCompileError("instruction attendue", t.line, t.source, t.col)
        if self.at("{"):
            return self.parse_block()

        if self.at("function"):
            if not top_level:
                raise MiniLangCompileError("une fonction doit être déclarée au niveau principal", t.line, t.source, t.col)
            return self.parse_function()

        if self.at("let"):
            self.advance()
            name = self.peek()
            if name.kind != "IDENT" or name.value in self.KEYWORDS:
                raise MiniLangCompileError("nom de variable attendu après 'let'", name.line, name.source, name.col)
            self.advance()
            expr = None
            if self.accept("="):
                expr = self.parse_expression()
            return MLLet(name.value, expr, name)

        if self.at("if"):
            self.advance()
            self.expect("(", "'(' attendu après 'if'")
            cond = self.parse_expression()
            self.expect(")", "')' attendu après la condition de 'if'")
            then_block = self.parse_block()
            self.separators()
            else_block = None
            if self.accept("else"):
                if self.at("if"):
                    # else if -> block wrapper around a nested if
                    nested = self.parse_statement(top_level=False)
                    else_block = MLBlock([nested])
                else:
                    else_block = self.parse_block()
            return MLIf(cond, then_block, else_block, t)

        if self.at("while"):
            self.advance()
            self.expect("(", "'(' attendu après 'while'")
            cond = self.parse_expression()
            self.expect(")", "')' attendu après la condition de 'while'")
            body = self.parse_block()
            return MLWhile(cond, body, t)

        if self.at("for"):
            return self.parse_for()

        if self.at("print"):
            self.advance()
            end_expr = None
            flush_expr = None
            # print(...) supporte désormais les formes utiles pour les programmes
            # MiniLang et les conversions Python:
            #   print()
            #   print(expr)
            #   print(expr, end="")
            #   print(expr, flush=True, end="")
            #   print(end=end)
            if self.accept("("):
                expr = None
                if not self.at(")"):
                    # Si le premier élément est déjà un argument nommé, il n'y a
                    # pas d'expression de valeur (ex: print(end="\n")).
                    if not (self.peek().kind == "IDENT" and self.peek().value in ("end", "flush") and self.peek(1).value == "="):
                        expr = self.parse_expression()
                while self.accept(",") or (expr is None and not self.at(")")):
                    kw = self.peek()
                    if kw.kind == "IDENT" and kw.value in ("end", "flush") and self.peek(1).value == "=":
                        self.advance()
                        self.advance()
                        value = self.parse_expression()
                        if kw.value == "end":
                            if end_expr is not None:
                                raise MiniLangCompileError("argument 'end' fourni plusieurs fois", kw.line, kw.source, kw.col)
                            end_expr = value
                        else:
                            if flush_expr is not None:
                                raise MiniLangCompileError("argument 'flush' fourni plusieurs fois", kw.line, kw.source, kw.col)
                            flush_expr = value
                    else:
                        if expr is None:
                            # Premier argument positionnel si print(end=...) n'était
                            # pas utilisé en premier.
                            expr = self.parse_expression()
                        elif end_expr is None:
                            end_expr = self.parse_expression()
                        else:
                            raise MiniLangCompileError("print() n'accepte qu'une valeur et un argument end", kw.line, kw.source, kw.col)
                self.expect(")", "')' attendu après 'print'")
            else:
                # Forme sans parenthèses: print expression
                expr = self.parse_expression()
            # print() sans valeur équivaut à une ligne vide. On matérialise la
            # valeur absente comme une chaîne vide afin que le compilateur puisse
            # utiliser exactement le même syscall que print(expr, end=...).
            if expr is None:
                empty_tok = t
                expr = MLLiteral("", empty_tok)
            return MLPrint(expr, t, end_expr, flush_expr)

        if self.at("exit"):
            self.advance()
            if self.accept("("):
                expr = self.parse_expression()
                self.expect(")", "')' attendu après 'exit'")
            else:
                expr = self.parse_expression()
            return MLExit(expr, t)

        if self.at("return"):
            self.advance()
            if self.at(";") or self.peek().kind in ("NEWLINE", "EOF") or self.at("}"):
                expr = None
            else:
                expr = self.parse_expression()
            return MLReturn(expr, t)

        if self.at("break"):
            self.advance()
            return MLBreak(t)
        if self.at("continue"):
            self.advance()
            return MLContinue(t)

        # Affectation simple/composee : variable ou element de tableau.
        expr = self.parse_expression()
        if self.peek().value in ("=", "+=", "-=", "*=", "/=", "%=") and isinstance(expr, (MLVar, MLIndex)):
            op_tok = self.advance()
            rhs = self.parse_expression()
            if isinstance(expr, MLVar):
                return MLAssign(expr.name, op_tok.value, rhs, expr.token)
            return MLIndexAssign(expr.target, expr.index, op_tok.value, rhs, expr.token)
        return MLExprStmt(expr, t)

    def parse_block(self) -> MLBlock:
        open_tok = self.expect("{", "'{' attendu")
        self.separators()
        stmts = []
        while not self.at("}"):
            if self.peek().kind == "EOF":
                raise MiniLangCompileError("'}' manquant pour fermer le bloc", open_tok.line, open_tok.source, open_tok.col)
            stmts.append(self.parse_statement(top_level=False))
            self.separators()
        self.advance()
        return MLBlock(stmts)

    def parse_function(self) -> MLFunction:
        tok = self.expect("function")
        name = self.peek()
        if name.kind != "IDENT" or name.value in self.KEYWORDS:
            raise MiniLangCompileError("nom de fonction attendu après 'function'", name.line, name.source, name.col)
        self.advance()
        self.expect("(", "'(' attendu après le nom de fonction")
        params: List[str] = []
        if not self.at(")"):
            while True:
                p = self.peek()
                if p.kind != "IDENT" or p.value in self.KEYWORDS:
                    raise MiniLangCompileError("nom de paramètre attendu", p.line, p.source, p.col)
                self.advance()
                if p.value in params:
                    raise MiniLangCompileError(f"paramètre dupliqué : {p.value}", p.line, p.source, p.col)
                params.append(p.value)
                if not self.accept(","):
                    break
        self.expect(")", "')' attendu dans la déclaration de fonction")
        body = self.parse_block()
        return MLFunction(name.value, params, body, tok)

    def parse_for(self) -> MLFor:
        tok = self.expect("for")
        self.expect("(", "'(' attendu après 'for'")

        init = None
        if not self.at(";"):
            if self.at("let"):
                init = self.parse_statement(for_header=True)
            else:
                t = self.peek()
                if t.kind == "IDENT" and self.peek(1).value in ("=", "+=", "-=", "*=", "/=", "%="):
                    self.advance(); op = self.advance().value
                    init = MLAssign(t.value, op, self.parse_expression(), t)
                else:
                    init = MLExprStmt(self.parse_expression(), t)
        self.expect(";", "';' attendu après l'initialisation du 'for'")

        cond = None if self.at(";") else self.parse_expression()
        self.expect(";", "';' attendu après la condition du 'for'")

        update = None
        if not self.at(")"):
            t = self.peek()
            if t.kind == "IDENT" and self.peek(1).value in ("=", "+=", "-=", "*=", "/=", "%="):
                self.advance(); op = self.advance().value
                update = MLAssign(t.value, op, self.parse_expression(), t)
            else:
                update = MLExprStmt(self.parse_expression(), t)
        self.expect(")", "')' attendu après le 'for'")
        body = self.parse_block()
        return MLFor(init, cond, update, body, tok)

    def parse_expression(self, min_prec: int = 0):
        tok = self.peek()
        if tok.kind == "NUMBER":
            self.advance()
            try:
                value = int(tok.value, 0)
            except ValueError:
                raise MiniLangCompileError(f"nombre invalide : {tok.value}", tok.line, tok.source, tok.col)
            left = MLLiteral(value, tok)
        elif tok.kind == "STRING":
            self.advance(); left = MLLiteral(tok.value, tok)
        elif tok.kind == "IDENT":
            self.advance()
            if self.at("("):
                self.advance()
                args = []
                if not self.at(")"):
                    while True:
                        args.append(self.parse_expression())
                        if not self.accept(","):
                            break
                self.expect(")", "')' attendu dans l'appel de fonction")
                left = MLCall(tok.value, args, tok)
            else:
                if tok.value.lower() in ("true", "false"):
                    left = MLLiteral(tok.value.lower() == "true", tok)
                else:
                    left = MLVar(tok.value, tok)
        elif tok.value in ("+", "-", "!", "~", "++", "--"):
            self.advance()
            expr = self.parse_expression(11)
            left = MLUnary(tok.value, expr, True, tok)
        elif self.accept("("):
            left = self.parse_expression()
            self.expect(")", "')' attendu")
        else:
            raise MiniLangCompileError(f"expression inattendue : {tok.value!r}", tok.line, tok.source, tok.col)

        # Postfix indexing/calls supplémentaires.
        while True:
            if self.accept("["):
                idx_tok = tok
                index = self.parse_expression()
                self.expect("]", "']' attendu après l'index")
                left = MLIndex(left, index, idx_tok)
                continue
            if self.peek().value in ("++", "--"):
                op_tok = self.advance()
                if not isinstance(left, MLVar):
                    raise MiniLangCompileError(f"'{op_tok.value}' exige une variable", op_tok.line, op_tok.source, op_tok.col)
                left = MLUnary(op_tok.value, left, False, op_tok)
                continue
            break

        while True:
            op = self.peek().value
            prec = self.PRECEDENCE.get(op, -1)
            if prec < min_prec:
                break
            op_tok = self.advance()
            right = self.parse_expression(prec + 1)
            left = MLBinary(op, left, right, op_tok)
            while self.peek().value in ("++", "--"):
                post = self.advance()
                if not isinstance(left, MLVar):
                    raise MiniLangCompileError(f"'{post.value}' exige une variable", post.line, post.source, post.col)
                left = MLUnary(post.value, left, False, post)
        return left


class MLReturnSignal(Exception):
    def __init__(self, value: Any): self.value = value
class MLBreakSignal(Exception): pass
class MLContinueSignal(Exception): pass
class MLExitSignal(Exception):
    def __init__(self, code: int): self.code = code


class MLEnv:
    def __init__(self, parent: Optional["MLEnv"] = None, runtime=None):
        self.parent = parent
        self.values: Dict[str, Any] = {}
        self.runtime = runtime if runtime is not None else (parent.runtime if parent else None)

    def declare(self, name: str, value: Any = 0):
        # MiniLang autorise la redéclaration dans le même scope :
        # la nouvelle valeur remplace simplement l'ancienne.
        self.values[name] = value

    def get(self, name: str):
        if name in self.values:
            return self.values[name]
        if self.parent:
            return self.parent.get(name)
        raise MiniLangCompileError(f"variable inconnue : {name}")

    def set(self, name: str, value: Any):
        if name in self.values:
            self.values[name] = value; return
        if self.parent:
            self.parent.set(name, value); return
        raise MiniLangCompileError(f"variable inconnue : {name}")


class MiniLang:
    """MiniLang 0.5: parser, interpréteur et compilateur VM32.

    Syntaxe prise en charge:
      let/affectations, nombres, chaînes, booléens, calculs, comparaisons,
      &&/||, if/else, while, for, break/continue, fonctions/return,
      print/exit, ++/--, commentaires # et //.
    """

    @staticmethod
    def parse(source: str) -> MLProgram:
        return MiniLangParser(source).parse()

    @staticmethod
    def _int_div(a: int, b: int) -> int:
        if b == 0:
            raise MiniLangCompileError("division par zéro")
        q = abs(int(a)) // abs(int(b))
        return -q if (a < 0) != (b < 0) else q

    @staticmethod
    def _truth(v: Any) -> bool:
        return bool(v)

    @staticmethod
    def _eval_expr(node: Any, env: MLEnv, functions: Dict[str, MLFunction], print_fn):
        if isinstance(node, MLLiteral):
            return node.value
        if isinstance(node, MLVar):
            return env.get(node.name)
        if isinstance(node, MLUnary):
            if node.op in ("++", "--"):
                if not isinstance(node.expr, MLVar):
                    raise MiniLangCompileError(f"'{node.op}' exige une variable", node.token.line, node.token.source, node.token.col)
                old = env.get(node.expr.name)
                if isinstance(old, str):
                    raise MiniLangCompileError("++/-- exige un entier", node.token.line, node.token.source, node.token.col)
                new = int(old) + (1 if node.op == "++" else -1)
                env.set(node.expr.name, new)
                return new if node.prefix else old
            value = MiniLang._eval_expr(node.expr, env, functions, print_fn)
            if node.op == "+": return +value
            if node.op == "-": return -value
            if node.op == "!": return not MiniLang._truth(value)
            if node.op == "~": return ~int(value)
            raise MiniLangCompileError(f"opérateur unaire inconnu : {node.op}", node.token.line, node.token.source, node.token.col)

        if isinstance(node, MLBinary):
            if node.op == "&&":
                left = MiniLang._eval_expr(node.left, env, functions, print_fn)
                return bool(left) and bool(MiniLang._eval_expr(node.right, env, functions, print_fn))
            if node.op == "||":
                left = MiniLang._eval_expr(node.left, env, functions, print_fn)
                return bool(left) or bool(MiniLang._eval_expr(node.right, env, functions, print_fn))
            a = MiniLang._eval_expr(node.left, env, functions, print_fn)
            b = MiniLang._eval_expr(node.right, env, functions, print_fn)
            op = node.op
            try:
                if op == "+":
                    if isinstance(a, str) or isinstance(b, str): return str(a) + str(b)
                    return int(a) + int(b)
                if op == "-": return int(a) - int(b)
                if op == "*": return int(a) * int(b)
                if op == "/": return MiniLang._int_div(int(a), int(b))
                if op == "%":
                    q = MiniLang._int_div(int(a), int(b)); return int(a) - q * int(b)
                if op == "==": return a == b
                if op == "!=": return a != b
                if op == "<": return a < b
                if op == "<=": return a <= b
                if op == ">": return a > b
                if op == ">=": return a >= b
                if op == "&": return int(a) & int(b)
                if op == "|": return int(a) | int(b)
                if op == "^": return int(a) ^ int(b)
                if op == "<<": return int(a) << (int(b) & 31)
                if op == ">>": return int(a) >> (int(b) & 31)
            except (TypeError, ValueError) as exc:
                raise MiniLangCompileError(f"opération invalide '{op}': {exc}", node.token.line, node.token.source, node.token.col)
            raise MiniLangCompileError(f"opérateur inconnu : {op}", node.token.line, node.token.source, node.token.col)

        if isinstance(node, MLCall):
            args = [MiniLang._eval_expr(x, env, functions, print_fn) for x in node.args]
            builtin_names = {
                "input", "inputInt", "len", "int", "str", "system", "env", "envSet",
                "exists", "isDir", "read", "write", "append", "mkdir", "remove", "copy", "move",
                "fileSize", "fileByte", "setFileByte", "list", "shell", "run", "sleep", "time",
                "timeMs", "random", "randomRange", "argc", "arg", "cwd", "chdir", "array",
                "arrayLen", "arrayGet", "arraySet", "read8", "read32", "write8", "write32",
                "substr", "replace", "contains", "startsWith", "endsWith", "lower", "upper",
                "trim", "chr", "ord", "ping", "httpGet", "httpPost", "httpDownload", "download", "pid", "program", "hostname", "memTotal",
                "memFree", "alloc", "free", "arrayGetStr", "importHost", "exportHost",
                "tcpConnect", "tcpSend", "tcpRecv", "tcpClose", "tcpIsOpen",
                "udpOpen", "udpSend", "udpRecv", "udpClose",
                "hostExists", "hostRead", "hostWrite", "hostAppend", "hostDelete", "hostMkdir",
                "hostList", "hostIsDir", "hostSize", "exec", "command", "sysf", "arraySetStr",
                "split", "join", "imageLoad", "imageDraw", "imageDrawScaled", "imageWidth", "imageHeight", "imageFree", "window", "clear", "pixel", "rect", "line", "circle",
                "text", "present", "close", "minimize", "keyDown", "keyPressed", "textInput", "mouseX", "mouseY", "mouseDown",
                "closeRequested", "windowAlive", "rgb"
            }
            if node.name in builtin_names:
                # L'interpréteur utilise le même runtime que les .mexe.
                return _ml_builtin(node.name, args, env.runtime, env)
            if node.name == "len":
                if len(args) != 1:
                    raise MiniLangCompileError("len() attend exactement 1 argument", node.token.line, node.token.source, node.token.col)
                return len(args[0])
            if node.name == "int":
                if len(args) != 1:
                    raise MiniLangCompileError("int() attend exactement 1 argument", node.token.line, node.token.source, node.token.col)
                return int(args[0])
            if node.name == "str":
                if len(args) != 1:
                    raise MiniLangCompileError("str() attend exactement 1 argument", node.token.line, node.token.source, node.token.col)
                return str(args[0])
            fn = functions.get(node.name)
            if not fn:
                raise MiniLangCompileError(f"fonction inconnue : {node.name}", node.token.line, node.token.source, node.token.col)
            if len(args) != len(fn.params):
                raise MiniLangCompileError(
                    f"{node.name}() attend {len(fn.params)} argument(s), reçu {len(args)}",
                    node.token.line, node.token.source, node.token.col
                )
            child = MLEnv(env, env.runtime)
            for name, value in zip(fn.params, args):
                child.declare(name, value)
            try:
                MiniLang._exec_block(fn.body, child, functions, print_fn)
            except MLReturnSignal as ret:
                return ret.value
            return 0

        raise MiniLangCompileError("nœud d'expression inconnu")

    @staticmethod
    def _exec_stmt(stmt: Any, env: MLEnv, functions: Dict[str, MLFunction], print_fn):
        if isinstance(stmt, MLLet):
            env.declare(stmt.name, 0 if stmt.expr is None else MiniLang._eval_expr(stmt.expr, env, functions, print_fn))
        elif isinstance(stmt, MLAssign):
            old = env.get(stmt.name)
            value = MiniLang._eval_expr(stmt.expr, env, functions, print_fn)
            if stmt.op != "=":
                base = stmt.op[0]
                value = MiniLang._eval_expr(MLBinary(base, MLLiteral(old, stmt.token), MLLiteral(value, stmt.token), stmt.token), env, functions, print_fn)
            env.set(stmt.name, value)
        elif isinstance(stmt, MLPrint):
            value = MiniLang._eval_expr(stmt.expr, env, functions, print_fn)
            end = "\n" if stmt.end_expr is None else str(MiniLang._eval_expr(stmt.end_expr, env, functions, print_fn))
            flush = True if stmt.flush_expr is None else bool(MiniLang._eval_expr(stmt.flush_expr, env, functions, print_fn))
            try:
                print_fn(value, end=end, flush=flush)
            except TypeError:
                # Compatible avec un print_fn personnalisé qui n'accepte qu'une valeur.
                print_fn(str(value) + end)
        elif isinstance(stmt, MLExit):
            raise MLExitSignal(int(MiniLang._eval_expr(stmt.expr, env, functions, print_fn)))
        elif isinstance(stmt, MLExprStmt):
            MiniLang._eval_expr(stmt.expr, env, functions, print_fn)
        elif isinstance(stmt, MLIf):
            block = stmt.then_block if MiniLang._truth(MiniLang._eval_expr(stmt.cond, env, functions, print_fn)) else stmt.else_block
            if block: MiniLang._exec_block(block, env, functions, print_fn)
        elif isinstance(stmt, MLWhile):
            while MiniLang._truth(MiniLang._eval_expr(stmt.cond, env, functions, print_fn)):
                try: MiniLang._exec_block(stmt.body, env, functions, print_fn)
                except MLContinueSignal: continue
                except MLBreakSignal: break
        elif isinstance(stmt, MLFor):
            if stmt.init: MiniLang._exec_stmt(stmt.init, env, functions, print_fn)
            while True:
                if stmt.cond is not None and not MiniLang._truth(MiniLang._eval_expr(stmt.cond, env, functions, print_fn)):
                    break
                try:
                    MiniLang._exec_block(stmt.body, env, functions, print_fn)
                except MLBreakSignal:
                    break
                except MLContinueSignal:
                    pass
                if stmt.update: MiniLang._exec_stmt(stmt.update, env, functions, print_fn)
        elif isinstance(stmt, MLBreak):
            raise MLBreakSignal()
        elif isinstance(stmt, MLContinue):
            raise MLContinueSignal()
        elif isinstance(stmt, MLReturn):
            value = 0 if stmt.expr is None else MiniLang._eval_expr(stmt.expr, env, functions, print_fn)
            raise MLReturnSignal(value)
        elif isinstance(stmt, MLFunction):
            return
        else:
            raise MiniLangCompileError(f"instruction interne inconnue: {type(stmt).__name__}")

    @staticmethod
    def _exec_block(block: MLBlock, env: MLEnv, functions: Dict[str, MLFunction], print_fn):
        for stmt in block.statements:
            MiniLang._exec_stmt(stmt, env, functions, print_fn)

    @staticmethod
    def run_source(source: str, print_fn=print) -> int:
        program = MiniLang.parse(source)
        functions = {s.name: s for s in program.statements if isinstance(s, MLFunction)}
        if len(functions) != sum(isinstance(s, MLFunction) for s in program.statements):
            # duplicate function names are caught here with a clearer message
            names = set()
            for s in program.statements:
                if isinstance(s, MLFunction):
                    if s.name in names:
                        raise MiniLangCompileError(f"fonction déjà déclarée : {s.name}", s.token.line, s.token.source, s.token.col)
                    names.add(s.name)
        env = MLEnv()
        try:
            for stmt in program.statements:
                if isinstance(stmt, MLFunction):
                    continue
                MiniLang._exec_stmt(stmt, env, functions, print_fn)
        except MLExitSignal as ex:
            return ex.code
        return 0


@dataclass
class MLSymbol:
    name: str
    storage: str              # global / local / param
    index: int
    type: str = "unknown"    # int / bool / string / array / unknown


class MLEmitter:
    def __init__(self):
        self.code = bytearray()
        self.data = bytearray()
        self.labels: Dict[str, int] = {}
        self.fixups: List[Tuple[int, str, str]] = []
        self.counter = 0
        self.string_pool: Dict[str, int] = {}

    def label(self, prefix: str = "L") -> str:
        name = f"{prefix}_{self.counter}"
        self.counter += 1
        return name

    def bind(self, name: str):
        if name in self.labels:
            raise RuntimeError(f"label dupliqué: {name}")
        self.labels[name] = len(self.code)

    def u8(self, x: int): self.code.append(x & 0xFF)
    def u16(self, x: int): self.code.extend(struct.pack(">H", x & 0xFFFF))
    def u32(self, x: int): self.code.extend(struct.pack(">I", x & WORD_MASK))

    def movi(self, reg: int, value: int):
        self.u8(CPU.MOVI); self.u8(reg); self.u32(value)

    def movi_data(self, reg: int, data_offset: int):
        self.u8(CPU.MOVI); self.u8(reg)
        pos = len(self.code); self.u32(0)
        self.fixups.append((pos, "data", str(data_offset)))

    def jump(self, opcode: int, label: str):
        self.u8(opcode)
        pos = len(self.code); self.u16(0)
        self.fixups.append((pos, "label", label))

    def call(self, label: str):
        self.jump(CPU.CALL, label)

    def add_string(self, value: str) -> int:
        if value in self.string_pool:
            return self.string_pool[value]
        off = len(self.data)
        blob = value.encode("utf-8") + b"\x00"
        self.data.extend(blob)
        self.string_pool[value] = off
        return off

    def finalize(self) -> MEXE:
        code_size = len(self.code)
        for pos, kind, target in self.fixups:
            if kind == "label":
                if target not in self.labels:
                    raise MiniLangCompileError(f"label introuvable: {target}")
                value = self.labels[target]
                if value > 0xFFFF:
                    raise MiniLangCompileError("programme trop grand : une adresse VM32 dépasse 16 bits")
                self.code[pos:pos + 2] = struct.pack(">H", value)
            else:
                value = code_size + int(target)
                self.code[pos:pos + 4] = struct.pack(">I", value & WORD_MASK)
        if len(self.code) > 0xFFFF:
            raise MiniLangCompileError("code VM32 trop grand (maximum 65535 octets)")
        # Le format MEXE2 actuel encode code/data sur 16 bits ; la RAM VM32 peut être
        # plus grande, mais un exécutable individuel reste limité par son format.
        if len(self.data) > 0xFFFF:
            raise MiniLangCompileError("section de données MEXE2 trop grande (maximum 65535 octets)")
        return MEXE(bytes(self.code), bytes(self.data), 0)



class MiniLangCompiler:
    # Zone globale haute mémoire, séparée du heap.
    GLOBAL_BASE = 0x00C00000

    # Source de vérité de toutes les fonctions natives MiniLang.
    # Format: nom -> (min_args, max_args, type_retour, syscall)
    BUILTIN_SPECS = {
            "input": (0, 1, "string", Syscalls.INPUT_STR),
            "inputInt": (0, 1, "int", Syscalls.INPUT_INT),
            "len": (1, 1, "int", None),
            "int": (1, 1, "int", Syscalls.STR_TO_INT),
            "str": (1, 1, "string", Syscalls.INT_TO_STR),
            "system": (1, 1, "string", Syscalls.SYSTEM_GET),
            "env": (1, 1, "string", Syscalls.ENV_GET),
            "envSet": (2, 2, "int", Syscalls.ENV_SET),
            "exists": (1, 1, "bool", Syscalls.FILE_EXISTS),
            "isDir": (1, 1, "bool", Syscalls.FILE_ISDIR),
            "read": (1, 1, "string", Syscalls.FILE_READ),
            "write": (2, 2, "int", Syscalls.FILE_WRITE),
            "append": (2, 2, "int", Syscalls.FILE_APPEND),
            "mkdir": (1, 2, "int", Syscalls.MKDIR),
            "remove": (1, 2, "int", Syscalls.FILE_DELETE),
            "copy": (2, 2, "int", Syscalls.FILE_COPY),
            "move": (2, 2, "int", Syscalls.FILE_MOVE),
            "fileSize": (1, 1, "int", Syscalls.FILE_SIZE),
            "fileByte": (2, 2, "int", Syscalls.FILE_READ_BYTE),
            "setFileByte": (3, 3, "int", Syscalls.FILE_WRITE_BYTE),
            "list": (1, 1, "string", Syscalls.LIST),
            "shell": (1, 1, "int", Syscalls.SHELL),
            "run": (1, 5, "int", Syscalls.RUN),
            "sleep": (1, 1, "int", Syscalls.SLEEP),
            "time": (0, 0, "int", Syscalls.TIME),
            "timeMs": (0, 0, "int", Syscalls.TIME_MS),
            "random": (1, 1, "int", Syscalls.RANDOM),
            "randomRange": (2, 2, "int", Syscalls.RANDOM_RANGE),
            "argc": (0, 0, "int", Syscalls.ARGC),
            "arg": (1, 1, "string", Syscalls.ARG),
            "cwd": (0, 0, "string", Syscalls.CWD),
            "chdir": (1, 1, "int", Syscalls.CHDIR),
            "array": (1, 1, "array", Syscalls.ARRAY_NEW),
            "arrayLen": (1, 1, "int", Syscalls.ARRAY_LEN),
            "arrayGet": (2, 2, "int", Syscalls.ARRAY_GET),
            "arraySet": (3, 3, "int", Syscalls.ARRAY_SET),
            "read8": (1, 1, "int", Syscalls.READ_MEM8),
            "read32": (1, 1, "int", Syscalls.READ_MEM32),
            "write8": (2, 2, "int", Syscalls.WRITE_MEM8),
            "write32": (2, 2, "int", Syscalls.WRITE_MEM32),
            "substr": (2, 3, "string", Syscalls.STR_SUBSTR),
            "replace": (3, 3, "string", Syscalls.STR_REPLACE),
            "contains": (2, 2, "bool", Syscalls.STR_CONTAINS),
            "startsWith": (2, 2, "bool", Syscalls.STR_STARTS),
            "endsWith": (2, 2, "bool", Syscalls.STR_ENDS),
            "lower": (1, 1, "string", Syscalls.STR_LOWER),
            "upper": (1, 1, "string", Syscalls.STR_UPPER),
            "trim": (1, 1, "string", Syscalls.STR_TRIM),
            "chr": (1, 1, "string", Syscalls.CHR),
            "ord": (1, 1, "int", Syscalls.ORD),
            "ping": (1, 1, "int", Syscalls.NET_PING),
            "httpGet": (1, 2, "string", Syscalls.HTTP_GET),
            "httpPost": (2, 4, "string", Syscalls.HTTP_POST),
            "httpDownload": (2, 3, "int", Syscalls.HTTP_DOWNLOAD),
            "download": (2, 3, "int", Syscalls.HTTP_DOWNLOAD),
            "dnsResolve": (1, 1, "string", Syscalls.DNS_RESOLVE),
            "tcpConnect": (2, 3, "int", Syscalls.TCP_CONNECT),
            "tcpSend": (2, 2, "int", Syscalls.TCP_SEND),
            "tcpRecv": (1, 3, "string", Syscalls.TCP_RECV),
            "tcpClose": (1, 1, "int", Syscalls.TCP_CLOSE),
            "tcpIsOpen": (1, 1, "bool", Syscalls.TCP_IS_OPEN),
            "udpOpen": (0, 0, "int", Syscalls.UDP_OPEN),
            "udpSend": (4, 4, "int", Syscalls.UDP_SEND),
            "udpRecv": (1, 3, "string", Syscalls.UDP_RECV),
            "udpClose": (1, 1, "int", Syscalls.UDP_CLOSE),
            "pid": (0, 0, "int", Syscalls.PID),
            "program": (0, 0, "string", Syscalls.PROGRAM),
            "hostname": (0, 0, "string", Syscalls.HOSTNAME),
            "memTotal": (0, 0, "int", Syscalls.MEM_TOTAL),
            "memFree": (0, 0, "int", Syscalls.MEM_FREE),
            "alloc": (1, 1, "int", Syscalls.ALLOC),
            "free": (1, 1, "int", Syscalls.FREE),
            "arrayGetStr": (2, 2, "string", Syscalls.ARRAY_GET_STR),
            "importHost": (2, 2, "int", Syscalls.IMPORT_HOST),
            "exportHost": (2, 2, "int", Syscalls.EXPORT_HOST),
            "hostExists": (1, 1, "bool", Syscalls.HOST_EXISTS),
            "hostRead": (1, 1, "string", Syscalls.HOST_READ),
            "hostWrite": (2, 2, "int", Syscalls.HOST_WRITE),
            "hostAppend": (2, 2, "int", Syscalls.HOST_APPEND),
            "hostDelete": (1, 1, "int", Syscalls.HOST_DELETE),
            "hostMkdir": (1, 1, "int", Syscalls.HOST_MKDIR),
            "hostList": (1, 1, "string", Syscalls.HOST_LIST),
            "hostIsDir": (1, 1, "bool", Syscalls.HOST_ISDIR),
            "hostSize": (1, 1, "int", Syscalls.HOST_SIZE),
            "exec": (1, 1, "string", Syscalls.EXEC_CAPTURE),
            "command": (1, 1, "int", Syscalls.SHELL),
            # sysf(nom, ...args) appelle dynamiquement une fonction système
            # native connue du compilateur. Le nom doit être une chaîne littérale
            # afin de connaître le type de retour et de produire du MEXE2 fiable.
            "sysf": (1, 6, "dynamic", None),
            "arraySetStr": (3, 3, "int", Syscalls.ARRAY_SET_STR),
            "split": (2, 2, "array", Syscalls.STR_SPLIT),
            "join": (2, 2, "string", Syscalls.STR_JOIN),
            "imageLoad": (1, 1, "int", Syscalls.GFX_IMAGE_LOAD),
            "imageDraw": (3, 3, "int", Syscalls.GFX_IMAGE_DRAW),
            "imageDrawScaled": (5, 5, "int", Syscalls.GFX_IMAGE_DRAW_SCALED),
            "imageWidth": (1, 1, "int", Syscalls.GFX_IMAGE_WIDTH),
            "imageHeight": (1, 1, "int", Syscalls.GFX_IMAGE_HEIGHT),
            "imageFree": (1, 1, "int", Syscalls.GFX_IMAGE_FREE),
            "window": (3, 3, "int", Syscalls.GFX_WINDOW),
            "clear": (1, 1, "int", Syscalls.GFX_CLEAR),
            "pixel": (3, 3, "int", Syscalls.GFX_PIXEL),
            "rect": (5, 5, "int", Syscalls.GFX_RECT),
            "line": (5, 5, "int", Syscalls.GFX_LINE),
            "circle": (4, 4, "int", Syscalls.GFX_CIRCLE),
            "text": (4, 4, "int", Syscalls.GFX_TEXT),
            "present": (0, 0, "int", Syscalls.GFX_PRESENT),
            "close": (0, 0, "int", Syscalls.GFX_CLOSE),
            "minimize": (0, 0, "int", Syscalls.GFX_MINIMIZE),
            "keyDown": (1, 1, "bool", Syscalls.GFX_KEY_DOWN),
            "keyPressed": (1, 1, "bool", Syscalls.GFX_KEY_PRESSED),
            "textInput": (0, 1, "string", Syscalls.GFX_TEXT_INPUT),
            "mouseX": (0, 0, "int", Syscalls.GFX_MOUSE_X),
            "mouseY": (0, 0, "int", Syscalls.GFX_MOUSE_Y),
            "mouseDown": (1, 1, "bool", Syscalls.GFX_MOUSE_DOWN),
            "closeRequested": (0, 0, "bool", Syscalls.GFX_CLOSE_REQUESTED),
            "windowAlive": (0, 0, "bool", Syscalls.GFX_ALIVE),
            "rgb": (3, 3, "int", Syscalls.GFX_RGB),
        }

    def __init__(self, program: MLProgram):
        self.program = program
        self.em = MLEmitter()
        self.globals: Dict[str, MLSymbol] = {}
        self.functions: Dict[str, MLFunction] = {}
        self.function_symbols: Dict[str, Dict[str, MLSymbol]] = {}
        self.function_local_counts: Dict[str, int] = {}
        self.function_return_types: Dict[str, str] = {}
        self.loop_stack: List[Tuple[str, str]] = []  # break, continue
        self.current_function: Optional[str] = None
        self.global_count = 0
        self.builtins = dict(self.BUILTIN_SPECS)

    def error(self, msg: str, token: MLToken):
        raise MiniLangCompileError(msg, token.line, token.source, token.col)

    def collect(self):
        for stmt in self.program.statements:
            if isinstance(stmt, MLFunction):
                if stmt.name in self.functions:
                    self.error(f"fonction déjà déclarée : {stmt.name}", stmt.token)
                self.functions[stmt.name] = stmt

        def collect_global_lets(node):
            if isinstance(node, MLLet):
                # Redéclarer une variable globale réutilise le même slot.
                # La nouvelle déclaration remplacera donc la valeur existante.
                if node.name not in self.globals:
                    self.globals[node.name] = MLSymbol(node.name, "global", self.global_count, "unknown")
                    self.global_count += 1
            elif isinstance(node, MLBlock):
                for x in node.statements: collect_global_lets(x)
            elif isinstance(node, MLIf):
                collect_global_lets(node.then_block)
                if node.else_block: collect_global_lets(node.else_block)
            elif isinstance(node, MLWhile):
                collect_global_lets(node.body)
            elif isinstance(node, MLFor):
                if node.init: collect_global_lets(node.init)
                collect_global_lets(node.body)

        for stmt in self.program.statements:
            if not isinstance(stmt, MLFunction):
                collect_global_lets(stmt)
        if self.global_count > 1024:
            raise MiniLangCompileError("trop de variables globales (maximum 1024)")

        for fn in self.functions.values():
            symbols: Dict[str, MLSymbol] = {}
            for i, name in enumerate(fn.params):
                symbols[name] = MLSymbol(name, "param", i, "unknown")
            locals_found: List[str] = []

            def walk(node):
                if isinstance(node, MLLet):
                    # Une redéclaration remplace la précédente.
                    # Si le nom correspond à un paramètre, on réutilise son slot.
                    if node.name in symbols:
                        return
                    if node.name not in locals_found:
                        locals_found.append(node.name)
                elif isinstance(node, MLBlock):
                    for x in node.statements: walk(x)
                elif isinstance(node, MLIf):
                    walk(node.then_block)
                    if node.else_block: walk(node.else_block)
                elif isinstance(node, MLWhile): walk(node.body)
                elif isinstance(node, MLFor):
                    if node.init: walk(node.init)
                    walk(node.body)

            walk(fn.body)
            for i, name in enumerate(locals_found):
                symbols[name] = MLSymbol(name, "local", i, "unknown")
            self.function_symbols[fn.name] = symbols
            self.function_local_counts[fn.name] = len(locals_found)
            self.function_return_types[fn.name] = self.infer_return_type(fn)

    def _merge_inferred_type(self, symbol: MLSymbol, new_type: str, token: Optional[MLToken] = None) -> bool:
        """Infère les paramètres sans les figer sur le premier appel.

        Un paramètre de fonction peut recevoir plusieurs types selon l'appel.
        Dès qu'un conflit apparaît, il devient ``dynamic`` au lieu de rendre
        les appels suivants incompatibles au niveau du compilateur.
        """
        if new_type in ("unknown", "dynamic", None):
            return False
        if symbol.type == new_type:
            return False
        if symbol.type in ("unknown", "dynamic"):
            if symbol.type == "dynamic":
                return False
            symbol.type = new_type
            return True
        symbol.type = "dynamic"
        return True

    def infer_function_types(self):
        """Infère les types des paramètres à partir des appels réels.

        Le VM32 stocke tous les paramètres dans des mots de 32 bits. Une
        chaîne est donc une adresse VM32, mais elle doit rester typée String
        au niveau du compilateur pour être imprimée/lue comme du texte. Cette
        passe pré-calculée évite que l'ordre des déclarations des fonctions
        change le résultat.
        """
        def symbols_for(fn_name: Optional[str]):
            if fn_name is None:
                return self.globals
            return self.function_symbols.get(fn_name, self.globals)

        def walk_expr(node: Any, fn_name: Optional[str]):
            changed = False
            if node is None:
                return False
            if isinstance(node, MLCall):
                target = self.functions.get(node.name)
                if target is not None:
                    target_symbols = self.function_symbols.get(node.name, {})
                    caller_symbols = symbols_for(fn_name)
                    for i, arg in enumerate(node.args):
                        if i >= len(target.params):
                            break
                        typ = self.estimate_type(arg, caller_symbols)
                        if typ != "unknown":
                            changed |= self._merge_inferred_type(
                                target_symbols[target.params[i]], typ, node.token
                            )
                for arg in node.args:
                    changed |= walk_expr(arg, fn_name)
                return changed
            if isinstance(node, MLBinary):
                changed |= walk_expr(node.left, fn_name)
                changed |= walk_expr(node.right, fn_name)
            elif isinstance(node, MLUnary):
                changed |= walk_expr(node.expr, fn_name)
            elif isinstance(node, MLIndex):
                changed |= walk_expr(node.target, fn_name)
                changed |= walk_expr(node.index, fn_name)
            return changed

        def walk_block(block: MLBlock, fn_name: Optional[str]):
            changed = False
            symbols = symbols_for(fn_name)
            for stmt in block.statements:
                if isinstance(stmt, MLLet):
                    sym = (self.globals.get(stmt.name) if fn_name is None
                           else self.function_symbols.get(fn_name, {}).get(stmt.name))
                    if sym is not None and stmt.expr is not None:
                        changed |= walk_expr(stmt.expr, fn_name)
                        typ = self.estimate_type(stmt.expr, symbols)
                        changed |= self._merge_inferred_type(sym, typ, stmt.token)
                elif isinstance(stmt, MLAssign):
                    changed |= walk_expr(stmt.expr, fn_name)
                    sym = symbols.get(stmt.name)
                    if sym is not None:
                        typ = self.estimate_type(stmt.expr, symbols)
                        changed |= self._merge_inferred_type(sym, typ, stmt.token)
                elif isinstance(stmt, MLIndexAssign):
                    changed |= walk_expr(stmt.target, fn_name)
                    changed |= walk_expr(stmt.index, fn_name)
                    changed |= walk_expr(stmt.expr, fn_name)
                elif isinstance(stmt, MLPrint):
                    changed |= walk_expr(stmt.expr, fn_name)
                    changed |= walk_expr(stmt.end_expr, fn_name)
                    changed |= walk_expr(stmt.flush_expr, fn_name)
                elif isinstance(stmt, MLReturn):
                    changed |= walk_expr(stmt.expr, fn_name)
                elif isinstance(stmt, MLExprStmt):
                    changed |= walk_expr(stmt.expr, fn_name)
                elif isinstance(stmt, MLIf):
                    changed |= walk_expr(stmt.cond, fn_name)
                    changed |= walk_block(stmt.then_block, fn_name)
                    if stmt.else_block:
                        changed |= walk_block(stmt.else_block, fn_name)
                elif isinstance(stmt, MLWhile):
                    changed |= walk_expr(stmt.cond, fn_name)
                    changed |= walk_block(stmt.body, fn_name)
                elif isinstance(stmt, MLFor):
                    if stmt.init:
                        if isinstance(stmt.init, (MLLet, MLAssign)):
                            changed |= walk_block(MLBlock([stmt.init]), fn_name)
                        else:
                            changed |= walk_expr(getattr(stmt.init, "expr", None), fn_name)
                    changed |= walk_expr(stmt.cond, fn_name)
                    changed |= walk_block(stmt.body, fn_name)
                    if stmt.update:
                        changed |= walk_expr(getattr(stmt.update, "expr", None), fn_name)
            return changed

        # Plusieurs passes permettent de propager A(a) -> B(a) -> C("texte")
        # indépendamment de l'ordre des déclarations des fonctions.
        for _ in range(max(4, len(self.functions) * 4 + 2)):
            changed = False
            for stmt in self.program.statements:
                if isinstance(stmt, MLFunction):
                    changed |= walk_block(stmt.body, stmt.name)
                else:
                    if isinstance(stmt, MLBlock):
                        changed |= walk_block(stmt, None)
                    elif isinstance(stmt, (MLLet, MLAssign, MLExprStmt, MLPrint, MLReturn)):
                        changed |= walk_block(MLBlock([stmt]), None)
                    elif isinstance(stmt, MLIf):
                        changed |= walk_expr(stmt.cond, None)
                        changed |= walk_block(stmt.then_block, None)
                        if stmt.else_block:
                            changed |= walk_block(stmt.else_block, None)
                    elif isinstance(stmt, MLWhile):
                        changed |= walk_expr(stmt.cond, None)
                        changed |= walk_block(stmt.body, None)
                    elif isinstance(stmt, MLFor):
                        changed |= walk_block(stmt.body, None)
            for fn_name, fn in self.functions.items():
                inferred = self.infer_return_type(fn)
                if inferred != self.function_return_types.get(fn_name):
                    self.function_return_types[fn_name] = inferred
                    changed = True
            if not changed:
                break

    def infer_return_type(self, fn: MLFunction) -> str:
        found = []
        def walk(node):
            if isinstance(node, MLReturn):
                if node.expr is not None:
                    found.append(self.estimate_type(node.expr, self.function_symbols.get(fn.name, {})))
            elif isinstance(node, MLBlock):
                for x in node.statements: walk(x)
            elif isinstance(node, MLIf):
                walk(node.then_block)
                if node.else_block: walk(node.else_block)
            elif isinstance(node, MLWhile): walk(node.body)
            elif isinstance(node, MLFor):
                if node.init: walk(node.init)
                if node.update: walk(node.update)
                walk(node.body)
        # Symbols are already present after collect; call only once locals are added.
        walk(fn.body)
        real = [x for x in found if x != "unknown"]
        if not real:
            # Une fonction sans retour concret reste indéfinie tant que ses
            # paramètres ne sont pas inférés. Cela évite de figer trop tôt une
            # valeur String comme un entier.
            return "unknown" if found else "int"
        if any(x != real[0] for x in real):
            self.error("une fonction ne peut pas retourner des types différents dans le backend VM32", fn.token)
        return real[0]

    def estimate_type(self, node: Any, symbols: Dict[str, MLSymbol]) -> str:
        if isinstance(node, MLLiteral):
            if isinstance(node.value, bool): return "bool"
            if isinstance(node.value, str): return "string"
            return "int"
        if isinstance(node, MLVar):
            if node.name in symbols: return symbols[node.name].type
            if node.name in self.globals: return self.globals[node.name].type
            return "unknown"
        if isinstance(node, MLUnary):
            return "bool" if node.op == "!" else self.estimate_type(node.expr, symbols)
        if isinstance(node, MLBinary):
            if node.op in ("==", "!=", "<", "<=", ">", ">=", "&&", "||"): return "bool"
            a = self.estimate_type(node.left, symbols); b = self.estimate_type(node.right, symbols)
            if node.op == "+" and (a == "string" or b == "string"): return "string"
            return "int" if a != "string" and b != "string" else "unknown"
        if isinstance(node, MLIndex):
            target_t = self.estimate_type(node.target, symbols)
            return "string" if target_t == "string" else "int"
        if isinstance(node, MLCall):
            if node.name in self.builtins:
                return self.builtins[node.name][2]
            return self.function_return_types.get(node.name, "unknown")
        return "unknown"

    def symbol(self, name: str, token: MLToken) -> MLSymbol:
        if self.current_function and name in self.function_symbols[self.current_function]:
            return self.function_symbols[self.current_function][name]
        if name in self.globals:
            return self.globals[name]
        self.error(f"variable inconnue : {name} (utilisez 'let {name} = ...')", token)

    def check_numeric(self, typ: str, token: MLToken, what: str = "opération"):
        if typ == "string":
            self.error(f"{what} exige un entier, pas une chaîne", token)

    def emit_load_symbol(self, sym: MLSymbol):
        if sym.storage == "global":
            self.em.movi(6, self.GLOBAL_BASE + sym.index * 4)
        elif sym.storage == "local":
            self.em.code += bytes([CPU.MOVR, 6, 7])
            self.em.movi(1, (sym.index + 1) * 4)
            self.em.code += bytes([CPU.SUB, 6, 1])
        else:  # param
            self.em.code += bytes([CPU.MOVR, 6, 7])
            self.em.movi(1, 8 + sym.index * 4)
            self.em.code += bytes([CPU.ADD, 6, 1])
        self.em.code += bytes([CPU.LOAD32, 0, 6])

    def emit_store_symbol(self, sym: MLSymbol):
        if sym.storage == "global":
            self.em.movi(6, self.GLOBAL_BASE + sym.index * 4)
        elif sym.storage == "local":
            self.em.code += bytes([CPU.MOVR, 6, 7])
            self.em.movi(1, (sym.index + 1) * 4)
            self.em.code += bytes([CPU.SUB, 6, 1])
        else:
            self.em.code += bytes([CPU.MOVR, 6, 7])
            self.em.movi(1, 8 + sym.index * 4)
            self.em.code += bytes([CPU.ADD, 6, 1])
        self.em.code += bytes([CPU.STORE32, 0, 6])

    def emit_builtin_call(self, node: MLCall, call_args: Optional[List[Any]] = None) -> str:
        spec = self.builtins.get(node.name)
        if spec is None:
            self.error(f"fonction inconnue : {node.name}", node.token)
        amin, amax, rtype, syscall = spec
        args = node.args if call_args is None else call_args
        if not (amin <= len(args) <= amax):
            if amin == amax:
                self.error(f"{node.name}() attend {amin} argument(s), reçu {len(args)}", node.token)
            self.error(f"{node.name}() attend entre {amin} et {amax} arguments, reçu {len(args)}", node.token)

        if node.name == "sysf":
            # Appel indirect d'une fonction système MiniLang native.
            # La résolution statique permet de conserver le vrai type de retour
            # (string/int/bool/array) et donc de rester compatible avec PRINT_STR,
            # la concaténation et les affectations typées.
            if not args or not isinstance(args[0], MLLiteral) or not isinstance(args[0].value, str):
                self.error(
                    "sysf() exige en premier argument le nom littéral d'une fonction système, "
                    "par exemple sysf(\"write\", \"/tmp/x.txt\", \"bonjour\")",
                    node.token,
                )
            target_name = args[0].value
            target = self.builtins.get(target_name)
            if target is None or target_name == "sysf":
                self.error(f"fonction système inconnue pour sysf : {target_name}", node.token)
            # Réutilise exactement le chemin de compilation de la fonction native cible.
            target_call = MLCall(target_name, args[1:], node.token)
            return self.emit_builtin_call(target_call)

        if node.name in ("input", "inputInt"):
            # Prompt optionnel : input() lit l'entrée standard sans afficher de prompt.
            if len(args) == 0:
                self.em.movi(1, 0)
            else:
                self.compile_expr(args[0])
                self.em.code += bytes([CPU.MOVR, 1, 0])
            self.em.code += bytes([CPU.SYSCALL, syscall])
            return rtype
        if node.name == "len":
            if not args: self.error("len() attend un argument", node.token)
            typ = self.estimate_type(args[0], self.function_symbols.get(self.current_function, {}) if self.current_function else self.globals)
            self.compile_expr(args[0])
            self.em.code += bytes([CPU.MOVR, 1, 0, CPU.SYSCALL, Syscalls.ARRAY_LEN if typ == "array" else Syscalls.STR_LEN])
            return "int"
        if node.name == "int":
            typ = self.compile_expr(args[0])
            if typ != "string":
                return "int"
        elif node.name == "str":
            typ = self.compile_expr(args[0])
            if typ == "string":
                return "string"
            if typ == "dynamic":
                self.em.code += bytes([CPU.SYSCALL, Syscalls.VALUE_TO_STR])
                return "string"
        else:
            # Builtin run() has up to five arguments; all others are fixed/overloaded.
            for arg in reversed(args):
                self.compile_expr(arg)
                self.em.code += bytes([CPU.PUSH, 0])
            for reg in range(1, len(args) + 1):
                self.em.code += bytes([CPU.POP, reg])

            # substr(text, debut[, longueur]) : le syscall attend toujours R3.
            # Quand longueur est absente, on lui fournit -1 pour demander
            # "jusqu'a la fin". Sinon R3 pouvait contenir une ancienne valeur
            # (souvent 0), ce qui produisait une chaine vide.
            if node.name == "substr" and len(args) == 2:
                self.em.movi(3, 0xFFFFFFFF)

            # Les arguments optionnels utilisent des registres fixes : ils doivent
            # être remis à zéro pour ne pas réutiliser une ancienne valeur VM32.
            if node.name == "httpGet" and len(args) == 1:
                self.em.movi(2, 0)
            elif node.name == "httpPost":
                if len(args) == 2:
                    self.em.movi(3, 0)
                    self.em.movi(4, 0)
                elif len(args) == 3:
                    self.em.movi(4, 0)
            elif node.name in ("httpDownload", "download") and len(args) == 2:
                self.em.movi(3, 0)

            self.em.code += bytes([CPU.SYSCALL, syscall])
            return rtype
        syscall = Syscalls.STR_TO_INT if node.name == "int" else Syscalls.INT_TO_STR
        self.em.code += bytes([CPU.MOVR, 1, 0, CPU.SYSCALL, syscall])
        return rtype

    def compile_expr(self, node: Any) -> str:
        if isinstance(node, MLLiteral):
            if isinstance(node.value, str):
                self.em.movi_data(0, self.em.add_string(node.value))
                return "string"
            self.em.movi(0, int(node.value))
            return "bool" if isinstance(node.value, bool) else "int"

        if isinstance(node, MLVar):
            sym = self.symbol(node.name, node.token)
            self.emit_load_symbol(sym)
            return sym.type

        if isinstance(node, MLIndex):
            target_t = self.compile_expr(node.target)
            self.em.code += bytes([CPU.PUSH, 0])
            self.compile_expr(node.index)
            self.em.code += bytes([CPU.POP, 1, CPU.MOVR, 2, 0])
            if target_t == "string":
                self.em.code += bytes([CPU.SYSCALL, Syscalls.STR_CHAR])
                return "string"
            self.em.code += bytes([CPU.SYSCALL, Syscalls.ARRAY_GET])
            return "int"

        if isinstance(node, MLUnary):
            if node.op in ("++", "--"):
                if not isinstance(node.expr, MLVar):
                    self.error(f"'{node.op}' exige une variable", node.token)
                sym = self.symbol(node.expr.name, node.expr.token)
                self.check_numeric(sym.type, node.token, f"'{node.op}'")
                if not node.prefix:
                    self.em.code += bytes([CPU.PUSH, 0])
                self.emit_load_symbol(sym)
                self.em.code += bytes([CPU.INC if node.op == "++" else CPU.DEC, 0])
                self.emit_store_symbol(sym)
                if not node.prefix:
                    self.em.code += bytes([CPU.POP, 1])
                    self.em.code += bytes([CPU.MOVR, 0, 1])
                return sym.type if sym.type != "unknown" else "int"
            typ = self.compile_expr(node.expr)
            if node.op == "!":
                self.check_numeric(typ, node.token, "'!'")
                l_true = self.em.label("not_true"); l_end = self.em.label("not_end")
                self.em.movi(1, 0); self.em.code += bytes([CPU.CMP, 0, 1]); self.em.jump(CPU.JZ, l_true)
                self.em.movi(0, 0); self.em.jump(CPU.JMP, l_end)
                self.em.bind(l_true); self.em.movi(0, 1); self.em.bind(l_end)
                return "bool"
            self.check_numeric(typ, node.token, f"'{node.op}'")
            if node.op == "+": return "int"
            if node.op == "-":
                self.em.movi(1, 0); self.em.code += bytes([CPU.SUB, 1, 0, CPU.MOVR, 0, 1])
                return "int"
            if node.op == "~":
                self.em.code += bytes([CPU.NOT, 0])
                return "int"
            self.error(f"opérateur unaire non supporté : {node.op}", node.token)

        if isinstance(node, MLBinary):
            op = node.op
            if op in ("&&", "||"):
                lt = self.compile_expr(node.left); self.check_numeric(lt, node.token, f"'{op}'")
                l_short = self.em.label("logic_short"); l_end = self.em.label("logic_end")
                self.em.movi(1, 0); self.em.code += bytes([CPU.CMP, 0, 1])
                self.em.jump(CPU.JZ if op == "&&" else CPU.JNZ, l_short)
                rt = self.compile_expr(node.right); self.check_numeric(rt, node.token, f"'{op}'")
                self.em.movi(1, 0); self.em.code += bytes([CPU.CMP, 0, 1])
                self.em.jump(CPU.JZ if op == "&&" else CPU.JNZ, l_short)
                # Si on arrive ici, les deux côtés étaient vrais pour &&
                # (résultat 1), ou les deux côtés étaient faux pour || (résultat 0).
                self.em.movi(0, 1 if op == "&&" else 0); self.em.jump(CPU.JMP, l_end)
                self.em.bind(l_short); self.em.movi(0, 0 if op == "&&" else 1); self.em.bind(l_end)
                return "bool"

            left_t = self.estimate_type(node.left, self.function_symbols.get(self.current_function, {}) if self.current_function else self.globals)
            right_t = self.estimate_type(node.right, self.function_symbols.get(self.current_function, {}) if self.current_function else self.globals)

            if op == "+" and (left_t == "dynamic" or right_t == "dynamic"):
                self.compile_expr(node.left); self.em.code += bytes([CPU.PUSH, 0])
                self.compile_expr(node.right); self.em.code += bytes([CPU.PUSH, 0])
                self.em.code += bytes([CPU.POP, 2, CPU.POP, 1, CPU.SYSCALL, Syscalls.VALUE_ADD])
                return "dynamic"

            if op == "+" and (left_t == "string" or right_t == "string"):
                self.compile_expr(node.left); self.em.code += bytes([CPU.PUSH, 0])
                self.compile_expr(node.right); self.em.code += bytes([CPU.PUSH, 0])
                self.em.code += bytes([CPU.POP, 2, CPU.POP, 1, CPU.SYSCALL, Syscalls.STR_CONCAT])
                return "string"

            if left_t == "dynamic" or right_t == "dynamic":
                if op not in ("==", "!="):
                    self.error("opération dynamique supportée uniquement avec +, == ou !=", node.token)
                self.compile_expr(node.left); self.em.code += bytes([CPU.PUSH, 0])
                self.compile_expr(node.right); self.em.code += bytes([CPU.PUSH, 0])
                self.em.code += bytes([CPU.POP, 2, CPU.POP, 1, CPU.SYSCALL, Syscalls.VALUE_EQ])
                if op == "!=":
                    self.em.movi(1, 1); self.em.code += bytes([CPU.XOR, 0, 1])
                return "bool"

            if left_t == "string" or right_t == "string":
                if op not in ("==", "!="):
                    self.error("opération impossible entre chaînes (utilisez +, ==, != et les fonctions texte)", node.token)
                self.compile_expr(node.left); self.em.code += bytes([CPU.PUSH, 0])
                self.compile_expr(node.right); self.em.code += bytes([CPU.PUSH, 0])
                self.em.code += bytes([CPU.POP, 2, CPU.POP, 1, CPU.SYSCALL, Syscalls.STR_EQ])
                if op == "!=":
                    self.em.movi(1, 1); self.em.code += bytes([CPU.XOR, 0, 1])
                return "bool"

            self.compile_expr(node.left); self.em.code += bytes([CPU.PUSH, 0])
            self.compile_expr(node.right); self.em.code += bytes([CPU.MOVR, 1, 0, CPU.POP, 0])
            self.check_numeric(left_t, node.token, "opération")
            self.check_numeric(right_t, node.token, "opération")
            if op in ("+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>"):
                opcode = {
                    "+": CPU.ADD, "-": CPU.SUB, "*": CPU.MUL, "/": CPU.DIV, "%": CPU.MOD,
                    "&": CPU.AND, "|": CPU.OR, "^": CPU.XOR, "<<": CPU.SHL, ">>": CPU.SHR
                }[op]
                self.em.code += bytes([opcode, 0, 1])
                return "int"
            if op in ("==", "!=", "<", "<=", ">", ">="):
                self.em.code += bytes([CPU.CMP, 0, 1])
                l_true = self.em.label("cmp_true"); l_end = self.em.label("cmp_end")
                jop = {"==": CPU.JZ, "!=": CPU.JNZ, "<": CPU.JLT, "<=": CPU.JLE, ">": CPU.JGT, ">=": CPU.JGE}[op]
                self.em.jump(jop, l_true)
                self.em.movi(0, 0); self.em.jump(CPU.JMP, l_end)
                self.em.bind(l_true); self.em.movi(0, 1); self.em.bind(l_end)
                return "bool"
            self.error(f"opérateur non supporté : {op}", node.token)

        if isinstance(node, MLCall):
            if node.name in self.builtins:
                return self.emit_builtin_call(node)
            fn = self.functions.get(node.name)
            if not fn:
                self.error(f"fonction inconnue : {node.name}", node.token)
            if len(node.args) != len(fn.params):
                self.error(f"{node.name}() attend {len(fn.params)} argument(s), reçu {len(node.args)}", node.token)
            # Tous les paramètres occupent un mot VM32, mais leur type statique
            # doit être conservé pour que le corps sache qu'une valeur numérique
            # peut en réalité être une adresse de chaîne. L'inférence en amont
            # renseigne normalement déjà ces types; on les renforce ici avec les
            # types réellement rencontrés à cet appel.
            target_symbols = self.function_symbols.get(node.name, {})
            arg_types = [self.estimate_type(arg, self.function_symbols.get(self.current_function, {}) if self.current_function else self.globals) for arg in node.args]
            for idx, typ in enumerate(arg_types):
                if idx < len(fn.params) and typ != "unknown":
                    self._merge_inferred_type(target_symbols[fn.params[idx]], typ, node.token)
            for arg in reversed(node.args):
                self.compile_expr(arg)
                self.em.code += bytes([CPU.PUSH, 0])
            self.em.call(self._function_label(node.name))
            for _ in node.args:
                self.em.code += bytes([CPU.POP, 6])
            result_type = self.infer_return_type(fn)
            self.function_return_types[node.name] = result_type
            return result_type

        self.error(f"expression non supportée : {type(node).__name__}", getattr(node, "token", MLToken("", "", 0, 0, "")))

    def _function_label(self, name: str) -> str:
        return f"func_{name}"

    def compile_stmt(self, stmt: Any, allow_return: bool = False):
        if isinstance(stmt, MLLet):
            sym = self.symbol(stmt.name, stmt.token)
            if stmt.expr is None:
                self.em.movi(0, 0)
                sym.type = "int" if sym.type == "unknown" else sym.type
            else:
                typ = self.compile_expr(stmt.expr)
                if sym.type == "unknown": sym.type = typ
                elif typ != sym.type and not (sym.type == "int" and typ == "bool"):
                    self.error(f"type incompatible pour {stmt.name}: {sym.type} <- {typ}", stmt.token)
            self.emit_store_symbol(sym)
            return

        if isinstance(stmt, MLAssign):
            sym = self.symbol(stmt.name, stmt.token)
            if stmt.op != "=":
                rhs_t = self.compile_expr(stmt.expr)
                if stmt.op == "+=" and (sym.type == "string" or rhs_t == "string"):
                    self.em.code += bytes([CPU.PUSH, 0])
                    self.emit_load_symbol(sym)
                    # Pile: RHS puis ancienne valeur. On dépile donc d'abord
                    # l'ancienne valeur en R1, puis RHS en R2 afin que
                    # STR_CONCAT construise bien ancienne + RHS (et non RHS + ancienne).
                    self.em.code += bytes([CPU.PUSH, 0, CPU.POP, 1, CPU.POP, 2, CPU.SYSCALL, Syscalls.STR_CONCAT])
                    typ = "string"
                else:
                    self.check_numeric(sym.type if sym.type != "unknown" else rhs_t, stmt.token, "affectation composée")
                    self.check_numeric(rhs_t, stmt.token, "affectation composée")
                    self.em.code += bytes([CPU.PUSH, 0])
                    self.emit_load_symbol(sym)
                    self.em.code += bytes([CPU.POP, 1])
                    opcode = {"+=": CPU.ADD, "-=": CPU.SUB, "*=": CPU.MUL, "/=": CPU.DIV, "%=": CPU.MOD}[stmt.op]
                    self.em.code += bytes([opcode, 0, 1])
                    typ = "int"
            else:
                typ = self.compile_expr(stmt.expr)
            if sym.type == "unknown": sym.type = typ
            elif stmt.op == "=" and sym.type != typ and not (sym.type == "int" and typ == "bool"):
                self.error(f"type incompatible pour {stmt.name}: {sym.type} <- {typ}", stmt.token)
            self.emit_store_symbol(sym)
            return

        if isinstance(stmt, MLIndexAssign):
            target_t = self.compile_expr(stmt.target)
            if target_t != "array":
                self.error("une affectation par index exige un tableau créé avec array()", stmt.token)
            self.em.code += bytes([CPU.PUSH, 0])
            self.compile_expr(stmt.index)
            self.em.code += bytes([CPU.PUSH, 0])
            self.compile_expr(stmt.expr)
            self.em.code += bytes([CPU.PUSH, 0, CPU.POP, 3, CPU.POP, 2, CPU.POP, 1])
            if stmt.op != "=":
                # R1=tableau, R2=index, R3=nouvelle valeur.
                self.em.code += bytes([CPU.MOVR, 4, 3, CPU.SYSCALL, Syscalls.ARRAY_GET])
                opcode = {"+=": CPU.ADD, "-=": CPU.SUB, "*=": CPU.MUL, "/=": CPU.DIV, "%=": CPU.MOD}.get(stmt.op)
                if opcode is None: self.error(f"affectation {stmt.op} non supportée sur un tableau", stmt.token)
                self.em.code += bytes([opcode, 0, 4, CPU.MOVR, 3, 0])
            self.em.code += bytes([CPU.SYSCALL, Syscalls.ARRAY_SET])
            return

        if isinstance(stmt, MLPrint):
            typ = self.compile_expr(stmt.expr)

            # print(expr) garde le comportement historique: une ligne par appel.
            if stmt.end_expr is None:
                if stmt.flush_expr is not None:
                    # Le runtime VM32 écrit immédiatement: flush=True n'a donc rien
                    # de supplémentaire à faire, mais on l'accepte pour faciliter la
                    # conversion de code Python vers MiniLang.
                    flush_t = self.compile_expr(stmt.flush_expr)
                    self.check_numeric(flush_t, stmt.token, "print(flush=...)")
                if typ == "string":
                    self.em.code += bytes([CPU.SYSCALL, Syscalls.PRINT_STR])
                elif typ == "dynamic":
                    self.em.code += bytes([CPU.SYSCALL, Syscalls.VALUE_PRINT])
                else:
                    self.em.code += bytes([CPU.PRINT, 0])
                return

            # print(expr, end=...) : le backend VM32 sort une chaîne sans ajouter
            # automatiquement de retour à la ligne. Pour un entier, on le convertit
            # d'abord en chaîne.
            if typ != "string":
                if typ == "dynamic":
                    self.em.code += bytes([CPU.SYSCALL, Syscalls.VALUE_TO_STR])
                else:
                    self.em.code += bytes([CPU.MOVR, 1, 0, CPU.SYSCALL, Syscalls.INT_TO_STR])
                typ = "string"

            # Sauvegarde de la valeur, compilation de end, puis R0=value/R1=end.
            self.em.code += bytes([CPU.PUSH, 0])
            end_t = self.compile_expr(stmt.end_expr)
            if end_t != "string":
                self.error("print(..., end=...) exige une chaîne", stmt.token)
            self.em.code += bytes([CPU.MOVR, 1, 0, CPU.POP, 0, CPU.SYSCALL, Syscalls.PRINT_STR_END])

            if stmt.flush_expr is not None:
                # flush=True est accepté comme option de compatibilité; les sorties
                # miniOS sont déjà flushées par le syscall.
                flush_t = self.compile_expr(stmt.flush_expr)
                self.check_numeric(flush_t, stmt.token, "print(flush=...)")
            return

        if isinstance(stmt, MLExit):
            typ = self.compile_expr(stmt.expr); self.check_numeric(typ, stmt.token, "exit")
            self.em.code += bytes([CPU.SYSCALL, Syscalls.EXIT])
            return

        if isinstance(stmt, MLExprStmt):
            self.compile_expr(stmt.expr)
            return

        if isinstance(stmt, MLIf):
            typ = self.compile_expr(stmt.cond); self.check_numeric(typ, stmt.token, "condition")
            l_else = self.em.label("if_else"); l_end = self.em.label("if_end")
            self.em.movi(1, 0); self.em.code += bytes([CPU.CMP, 0, 1]); self.em.jump(CPU.JZ, l_else)
            for x in stmt.then_block.statements: self.compile_stmt(x, allow_return)
            if stmt.else_block:
                self.em.jump(CPU.JMP, l_end); self.em.bind(l_else)
                for x in stmt.else_block.statements: self.compile_stmt(x, allow_return)
                self.em.bind(l_end)
            else:
                self.em.bind(l_else)
            return

        if isinstance(stmt, MLWhile):
            l_cond = self.em.label("while_cond"); l_end = self.em.label("while_end")
            self.em.bind(l_cond)
            typ = self.compile_expr(stmt.cond); self.check_numeric(typ, stmt.token, "condition")
            self.em.movi(1, 0); self.em.code += bytes([CPU.CMP, 0, 1]); self.em.jump(CPU.JZ, l_end)
            self.loop_stack.append((l_end, l_cond))
            for x in stmt.body.statements: self.compile_stmt(x, allow_return)
            self.loop_stack.pop()
            self.em.jump(CPU.JMP, l_cond); self.em.bind(l_end)
            return

        if isinstance(stmt, MLFor):
            if stmt.init: self.compile_stmt(stmt.init, allow_return)
            l_cond = self.em.label("for_cond"); l_update = self.em.label("for_update"); l_end = self.em.label("for_end")
            self.em.bind(l_cond)
            if stmt.cond is not None:
                typ = self.compile_expr(stmt.cond); self.check_numeric(typ, stmt.token, "condition")
                self.em.movi(1, 0); self.em.code += bytes([CPU.CMP, 0, 1]); self.em.jump(CPU.JZ, l_end)
            self.loop_stack.append((l_end, l_update))
            for x in stmt.body.statements: self.compile_stmt(x, allow_return)
            self.loop_stack.pop()
            self.em.bind(l_update)
            if stmt.update: self.compile_stmt(stmt.update, allow_return)
            self.em.jump(CPU.JMP, l_cond); self.em.bind(l_end)
            return

        if isinstance(stmt, MLBreak):
            if not self.loop_stack: self.error("'break' utilisé hors d'une boucle", stmt.token)
            self.em.jump(CPU.JMP, self.loop_stack[-1][0]); return

        if isinstance(stmt, MLContinue):
            if not self.loop_stack: self.error("'continue' utilisé hors d'une boucle", stmt.token)
            self.em.jump(CPU.JMP, self.loop_stack[-1][1]); return

        if isinstance(stmt, MLReturn):
            if not allow_return:
                self.error("'return' utilisé en dehors d'une fonction", stmt.token)
            if stmt.expr is None:
                self.em.movi(0, 0)
            else:
                self.compile_expr(stmt.expr)
            self.emit_function_epilogue()
            return

        if isinstance(stmt, MLFunction):
            self.error("déclaration de fonction à un endroit invalide", stmt.token)

        self.error(f"instruction non supportée : {type(stmt).__name__}", getattr(stmt, "token", MLToken("", "", 0, 0, "")))

    def emit_function_epilogue(self):
        count = self.function_local_counts.get(self.current_function or "", 0)
        for _ in range(count): self.em.code += bytes([CPU.POP, 6])
        self.em.code += bytes([CPU.POP, 7, CPU.RET])

    def compile(self) -> MEXE:
        self.collect()
        self.infer_function_types()

        # Main program first.
        self.current_function = None
        for stmt in self.program.statements:
            if isinstance(stmt, MLFunction): continue
            self.compile_stmt(stmt, allow_return=False)
        self.em.u8(CPU.HALT)

        # Functions after main; CALL targets are patched later.
        for name, fn in self.functions.items():
            self.current_function = name
            self.em.bind(self._function_label(name))
            # Save caller frame pointer and establish this call's frame.
            self.em.code += bytes([CPU.PUSH, 7, CPU.GETSP, 7])
            # Allocate locals as stack slots.
            for _ in range(self.function_local_counts[name]):
                self.em.movi(6, 0); self.em.code += bytes([CPU.PUSH, 6])
            for stmt in fn.body.statements:
                self.compile_stmt(stmt, allow_return=True)
            self.em.movi(0, 0)
            self.emit_function_epilogue()

        self.current_function = None
        exe = self.em.finalize()
        return exe


class MiniLang:
    """Public MiniLang API used by the shell."""

    @staticmethod
    def parse(source: str) -> MLProgram:
        return MiniLangParser(source).parse()

    @staticmethod
    def run_source(source: str, print_fn=print, runtime=None) -> int:
        return MiniLangInterpreter.run(source, print_fn, runtime)

    @staticmethod
    def compile_placeholder(source: str) -> MEXE:
        program = MiniLang.parse(source)
        return MiniLangCompiler(program).compile()


class MiniLangInterpreter:
    @staticmethod
    def run(source: str, print_fn=print, runtime=None) -> int:
        program = MiniLang.parse(source)
        functions: Dict[str, MLFunction] = {}
        for stmt in program.statements:
            if isinstance(stmt, MLFunction):
                if stmt.name in functions:
                    raise MiniLangCompileError(f"fonction déjà déclarée : {stmt.name}", stmt.token.line, stmt.token.source, stmt.token.col)
                functions[stmt.name] = stmt
        env = MLEnv(runtime=runtime)
        try:
            MiniLangInterpreter._exec_block(MLBlock([s for s in program.statements if not isinstance(s, MLFunction)]), env, functions, print_fn)
        except MLExitSignal as ex:
            return ex.code
        return 0

    @staticmethod
    def _exec_block(block: MLBlock, env: MLEnv, functions: Dict[str, MLFunction], print_fn):
        MiniLang._exec_block_impl(block, env, functions, print_fn)

    @staticmethod
    def _exec_block_impl(block: MLBlock, env: MLEnv, functions: Dict[str, MLFunction], print_fn):
        # Delegate to the methods attached to MiniLang below for compatibility.
        for stmt in block.statements:
            MiniLang._exec_stmt_impl(stmt, env, functions, print_fn)


# Runtime helpers kept outside MiniLangCompiler to keep the public API compact.
def _ml_builtin(name: str, args: List[Any], runtime=None, env: Optional[MLEnv] = None):
    if name == "len":
        return len(args[0])
    if name == "int": return int(args[0])
    if name == "str": return str(args[0])
    if runtime is None:
        # Fonctions qui ne dépendent pas du miniOS sont toujours utilisables.
        if name == "time": return int(time.time())
        if name == "timeMs": return int(time.time() * 1000)
        if name == "random":
            import random; return random.randrange(max(1, int(args[0])))
        if name == "randomRange":
            import random; return random.randint(int(args[0]), int(args[1]))
        raise MiniLangCompileError(f"fonction runtime indisponible sans miniOS: {name}")
    proc = getattr(runtime, "current_process", None)
    cwd = getattr(proc, "cwd", runtime.cwd)
    if name == "input":
        prompt = str(args[0]) if args else ""
        if runtime is not None and proc is not None and getattr(proc, "stdin_pipe", False):
            available, value = proc.read_stdin_line()
            if not available:
                raise RuntimeError("entrée standard terminée (EOF)")
            return value
        return input(prompt)
    if name == "inputInt":
        prompt = str(args[0]) if args else ""
        while True:
            if runtime is not None and proc is not None and getattr(proc, "stdin_pipe", False):
                available, raw = proc.read_stdin_line()
                if not available:
                    raise RuntimeError("entrée standard terminée (EOF)")
            else:
                raw = input(prompt)
            try: return int(raw.strip(), 0)
            except ValueError:
                print("Valeur invalide: entrez un entier.")
    if name == "system":
        key=str(args[0]).lower(); vals={"os.name":"miniOS","os.version":VERSION,"os.arch":"VM32","user.name":"user","user.home":"/home/user","user.dir":cwd,"hostname":HOSTNAME,"memory.size":str(RAM_SIZE),"path":runtime.env.get("PATH","")}; return vals.get(key,"")
    if name == "env": return runtime.env.get(str(args[0]), "")
    if name == "envSet": runtime.env[str(args[0])] = str(args[1]); return 0
    if name == "exists": return int(runtime.disk.exists(runtime.resolve(str(args[0]), cwd)))
    if name == "isDir": return int(runtime.disk.is_dir(runtime.resolve(str(args[0]), cwd)))
    if name == "read":
        d=runtime.disk.read(runtime.resolve(str(args[0]), cwd)); return decode_text_bytes(d) if isinstance(d,bytes) else str(d)
    if name == "write": runtime.disk.write(runtime.resolve(str(args[0]), cwd), str(args[1])); return 0
    if name == "append": runtime.disk.append(runtime.resolve(str(args[0]), cwd), str(args[1])); return 0
    if name == "mkdir": runtime.disk.mkdir(runtime.resolve(str(args[0]), cwd), parents=bool(args[1]) if len(args)>1 else False); return 0
    if name == "remove": runtime.disk.delete(runtime.resolve(str(args[0]), cwd), recursive=bool(args[1]) if len(args)>1 else False); return 0
    if name == "copy": runtime.disk.copy(runtime.resolve(str(args[0]), cwd), runtime.resolve(str(args[1]), cwd)); return 0
    if name == "move": runtime.disk.move(runtime.resolve(str(args[0]), cwd), runtime.resolve(str(args[1]), cwd)); return 0
    if name == "fileSize":
        d=runtime.disk.read(runtime.resolve(str(args[0]), cwd)); return len(d) if isinstance(d,bytes) else len(str(d).encode())
    if name == "fileByte":
        d=runtime.disk.read(runtime.resolve(str(args[0]), cwd)); raw=d if isinstance(d,bytes) else str(d).encode(); i=int(args[1]); return raw[i] if 0<=i<len(raw) else -1
    if name == "setFileByte":
        p=runtime.resolve(str(args[0]), cwd); d=runtime.disk.read(p); raw=bytearray(d if isinstance(d,bytes) else str(d).encode()); i=int(args[1]);
        if i>=len(raw): raw.extend(b"\0"*(i+1-len(raw))); raw[i]=int(args[2])&255; runtime.disk.write(p,bytes(raw)); return 0
    if name == "list": return "\n".join(n+("/" if d else "") for n,d in runtime.disk.ls(runtime.resolve(str(args[0]),cwd),cwd))
    if name == "shell":
        old_cwd = runtime.cwd
        try:
            runtime.cwd = cwd
            runtime.execute(str(args[0]))
        finally:
            runtime.cwd = old_cwd
        return 0
    if name == "run":
        path=runtime.search_path(str(args[0]));
        if not path: raise FileNotFoundError(str(args[0]));
        return runtime._run_virtual_mexe(path,args=[str(x) for x in args[1:]],quiet=False)
    if name == "sleep": time.sleep(max(0,int(args[0]))/1000); return 0
    if name == "time": return int(time.time())
    if name == "timeMs": return int(time.time()*1000)
    if name == "random":
        import random; return random.randrange(max(1,int(args[0])))
    if name == "randomRange":
        import random; return random.randint(int(args[0]),int(args[1]))
    if name == "argc": return len(getattr(proc,"argv",[]))
    if name == "arg":
        a=getattr(proc,"argv",[]); i=int(args[0]); return a[i] if 0<=i<len(a) else ""
    if name == "cwd": return cwd
    if name == "chdir":
        p=runtime.resolve(str(args[0]),cwd);
        if not runtime.disk.is_dir(p): raise NotADirectoryError(p)
        if proc: proc.cwd=p
        else: runtime.cwd=p
        return 0
    if name == "ping": runtime.cmd_ping([str(args[0])]); return 0
    if name == "pid": return getattr(proc,"pid",0)
    if name == "program": return getattr(proc,"name","program")
    if name == "hostname": return HOSTNAME
    if name == "memTotal": return RAM_SIZE
    if name == "memFree": return RAM_SIZE
    if name == "alloc": return [0] * max(1, int(args[0]))
    if name == "free": return 0
    if name == "substr": s=str(args[0]); i=max(0,int(args[1])); return s[i:] if len(args)<3 else s[i:i+int(args[2])]
    if name == "replace": return str(args[0]).replace(str(args[1]),str(args[2]))
    if name == "contains": return int(str(args[1]) in str(args[0]))
    if name == "startsWith": return int(str(args[0]).startswith(str(args[1])))
    if name == "endsWith": return int(str(args[0]).endswith(str(args[1])))
    if name == "lower": return str(args[0]).lower()
    if name == "upper": return str(args[0]).upper()
    if name == "trim": return str(args[0]).strip()
    if name == "chr": return chr(int(args[0]) & 0x10FFFF)
    if name == "ord": return ord(str(args[0])[0]) if str(args[0]) else -1
    if name == "array": return [0]*max(0,int(args[0]))
    if name == "arrayLen": return len(args[0])
    if name == "arrayGet": return args[0][int(args[1])]
    if name == "arrayGetStr": return str(args[0][int(args[1])])
    if name == "arraySet": args[0][int(args[1])] = args[2]; return args[2]
    if name == "importHost":
        host=runtime.resolve_host_path(str(args[0])); vp=runtime.resolve(str(args[1]), cwd);
        if not os.path.isfile(host): raise FileNotFoundError(host)
        if runtime.disk.is_dir(vp): vp=vp.rstrip("/")+"/"+os.path.basename(host)
        with open(host,"rb") as f: raw=f.read(); raw,_=normalize_imported_text(raw, host); runtime.disk.write(vp,raw); return 0
    if name == "exportHost":
        vp=runtime.resolve(str(args[0]),cwd); host=runtime.resolve_host_path(str(args[1])); data=runtime.disk.read(vp); raw=data if isinstance(data,bytes) else str(data).encode(); os.makedirs(os.path.dirname(host) or ".",exist_ok=True); open(host,"wb").write(raw); return 0
    if name == "hostExists": return int(os.path.exists(runtime.resolve_host_path(str(args[0]))))
    if name == "tcpConnect":
        host, port = str(args[0]), int(args[1])
        timeout = 15.0 if len(args) < 3 or int(args[2]) <= 0 else min(int(args[2]), 120)
        sock = socket.create_connection((host, port), timeout=timeout)
        sock.settimeout(None)
        pid = int(getattr(proc, "pid", 0)) if proc is not None else 0
        return NETWORK_SOCKETS.open(pid, sock, "tcp")
    if name == "tcpSend":
        pid = int(getattr(proc, "pid", 0)) if proc is not None else 0
        sock = NETWORK_SOCKETS.get(pid, int(args[0]), "tcp")
        raw = str(args[1]).encode("utf-8")
        sock.sendall(raw)
        return len(raw)
    if name == "tcpRecv":
        pid = int(getattr(proc, "pid", 0)) if proc is not None else 0
        handle = int(args[0])
        max_bytes = int(args[1]) if len(args) >= 2 and int(args[1]) > 0 else 4096
        timeout = 15.0 if len(args) < 3 or int(args[2]) <= 0 else min(int(args[2]), 120)
        sock = NETWORK_SOCKETS.get(pid, handle, "tcp")
        sock.settimeout(timeout)
        try:
            data = sock.recv(min(max_bytes, 4 * 1024 * 1024))
        except socket.timeout:
            data = b""
        finally:
            sock.settimeout(None)
        return data.decode("utf-8", errors="replace")
    if name == "tcpClose":
        pid = int(getattr(proc, "pid", 0)) if proc is not None else 0
        return 0 if NETWORK_SOCKETS.close(pid, int(args[0])) else 1
    if name == "tcpIsOpen":
        pid = int(getattr(proc, "pid", 0)) if proc is not None else 0
        try:
            NETWORK_SOCKETS.get(pid, int(args[0]), "tcp")
            return True
        except Exception:
            return False
    if name == "udpOpen":
        pid = int(getattr(proc, "pid", 0)) if proc is not None else 0
        return NETWORK_SOCKETS.open(pid, socket.socket(socket.AF_INET, socket.SOCK_DGRAM), "udp")
    if name == "udpSend":
        pid = int(getattr(proc, "pid", 0)) if proc is not None else 0
        sock = NETWORK_SOCKETS.get(pid, int(args[0]), "udp")
        raw = str(args[3]).encode("utf-8")
        return sock.sendto(raw, (str(args[1]), int(args[2])))
    if name == "udpRecv":
        pid = int(getattr(proc, "pid", 0)) if proc is not None else 0
        handle = int(args[0])
        max_bytes = int(args[1]) if len(args) >= 2 and int(args[1]) > 0 else 4096
        timeout = 15.0 if len(args) < 3 or int(args[2]) <= 0 else min(int(args[2]), 120)
        sock = NETWORK_SOCKETS.get(pid, handle, "udp")
        sock.settimeout(timeout)
        try:
            data, _addr = sock.recvfrom(min(max_bytes, 4 * 1024 * 1024))
        except socket.timeout:
            data = b""
        finally:
            sock.settimeout(None)
        return data.decode("utf-8", errors="replace")
    if name == "udpClose":
        pid = int(getattr(proc, "pid", 0)) if proc is not None else 0
        return 0 if NETWORK_SOCKETS.close(pid, int(args[0])) else 1
    if name == "imageLoad":
        if proc is None: raise RuntimeError("processus MiniLang absent")
        p = runtime.resolve(str(args[0]), cwd)
        raw = runtime.disk.read(p); raw = raw if isinstance(raw, bytes) else str(raw).encode("utf-8")
        return proc.image_manager.load(p, raw)
    if name == "imageDraw":
        if proc is None: raise RuntimeError("processus MiniLang absent")
        runtime.graphics.image_draw(int(getattr(proc,"pid",0)), proc.image_manager.get(int(args[0])), int(args[1]), int(args[2])); return 0
    if name == "imageDrawScaled":
        if proc is None: raise RuntimeError("processus MiniLang absent")
        runtime.graphics.image_draw_scaled(int(getattr(proc,"pid",0)), proc.image_manager.get(int(args[0])), int(args[1]), int(args[2]), max(1,int(args[3])), max(1,int(args[4]))); return 0
    if name == "imageWidth":
        if proc is None: raise RuntimeError("processus MiniLang absent")
        return proc.image_manager.get(int(args[0])).width
    if name == "imageHeight":
        if proc is None: raise RuntimeError("processus MiniLang absent")
        return proc.image_manager.get(int(args[0])).height
    if name == "imageFree":
        if proc is None: raise RuntimeError("processus MiniLang absent")
        return 0 if proc.image_manager.free(int(args[0])) else 1
    if name == "rgb":
        r=max(0,min(255,int(args[0]))); g=max(0,min(255,int(args[1]))); b=max(0,min(255,int(args[2])))
        return (r<<16)|(g<<8)|b
    pid=int(getattr(proc,"pid",0))
    if name == "window": return runtime.graphics.window(str(args[0]),int(args[1]),int(args[2]),pid)
    if name == "clear": runtime.graphics.clear(pid,int(args[0])); return 0
    if name == "pixel": runtime.graphics.pixel(pid,int(args[0]),int(args[1]),int(args[2])); return 0
    if name == "rect": runtime.graphics.rect(pid,int(args[0]),int(args[1]),int(args[2]),int(args[3]),int(args[4])); return 0
    if name == "line": runtime.graphics.line(pid,int(args[0]),int(args[1]),int(args[2]),int(args[3]),int(args[4])); return 0
    if name == "circle": runtime.graphics.circle(pid,int(args[0]),int(args[1]),int(args[2]),int(args[3])); return 0
    if name == "text": runtime.graphics.text(pid,int(args[0]),int(args[1]),str(args[2]),int(args[3])); return 0
    if name == "present": runtime.graphics.present(pid); return 0
    if name == "close": runtime.graphics.close(pid); return 0
    if name == "minimize": runtime.graphics.minimize(pid); return 0
    if name == "keyDown": return int(runtime.graphics.key_down(pid,str(args[0])))
    if name == "keyPressed": return int(runtime.graphics.key_pressed(pid,str(args[0])))
    if name == "textInput": return runtime.graphics.text_input(pid, str(args[0]) if args else "get")
    if name == "mouseX": return int(runtime.graphics.mouse_x(pid))
    if name == "mouseY": return int(runtime.graphics.mouse_y(pid))
    if name == "mouseDown": return int(runtime.graphics.mouse_down(pid,int(args[0])))
    if name == "closeRequested": return int(runtime.graphics.close_requested(pid))
    if name == "windowAlive": return int(runtime.graphics.alive(pid))
    raise MiniLangCompileError(f"fonction runtime inconnue: {name}")

def _ml_eval_expr(node: Any, env: MLEnv, functions: Dict[str, MLFunction], print_fn):
    if isinstance(node, MLLiteral): return node.value
    if isinstance(node, MLVar): return env.get(node.name)
    if isinstance(node, MLUnary):
        if node.op in ("++", "--"):
            if not isinstance(node.expr, MLVar): raise MiniLangCompileError(f"'{node.op}' exige une variable", node.token.line, node.token.source, node.token.col)
            old = env.get(node.expr.name)
            try: new = int(old) + (1 if node.op == "++" else -1)
            except Exception: raise MiniLangCompileError(f"'{node.op}' exige un entier", node.token.line, node.token.source, node.token.col)
            env.set(node.expr.name, new); return new if node.prefix else old
        v = _ml_eval_expr(node.expr, env, functions, print_fn)
        if node.op == "+": return +v
        if node.op == "-": return -v
        if node.op == "!": return not bool(v)
        if node.op == "~": return ~int(v)
        raise MiniLangCompileError(f"opérateur unaire inconnu : {node.op}", node.token.line, node.token.source, node.token.col)
    if isinstance(node, MLBinary):
        op = node.op
        if op == "&&":
            a = _ml_eval_expr(node.left, env, functions, print_fn)
            return bool(a) and bool(_ml_eval_expr(node.right, env, functions, print_fn))
        if op == "||":
            a = _ml_eval_expr(node.left, env, functions, print_fn)
            return bool(a) or bool(_ml_eval_expr(node.right, env, functions, print_fn))
        a = _ml_eval_expr(node.left, env, functions, print_fn); b = _ml_eval_expr(node.right, env, functions, print_fn)
        try:
            if op == "+": return str(a) + str(b) if isinstance(a, str) or isinstance(b, str) else int(a) + int(b)
            if op == "-": return int(a) - int(b)
            if op == "*": return int(a) * int(b)
            if op == "/": return MiniLang._int_div(int(a), int(b))
            if op == "%": return int(a) - MiniLang._int_div(int(a), int(b)) * int(b)
            if op == "==": return a == b
            if op == "!=": return a != b
            if op == "<": return a < b
            if op == "<=": return a <= b
            if op == ">": return a > b
            if op == ">=": return a >= b
            if op == "&": return int(a) & int(b)
            if op == "|": return int(a) | int(b)
            if op == "^": return int(a) ^ int(b)
            if op == "<<": return int(a) << (int(b) & 31)
            if op == ">>": return int(a) >> (int(b) & 31)
        except Exception as exc:
            raise MiniLangCompileError(f"opération invalide '{op}': {exc}", node.token.line, node.token.source, node.token.col)
        raise MiniLangCompileError(f"opérateur inconnu : {op}", node.token.line, node.token.source, node.token.col)
    if isinstance(node, MLIndex):
        target = _ml_eval_expr(node.target, env, functions, print_fn); idx = int(_ml_eval_expr(node.index, env, functions, print_fn))
        if isinstance(target, str):
            if idx < 0 or idx >= len(target): raise MiniLangCompileError("index de chaîne hors limites", node.token.line, node.token.source, node.token.col)
            return target[idx]
        return target[idx]
    if isinstance(node, MLCall):
        args = [_ml_eval_expr(x, env, functions, print_fn) for x in node.args]
        if node.name in {
            "input","inputInt","len","int","str","system","env","envSet","exists","isDir","read","write","append","mkdir","remove","copy","move","fileSize","fileByte","setFileByte","list","shell","run","sleep","time","timeMs","random","randomRange","argc","arg","cwd","chdir","array","arrayLen","arrayGet","arraySet","substr","replace","contains","startsWith","endsWith","lower","upper","trim","chr","ord","ping","pid","program","hostname","memTotal","memFree","alloc","free","arrayGetStr","importHost","exportHost","hostExists"
        }:
            return _ml_builtin(node.name, args, env.runtime)
        if node.name == "len":
            if len(args) != 1: raise MiniLangCompileError("len() attend 1 argument", node.token.line, node.token.source, node.token.col)
            return len(args[0])
        if node.name == "int":
            if len(args) != 1: raise MiniLangCompileError("int() attend 1 argument", node.token.line, node.token.source, node.token.col)
            return int(args[0])
        if node.name == "str":
            if len(args) != 1: raise MiniLangCompileError("str() attend 1 argument", node.token.line, node.token.source, node.token.col)
            return str(args[0])
        fn = functions.get(node.name)
        if not fn: raise MiniLangCompileError(f"fonction inconnue : {node.name}", node.token.line, node.token.source, node.token.col)
        if len(args) != len(fn.params): raise MiniLangCompileError(f"{node.name}() attend {len(fn.params)} argument(s), reçu {len(args)}", node.token.line, node.token.source, node.token.col)
        child = MLEnv(env, env.runtime)
        for n, v in zip(fn.params, args): child.declare(n, v)
        try:
            MiniLang._exec_block_impl(fn.body, child, functions, print_fn)
        except MLReturnSignal as ret: return ret.value
        return 0
    raise MiniLangCompileError(f"expression interne inconnue : {type(node).__name__}")


def _ml_exec_stmt(node: Any, env: MLEnv, functions: Dict[str, MLFunction], print_fn):
    if isinstance(node, MLLet):
        env.declare(node.name, 0 if node.expr is None else _ml_eval_expr(node.expr, env, functions, print_fn))
    elif isinstance(node, MLAssign):
        value = _ml_eval_expr(node.expr, env, functions, print_fn)
        if node.op != "=":
            old = env.get(node.name)
            base = {"+=": "+", "-=": "-", "*=": "*", "/=": "/", "%=": "%"}[node.op]
            fake = MLBinary(base, MLLiteral(old, node.token), MLLiteral(value, node.token), node.token)
            value = _ml_eval_expr(fake, env, functions, print_fn)
        env.set(node.name, value)
    elif isinstance(node, MLIndexAssign):
        target = _ml_eval_expr(node.target, env, functions, print_fn); idx = int(_ml_eval_expr(node.index, env, functions, print_fn)); value = _ml_eval_expr(node.expr, env, functions, print_fn)
        if node.op == "=": target[idx] = value
        else:
            old = target[idx]; base = {"+=":"+","-=":"-","*=":"*","/=":"/","%=" : "%"}[node.op]
            target[idx] = _ml_eval_expr(MLBinary(base, MLLiteral(old,node.token), MLLiteral(value,node.token), node.token), env, functions, print_fn)
    elif isinstance(node, MLPrint):
        value = _ml_eval_expr(node.expr, env, functions, print_fn)
        end = "\n" if node.end_expr is None else str(_ml_eval_expr(node.end_expr, env, functions, print_fn))
        flush = True if node.flush_expr is None else bool(_ml_eval_expr(node.flush_expr, env, functions, print_fn))
        try:
            print_fn(value, end=end, flush=flush)
        except TypeError:
            print_fn(str(value) + end)
    elif isinstance(node, MLExit): raise MLExitSignal(int(_ml_eval_expr(node.expr, env, functions, print_fn)))
    elif isinstance(node, MLExprStmt): _ml_eval_expr(node.expr, env, functions, print_fn)
    elif isinstance(node, MLIf):
        if bool(_ml_eval_expr(node.cond, env, functions, print_fn)):
            MiniLang._exec_block_impl(node.then_block, env, functions, print_fn)
        elif node.else_block:
            MiniLang._exec_block_impl(node.else_block, env, functions, print_fn)
    elif isinstance(node, MLWhile):
        while bool(_ml_eval_expr(node.cond, env, functions, print_fn)):
            try: MiniLang._exec_block_impl(node.body, env, functions, print_fn)
            except MLContinueSignal: pass
            except MLBreakSignal: break
    elif isinstance(node, MLFor):
        if node.init: _ml_exec_stmt(node.init, env, functions, print_fn)
        while node.cond is None or bool(_ml_eval_expr(node.cond, env, functions, print_fn)):
            try: MiniLang._exec_block_impl(node.body, env, functions, print_fn)
            except MLContinueSignal: pass
            except MLBreakSignal: break
            if node.update: _ml_exec_stmt(node.update, env, functions, print_fn)
    elif isinstance(node, MLBreak): raise MLBreakSignal()
    elif isinstance(node, MLContinue): raise MLContinueSignal()
    elif isinstance(node, MLReturn): raise MLReturnSignal(0 if node.expr is None else _ml_eval_expr(node.expr, env, functions, print_fn))
    elif isinstance(node, MLFunction): pass
    else: raise MiniLangCompileError(f"instruction interne inconnue : {type(node).__name__}")


MiniLang._int_div = staticmethod(lambda a, b: (_ for _ in ()).throw(MiniLangCompileError("division par zéro")) if b == 0 else (-1 if (a < 0) != (b < 0) else 1) * (abs(int(a)) // abs(int(b))))
MiniLang._exec_block_impl = staticmethod(lambda block, env, functions, print_fn: [ _ml_exec_stmt(s, env, functions, print_fn) for s in block.statements ])
MiniLang._exec_stmt_impl = staticmethod(_ml_exec_stmt)


# ================================================================
# JVM class-file parser
# ================================================================

@dataclass
class CPEntry:
    tag: int
    value: Any


@dataclass
class JVMField:
    access: int
    name: str
    descriptor: str
    attributes: Dict[str, bytes] = field(default_factory=dict)


@dataclass
class JVMMethod:
    access: int
    name: str
    descriptor: str
    attributes: Dict[str, bytes] = field(default_factory=dict)
    max_stack: int = 0
    max_locals: int = 0
    code: bytes = b""
    exception_table: List[Tuple[int, int, int, int]] = field(default_factory=list)


@dataclass
class JVMClass:
    name: str
    super_name: Optional[str]
    access: int
    cp: List[Optional[CPEntry]]
    fields: List[JVMField]
    methods: List[JVMMethod]
    interfaces: List[str]
    major: int
    minor: int
    source: str = ""

    def utf8(self, index: int) -> str:
        e = self.cp[index]
        if not e or e.tag != 1:
            raise ValueError(f"Constant #{index} n'est pas UTF8")
        return e.value

    def class_name(self, index: int) -> str:
        e = self.cp[index]
        if not e or e.tag != 7:
            raise ValueError(f"Constant #{index} n'est pas Class")
        return self.utf8(e.value)

    def const(self, index: int) -> CPEntry:
        e = self.cp[index]
        if e is None:
            raise ValueError(f"Constant #{index} invalide")
        return e

    def find_method(self, name: str, desc: str) -> Optional[JVMMethod]:
        for m in self.methods:
            if m.name == name and m.descriptor == desc:
                return m
        return None

    @classmethod
    def parse(cls, blob: bytes, source: str = "") -> "JVMClass":
        f = io.BytesIO(blob)
        if read_bytes(f, 4) != b"\xCA\xFE\xBA\xBE":
            raise ValueError("Classe Java invalide: magic CAFEBABE absent")
        minor = read_u2(f); major = read_u2(f)
        cp_count = read_u2(f)
        cp: List[Optional[CPEntry]] = [None] * cp_count
        i = 1
        while i < cp_count:
            tag = read_u1(f)
            if tag == 1:
                ln = read_u2(f)
                cp[i] = CPEntry(tag, read_bytes(f, ln).decode("utf-8", errors="replace"))
            elif tag == 3:
                cp[i] = CPEntry(tag, read_i4(f))
            elif tag == 4:
                cp[i] = CPEntry(tag, struct.unpack(">f", read_bytes(f, 4))[0])
            elif tag == 5:
                cp[i] = CPEntry(tag, struct.unpack(">q", read_bytes(f, 8))[0]); i += 1
            elif tag == 6:
                cp[i] = CPEntry(tag, struct.unpack(">d", read_bytes(f, 8))[0]); i += 1
            elif tag == 7:
                cp[i] = CPEntry(tag, read_u2(f))
            elif tag == 8:
                cp[i] = CPEntry(tag, read_u2(f))
            elif tag in (9, 10, 11):
                cp[i] = CPEntry(tag, (read_u2(f), read_u2(f)))
            elif tag == 12:
                cp[i] = CPEntry(tag, (read_u2(f), read_u2(f)))
            elif tag == 15:
                cp[i] = CPEntry(tag, (read_u1(f), read_u2(f)))
            elif tag == 16:
                cp[i] = CPEntry(tag, read_u2(f))
            elif tag == 17:
                cp[i] = CPEntry(tag, (read_u2(f), read_u2(f)))
            elif tag == 18:
                cp[i] = CPEntry(tag, (read_u2(f), read_u2(f)))
            elif tag in (19, 20):
                cp[i] = CPEntry(tag, read_u2(f))
            else:
                raise ValueError(f"Constant pool tag inconnu: {tag}")
            i += 1

        access = read_u2(f)
        this_class = read_u2(f)
        super_class = read_u2(f)
        name = cp[this_class].value if cp[this_class] and cp[this_class].tag == 1 else None
        # Resolve through Class -> Utf8.
        this_name = cp[cp[this_class].value].value  # type: ignore
        super_name = None if super_class == 0 else cp[cp[super_class].value].value  # type: ignore

        interfaces = []
        for _ in range(read_u2(f)):
            idx = read_u2(f); interfaces.append(cp[cp[idx].value].value)  # type: ignore

        fields = []
        for _ in range(read_u2(f)):
            fa = read_u2(f); ni = read_u2(f); di = read_u2(f)
            fields.append(JVMField(fa, cp[ni].value, cp[di].value))  # type: ignore
            ac = read_u2(f)
            for _a in range(ac):
                ai = read_u2(f); ln = read_u4(f); blob2 = read_bytes(f, ln)
                fields[-1].attributes[cp[ai].value] = blob2  # type: ignore

        methods: List[JVMMethod] = []
        for _ in range(read_u2(f)):
            ma = read_u2(f); ni = read_u2(f); di = read_u2(f)
            m = JVMMethod(ma, cp[ni].value, cp[di].value)  # type: ignore
            ac = read_u2(f)
            for _a in range(ac):
                ai = read_u2(f); ln = read_u4(f); blob2 = read_bytes(f, ln)
                aname = cp[ai].value  # type: ignore
                m.attributes[aname] = blob2
                if aname == "Code":
                    cf = io.BytesIO(blob2)
                    m.max_stack = read_u2(cf); m.max_locals = read_u2(cf)
                    clen = read_u4(cf); m.code = read_bytes(cf, clen)
                    etn = read_u2(cf)
                    for _e in range(etn):
                        m.exception_table.append((read_u2(cf), read_u2(cf), read_u2(cf), read_u2(cf)))
                    nested = read_u2(cf)
                    for _n in range(nested):
                        # We do not yet interpret nested Code attributes.
                        read_u2(cf); nlen = read_u4(cf); read_bytes(cf, nlen)
            methods.append(m)

        ac = read_u2(f)
        for _ in range(ac):
            ai = read_u2(f); ln = read_u4(f); read_bytes(f, ln)

        return cls(this_name, super_name, access, cp, fields, methods, interfaces, major, minor, source)


# ================================================================
# JVM runtime objects
# ================================================================

@dataclass
class JavaObject:
    class_name: str
    fields: Dict[str, Any] = field(default_factory=dict)

    def __repr__(self):
        return f"<{self.class_name} object>"


@dataclass
class JavaArray:
    values: List[Any]
    component: str = "Ljava/lang/Object;"

    def __repr__(self):
        return f"[{len(self.values)} x {self.component}]"


@dataclass
class JVMFrame:
    klass: JVMClass
    method: JVMMethod
    locals: List[Any]
    stack: List[Any] = field(default_factory=list)
    pc: int = 0
    return_to: Optional["JVMFrame"] = None


class JavaException(Exception):
    def __init__(self, class_name: str, message: str = ""):
        self.class_name = class_name
        self.message = message
        super().__init__(f"{class_name}: {message}" if message else class_name)


class PrintStreamObject(JavaObject):
    def __init__(self):
        super().__init__("java/io/PrintStream")


class StringObject:
    def __init__(self, value: str):
        self.class_name = "java/lang/String"
        self.value = value

    def __str__(self):
        return self.value

    def __repr__(self):
        return repr(self.value)


class SystemClassObject:
    def __init__(self, runtime: "JavaRuntime"):
        self.runtime = runtime


class JavaRuntime:
    def __init__(self, os_ref: Optional["MiniOS"] = None):
        self.os = os_ref
        self.static_fields: Dict[Tuple[str, str, str], Any] = {}
        self.string_cache: Dict[str, StringObject] = {}
        self.stdout = PrintStreamObject()
        self.static_fields[("java/lang/System", "out", "Ljava/io/PrintStream;")] = self.stdout
        self.exit_requested = False
        self.exit_code = 0

    def read_line(self, prompt: str = "") -> str:
        """Read one line from the real terminal; exposed to Java applications."""
        try:
            return input(prompt)
        except (EOFError, KeyboardInterrupt):
            print()
            return ""

    def read_int(self, prompt: str = "") -> int:
        """Read an integer, retrying until the user supplies a valid value."""
        while True:
            raw = self.read_line(prompt).strip()
            try:
                return int(raw, 10)
            except ValueError:
                self.println("Entrée invalide : veuillez saisir un entier.")

    def get_property(self, key: str) -> str:
        """Virtual miniOS system properties available to Java programs."""
        key = str(key)
        os_ref = self.os
        props = {
            "os.name": VERSION.split()[0],
            "os.version": VERSION,
            "os.arch": "vm32-jvm",
            "user.name": "user",
            "user.home": "/home/user",
            "user.dir": getattr(os_ref, "cwd", "/home/user"),
            "file.separator": "/",
            "path.separator": ":",
            "line.separator": "\n",
            "hostname": HOSTNAME,
            "memory.size": str(RAM_SIZE),
            "memory.unit": "bytes",
            "jvm.version": "miniJVM 0.5",
        }
        if key == "time":
            return datetime.datetime.now().strftime("%H:%M:%S")
        if key == "date":
            return datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        return props.get(key, "")

    def get_env(self, key: str) -> str:
        """Read the virtual miniOS environment, not the host process environment."""
        if self.os is not None:
            return str(self.os.env.get(str(key), ""))
        return ""

    def java_string(self, value: str) -> StringObject:
        if value not in self.string_cache:
            self.string_cache[value] = StringObject(value)
        return self.string_cache[value]

    def printable(self, value: Any) -> str:
        if value is None:
            return "null"
        if isinstance(value, StringObject):
            return value.value
        if isinstance(value, JavaObject):
            return f"{value}"
        if isinstance(value, JavaArray):
            return repr(value)
        if isinstance(value, bool):
            return "true" if value else "false"
        return str(value)

    def println(self, value: Any = None):
        print(self.printable(value))

    def print(self, value: Any = None):
        sys.stdout.write(self.printable(value)); sys.stdout.flush()

    def invoke_native(self, owner: str, name: str, desc: str, args: List[Any], obj: Any) -> Tuple[bool, Any]:
        # System methods
        if owner == "java/lang/System" and name == "exit" and desc == "(I)V":
            self.exit_code = int(args[0]); self.exit_requested = True
            return True, None
        if owner == "java/lang/System" and name == "getProperty" and desc == "(Ljava/lang/String;)Ljava/lang/String;":
            key = self.printable(args[0] if args else "")
            return True, self.java_string(self.get_property(key))
        if owner == "java/lang/System" and name == "getenv" and desc == "(Ljava/lang/String;)Ljava/lang/String;":
            key = self.printable(args[0] if args else "")
            return True, self.java_string(self.get_env(key))

        # miniOS interactive/system API
        if owner == "miniOS/Runtime":
            if name == "readLine" and desc in ("()Ljava/lang/String;", "(Ljava/lang/String;)Ljava/lang/String;"):
                prompt = self.printable(args[0]) if args else ""
                return True, self.java_string(self.read_line(prompt))
            if name == "readInt" and desc in ("()I", "(Ljava/lang/String;)I"):
                prompt = self.printable(args[0]) if args else ""
                return True, self.read_int(prompt)

        # PrintStream
        if owner == "java/io/PrintStream":
            if name == "println":
                val = args[0] if args else None
                self.println(val)
                return True, None
            if name == "print":
                val = args[0] if args else None
                self.print(val)
                return True, None

        # String conveniences commonly emitted by small tests.
        if owner == "java/lang/String":
            if name == "length" and desc == "()I" and isinstance(obj, StringObject):
                return True, len(obj.value)
            if name == "toString" and desc == "()Ljava/lang/String;" and isinstance(obj, StringObject):
                return True, obj
            if name == "concat" and desc == "(Ljava/lang/String;)Ljava/lang/String;" and isinstance(obj, StringObject):
                other = args[0] if args else self.java_string("")
                return True, self.java_string(obj.value + self.printable(other))

        # Object.toString / getClass as minimal runtime hooks.
        if owner == "java/lang/Object" and name == "toString" and desc == "()Ljava/lang/String;":
            return True, self.java_string(self.printable(obj))
        if owner == "java/lang/Object" and name == "getClass" and desc == "()Ljava/lang/Class;":
            return True, JavaObject("java/lang/Class", {"name": getattr(obj, "class_name", "java/lang/Object")})

        return False, None


# ================================================================
# JVM loader and interpreter
# ================================================================

class JARLoader:
    def __init__(self):
        self.classes: Dict[str, JVMClass] = {}
        self.jars: List[str] = []

    def load_class_bytes(self, name: str, blob: bytes, source: str = "memory") -> JVMClass:
        norm = name.replace(".", "/")
        klass = JVMClass.parse(blob, source)
        self.classes[klass.name] = klass
        return klass

    def load_class_file(self, path: str) -> JVMClass:
        with open(path, "rb") as f:
            blob = f.read()
        klass = JVMClass.parse(blob, path)
        self.classes[klass.name] = klass
        return klass

    def load_jar(self, path: str) -> Optional[JVMClass]:
        main = None
        with zipfile.ZipFile(path, "r") as z:
            manifest = ""
            try:
                manifest = z.read("META-INF/MANIFEST.MF").decode("utf-8", errors="replace")
            except KeyError:
                pass
            for line in manifest.splitlines():
                if line.lower().startswith("main-class:"):
                    main = line.split(":", 1)[1].strip()
                    break

            for info in z.infolist():
                if info.is_dir() or not info.filename.endswith(".class"):
                    continue
                try:
                    blob = z.read(info)
                    klass = JVMClass.parse(blob, f"{path}!/{info.filename}")
                    self.classes[klass.name] = klass
                except Exception:
                    # Do not prevent the JAR index from loading because of an unrelated class.
                    continue
        self.jars.append(path)
        if main:
            key = main.replace(".", "/")
            return self.classes.get(key)
        return None

    def get(self, name: str) -> Optional[JVMClass]:
        n = name.replace(".", "/")
        return self.classes.get(n)


class JVM:
    # Access flags
    ACC_NATIVE = 0x0100
    ACC_STATIC = 0x0008
    ACC_ABSTRACT = 0x0400

    def __init__(self, os_ref: Optional["MiniOS"] = None):
        self.os = os_ref
        self.runtime = JavaRuntime(os_ref)
        self.loader = JARLoader()
        self.loaded: Dict[str, JVMClass] = {}
        self.frames: List[JVMFrame] = []
        self.heap: List[Any] = []
        self.steps = 0
        self.class_initialized: set[str] = set()
        self.entry_class: Optional[JVMClass] = None

    def load_class(self, name: str) -> JVMClass:
        n = name.replace(".", "/")
        if n in self.loaded:
            return self.loaded[n]
        k = self.loader.get(n)
        if k is None:
            raise JavaException("java/lang/ClassNotFoundException", n)
        self.loaded[n] = k
        return k

    def register(self, klass: JVMClass):
        self.loaded[klass.name] = klass
        self.loader.classes[klass.name] = klass

    def load_any(self, path: str) -> JVMClass:
        if not os.path.isfile(path):
            raise FileNotFoundError(path)
        if path.lower().endswith(".class"):
            k = self.loader.load_class_file(path)
            self.register(k)
            return k
        if path.lower().endswith(".jar"):
            main = self.loader.load_jar(path)
            for k in self.loader.classes.values():
                self.register(k)
            if main is None:
                raise JavaException("java/lang/NoSuchMethodException", "Main-Class absent du JAR")
            return main
        raise ValueError("java attend un fichier .class ou .jar")

    def resolve_utf8(self, k: JVMClass, idx: int) -> str:
        return k.utf8(idx)

    def cp_fieldref(self, k: JVMClass, idx: int):
        e = k.const(idx)
        if e.tag != 9:
            raise ValueError("Constant Fieldref attendue")
        ci, nti = e.value
        ce = k.const(ci)
        owner = k.utf8(ce.value)
        nt = k.const(nti)
        name_i, desc_i = nt.value
        return owner, k.utf8(name_i), k.utf8(desc_i)

    def cp_methodref(self, k: JVMClass, idx: int):
        e = k.const(idx)
        if e.tag not in (10, 11):
            raise ValueError("Constant Methodref attendue")
        ci, nti = e.value
        owner = k.class_name(ci)
        nt = k.const(nti)
        name_i, desc_i = nt.value
        return owner, k.utf8(name_i), k.utf8(desc_i)

    def push_frame(self, k: JVMClass, m: JVMMethod, args: List[Any], obj: Any = None):
        slots = max(m.max_locals, 1 + desc_arg_slots(m.descriptor) if not (m.access & self.ACC_STATIC) else desc_arg_slots(m.descriptor))
        locals_ = [None] * slots
        pos = 0
        if not (m.access & self.ACC_STATIC):
            locals_[0] = obj
            pos = 1
        for val in args:
            if pos >= len(locals_):
                locals_.append(val)
            else:
                locals_[pos] = val
            pos += 2 if isinstance(val, float) and False else 1
        frame = JVMFrame(k, m, locals_)
        self.frames.append(frame)
        return frame

    def class_method(self, owner: str, name: str, desc: str) -> Tuple[JVMClass, JVMMethod]:
        owner = owner.replace(".", "/")
        # Runtime-only classes are handled natively and don't need real methods.
        k = self.loaded.get(owner) or self.loader.get(owner)
        if k:
            self.loaded[owner] = k
            m = k.find_method(name, desc)
            if m:
                return k, m
            if k.super_name:
                try:
                    return self.class_method(k.super_name, name, desc)
                except JavaException:
                    pass
        raise JavaException("java/lang/NoSuchMethodError", f"{owner}.{name}{desc}")

    def get_static(self, owner: str, name: str, desc: str):
        return self.runtime.static_fields.get((owner, name, desc))

    def put_static(self, owner: str, name: str, desc: str, value: Any):
        self.runtime.static_fields[(owner, name, desc)] = value

    def get_instance_field(self, obj: JavaObject, name: str, desc: str):
        return obj.fields.get((name, desc))

    def put_instance_field(self, obj: JavaObject, name: str, desc: str, value: Any):
        obj.fields[(name, desc)] = value

    def ldc_value(self, k: JVMClass, index: int):
        e = k.const(index)
        if e.tag == 8:
            return self.runtime.java_string(k.utf8(e.value))
        if e.tag == 3:
            return e.value
        if e.tag == 4:
            return e.value
        if e.tag == 5 or e.tag == 6:
            return e.value
        if e.tag == 7:
            return JavaObject("java/lang/Class", {"name": k.class_name(index)})
        return e.value

    @staticmethod
    def _u8(code: bytes, pc: int): return code[pc]
    @staticmethod
    def _i8(code: bytes, pc: int): return struct.unpack(">b", code[pc:pc + 1])[0]
    @staticmethod
    def _u16(code: bytes, pc: int): return struct.unpack(">H", code[pc:pc + 2])[0]
    @staticmethod
    def _i16(code: bytes, pc: int): return struct.unpack(">h", code[pc:pc + 2])[0]
    @staticmethod
    def _i32(code: bytes, pc: int): return struct.unpack(">i", code[pc:pc + 4])[0]

    def invoke(self, owner: str, name: str, desc: str, args: List[Any], obj: Any = None, special: bool = False) -> Any:
        native, result = self.runtime.invoke_native(owner, name, desc, args, obj)
        if native:
            return result

        # Constructor for any user class: allocate an object and just run <init> if available.
        try:
            k, m = self.class_method(owner, name, desc)
        except JavaException:
            if name == "<init>":
                return None
            raise
        if m.access & self.ACC_NATIVE:
            native, result = self.runtime.invoke_native(owner, name, desc, args, obj)
            if native:
                return result
            raise JavaException("java/lang/UnsatisfiedLinkError", f"{owner}.{name}")
        if m.access & self.ACC_ABSTRACT:
            raise JavaException("java/lang/AbstractMethodError", f"{owner}.{name}")

        caller_depth = len(self.frames)
        self.push_frame(k, m, args, obj)
        result = self.run_until_depth(caller_depth)
        return result

    def run_until_depth(self, depth: int) -> Any:
        result = None
        while len(self.frames) > depth:
            if self.runtime.exit_requested:
                self.frames.clear()
                break
            ret = self.step()
            if ret is not _NO_RETURN:
                result = ret
        return result

    def run_main(self, klass: JVMClass, args: Optional[List[str]] = None) -> int:
        args = args or []
        self.entry_class = klass
        self.steps = 0
        self.runtime.exit_requested = False
        self.runtime.exit_code = 0
        self.frames.clear()

        main = klass.find_method("main", "([Ljava/lang/String;)V")
        if main is None:
            # Some test classes are convenient with a no-arg main.
            main = klass.find_method("main", "()V")
            if main is None:
                raise JavaException("java/lang/NoSuchMethodException", f"{klass.name}.main")
            self.push_frame(klass, main, [])
        else:
            self.push_frame(klass, main, [JavaArray([self.runtime.java_string(a) for a in args], "Ljava/lang/String;")])
        self.run_until_depth(0)
        return self.runtime.exit_code

    def step(self):
        self.steps += 1
        if self.steps > JVM_MAX_STEPS:
            raise RuntimeError("JVM: limite d'instructions atteinte")
        frame = self.frames[-1]
        code = frame.method.code
        if frame.pc >= len(code):
            raise JavaException("java/lang/VerifyError", f"PC hors méthode {frame.klass.name}.{frame.method.name}")
        op_pc = frame.pc
        op = code[frame.pc]
        frame.pc += 1
        s = frame.stack
        l = frame.locals

        # constants
        if op == 0x00: return _NO_RETURN  # nop
        if 0x02 <= op <= 0x08: s.append(op - 0x03)  # iconst_m1..iconst_5
        elif op == 0x09: s.append(0); l.append(0) if False else None  # lconst_0
        elif op == 0x0A: s.append(1)
        elif op == 0x0B: s.append(0.0)
        elif op == 0x0C: s.append(1.0)
        elif op == 0x0D: s.append(2.0)
        elif op == 0x10: s.append(self._i8(code, frame.pc)); frame.pc += 1
        elif op == 0x11: s.append(self._i16(code, frame.pc)); frame.pc += 2
        elif op == 0x12:
            idx = self._u8(code, frame.pc); frame.pc += 1; s.append(self.ldc_value(frame.klass, idx))
        elif op in (0x13, 0x14):
            idx = self._u16(code, frame.pc); frame.pc += 2; s.append(self.ldc_value(frame.klass, idx))

        # local integer/reference load/store
        elif op == 0x15:
            idx = self._u8(code, frame.pc); frame.pc += 1; s.append(l[idx])
        elif op == 0x16:
            idx = self._u8(code, frame.pc); frame.pc += 1; s.append(l[idx])
        elif op == 0x17:
            idx = self._u8(code, frame.pc); frame.pc += 1; s.append(l[idx])
        elif op == 0x18:
            idx = self._u8(code, frame.pc); frame.pc += 1; s.append(l[idx])
        elif op == 0x19:
            idx = self._u8(code, frame.pc); frame.pc += 1; s.append(l[idx])
        elif 0x1A <= op <= 0x1D:
            s.append(l[op - 0x1A])
        elif 0x1E <= op <= 0x21:
            s.append(l[op - 0x1E])
        elif 0x22 <= op <= 0x25:
            s.append(l[op - 0x22])
        elif 0x26 <= op <= 0x29:
            s.append(l[op - 0x26])
        elif 0x2A <= op <= 0x2D:
            s.append(l[op - 0x2A])
        elif op == 0x36:
            idx = self._u8(code, frame.pc); frame.pc += 1; l[idx] = s.pop()
        elif op == 0x37:
            idx = self._u8(code, frame.pc); frame.pc += 1; l[idx] = s.pop()
        elif op == 0x38:
            idx = self._u8(code, frame.pc); frame.pc += 1; l[idx] = s.pop()
        elif op == 0x39:
            idx = self._u8(code, frame.pc); frame.pc += 1; l[idx] = s.pop()
        elif op == 0x3A:
            idx = self._u8(code, frame.pc); frame.pc += 1; l[idx] = s.pop()
        elif 0x3B <= op <= 0x3E:
            l[op - 0x3B] = s.pop()
        elif 0x3F <= op <= 0x42:
            l[op - 0x3F] = s.pop()
        elif 0x43 <= op <= 0x46:
            l[op - 0x43] = s.pop()
        elif 0x47 <= op <= 0x4A:
            l[op - 0x47] = s.pop()
        elif 0x4B <= op <= 0x4E:
            l[op - 0x4B] = s.pop()

        # array loads / stores
        elif op in (0x2E, 0x2F, 0x30, 0x31, 0x32):
            idx = int(s.pop()); arr = s.pop(); s.append(arr.values[idx])
        elif op in (0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56):
            val = s.pop(); idx = int(s.pop()); arr = s.pop(); arr.values[idx] = val

        # stack manipulation
        elif op == 0x57: s.pop()
        elif op == 0x58: s.pop(); s.pop()
        elif op == 0x59: s.append(s[-1])
        elif op == 0x5F:
            a = s.pop(); b = s.pop(); s.extend([a, b])

        # integer arithmetic
        elif op in (0x60, 0x64, 0x68, 0x6C, 0x7E, 0x80, 0x82):
            b = s.pop(); a = s.pop()
            if op == 0x60: s.append(int(a) + int(b))
            elif op == 0x64: s.append(int(a) - int(b))
            elif op == 0x68: s.append(int(a) * int(b))
            elif op == 0x6C:
                if int(b) == 0: raise JavaException("java/lang/ArithmeticException", "/ by zero")
                s.append(int(int(a) / int(b)))
            elif op == 0x7E: s.append(int(a) & int(b))
            elif op == 0x80: s.append(int(a) | int(b))
            elif op == 0x82: s.append(int(a) ^ int(b))
        elif op == 0x74: s.append(-int(s.pop()))
        elif op == 0x78: b = int(s.pop()); a = int(s.pop()); s.append(a << (b & 31))
        elif op == 0x7A: b = int(s.pop()); a = int(s.pop()); s.append(a >> (b & 31))
        elif op == 0x7C: b = int(s.pop()); a = int(s.pop()); s.append((a & 0xFFFFFFFF) >> (b & 31))
        elif op == 0x84:
            idx = self._u8(code, frame.pc); const = self._i8(code, frame.pc + 1); frame.pc += 2; l[idx] = int(l[idx]) + const

        # comparisons / branches
        elif op in (0x99, 0x9A):
            v = int(s.pop()); off = self._i16(code, frame.pc); frame.pc += 2
            if (op == 0x99 and v == 0) or (op == 0x9A and v != 0): frame.pc = op_pc + off
        elif op in (0x9F, 0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6):
            b = s.pop(); a = s.pop(); off = self._i16(code, frame.pc); frame.pc += 2
            cond = {
                0x9F: a == b, 0xA0: a != b, 0xA1: a < b, 0xA2: a >= b,
                0xA3: a > b, 0xA4: a <= b, 0xA5: a is b, 0xA6: a is not b,
            }[op]
            if cond: frame.pc = op_pc + off
        elif op == 0xA7:
            off = self._i16(code, frame.pc); frame.pc = op_pc + off
        elif op == 0xC6 or op == 0xC7:
            obj = s.pop(); off = self._i16(code, frame.pc); frame.pc += 2
            if (op == 0xC6 and obj is None) or (op == 0xC7 and obj is not None): frame.pc = op_pc + off
        elif op == 0xC8:
            off = self._i32(code, frame.pc); frame.pc = op_pc + off

        # returns
        elif op == 0xAC or op == 0xAD or op == 0xAE or op == 0xAF or op == 0xB0 or op == 0xB1:
            ret = None if op == 0xB1 else s.pop()
            self.frames.pop()
            if self.frames:
                if ret is not None:
                    self.frames[-1].stack.append(ret)
            return ret

        # fields / constants / objects
        elif op == 0xB2:  # getstatic
            idx = self._u16(code, frame.pc); frame.pc += 2
            owner, name, desc = self.cp_fieldref(frame.klass, idx)
            val = self.get_static(owner, name, desc)
            if val is None and owner not in ("java/lang/System",):
                val = None
            s.append(val)
        elif op == 0xB3:  # putstatic
            idx = self._u16(code, frame.pc); frame.pc += 2
            owner, name, desc = self.cp_fieldref(frame.klass, idx)
            self.put_static(owner, name, desc, s.pop())
        elif op == 0xB4:  # getfield
            idx = self._u16(code, frame.pc); frame.pc += 2
            owner, name, desc = self.cp_fieldref(frame.klass, idx)
            obj = s.pop()
            if obj is None: raise JavaException("java/lang/NullPointerException")
            s.append(self.get_instance_field(obj, name, desc))
        elif op == 0xB5:  # putfield
            idx = self._u16(code, frame.pc); frame.pc += 2
            owner, name, desc = self.cp_fieldref(frame.klass, idx)
            val = s.pop(); obj = s.pop()
            if obj is None: raise JavaException("java/lang/NullPointerException")
            self.put_instance_field(obj, name, desc, val)
        elif op == 0xB0:  # handled above but retained for clarity
            pass
        elif op == 0xB7 or op == 0xB6 or op == 0xB8 or op == 0xB9:
            idx = self._u16(code, frame.pc); frame.pc += 2
            if op == 0xB9: frame.pc += 2
            owner, name, desc = self.cp_methodref(frame.klass, idx)
            argc = len(parse_method_descriptor(desc))
            args = [s.pop() for _ in range(argc)][::-1]
            obj = None
            if not (op == 0xB8 and name != "<init>"):
                # invokevirtual/invokespecial consume receiver; invokestatic doesn't.
                if op != 0xB8:
                    obj = s.pop()
            result = self.invoke(owner, name, desc, args, obj, special=(op == 0xB7))
            if method_return_type(desc) != "V" and result is not None:
                s.append(result)
        elif op == 0xBB:  # new
            idx = self._u16(code, frame.pc); frame.pc += 2
            cls_name = frame.klass.class_name(idx)
            obj = JavaObject(cls_name)
            self.heap.append(obj)
            s.append(obj)
        elif op == 0xBC or op == 0xBD:  # newarray / anewarray
            count = int(s.pop())
            if count < 0: raise JavaException("java/lang/NegativeArraySizeException")
            if op == 0xBC:
                atype = self._u8(code, frame.pc); frame.pc += 1; comp = str(atype)
            else:
                idx = self._u16(code, frame.pc); frame.pc += 2; comp = frame.klass.class_name(idx)
            arr = JavaArray([0] * count, comp); self.heap.append(arr); s.append(arr)
        elif op == 0xBE:
            arr = s.pop()
            if arr is None: raise JavaException("java/lang/NullPointerException")
            s.append(len(arr.values))
        elif op == 0xC0:
            idx = self._u16(code, frame.pc); frame.pc += 2
            # Minimal checkcast: runtime object identity is enough for current subset.
            _ = frame.klass.class_name(idx)
        elif op == 0xC1:
            idx = self._u16(code, frame.pc); frame.pc += 2
            cls_name = frame.klass.class_name(idx)
            obj = s.pop(); s.append(1 if (obj is not None and getattr(obj, "class_name", None) == cls_name) else 0)

        # null / integer conversion
        elif op == 0x01: s.append(None)
        elif op == 0x02: s.append(-1)
        elif op == 0x85: s.append(int(s.pop()))  # i2l-ish no separate width in our boxed model
        elif op == 0x86: s.append(float(s.pop()))
        elif op == 0x87: s.append(float(s.pop()))
        elif op == 0x88: s.append(int(s.pop()))
        elif op == 0x8A: s.append(int(s.pop()))
        elif op == 0x91: s.append((int(s.pop()) + 128) % 256 - 128)
        elif op == 0x92: s.append((int(s.pop()) + 128) % 256 - 128)

        else:
            raise NotImplementedError(
                f"JVM opcode 0x{op:02X} non implémenté dans {frame.klass.name}.{frame.method.name} à PC {op_pc}"
            )
        return _NO_RETURN


class _NoReturn:
    pass


_NO_RETURN = _NoReturn()


# ================================================================
# Java source compiler (small real .java -> .class compiler)
# ================================================================

class JavaCompileError(Exception):
    def __init__(self, message: str, line: int = 0, source: str = "", col: int = 0):
        self.message = message
        self.line = line
        self.source = source
        self.col = col
        super().__init__(self.__str__())

    def __str__(self):
        if self.line:
            text = f"Ligne {self.line}"
            if self.col:
                text += f", colonne {self.col}"
            text += f": {self.message}"
            if self.source:
                text += f"\n    > {self.source.strip()}"
            return text
        return self.message


@dataclass
class JToken:
    kind: str
    value: str
    line: int
    col: int
    source: str


class JavaLexer:
    MULTI = ("==", "!=", "<=", ">=", "&&", "||", "++", "--", "+=", "-=", "*=", "/=", "%=")

    def __init__(self, source: str):
        self.source = source
        self.lines = source.splitlines() or [""]
        self.i = 0
        self.line = 1
        self.col = 1

    def _peek(self, n: int = 0) -> str:
        j = self.i + n
        return self.source[j] if j < len(self.source) else ""

    def _advance(self) -> str:
        ch = self._peek()
        if not ch:
            return ""
        self.i += 1
        if ch == "\n":
            self.line += 1
            self.col = 1
        else:
            self.col += 1
        return ch

    def _error(self, message: str, line: Optional[int] = None, col: Optional[int] = None):
        ln = self.line if line is None else line
        cl = self.col if col is None else col
        src = self.lines[ln - 1] if 1 <= ln <= len(self.lines) else ""
        raise JavaCompileError(message, ln, src, cl)

    def tokenize(self) -> List[JToken]:
        out: List[JToken] = []
        keywords = {
            "public", "private", "protected", "static", "final", "class", "void", "int", "boolean",
            "String", "if", "else", "while", "for", "return", "true", "false", "new", "this",
        }
        while self.i < len(self.source):
            ch = self._peek()
            if ch.isspace():
                self._advance(); continue
            if ch == "/" and self._peek(1) == "/":
                while self._peek() not in ("", "\n"):
                    self._advance()
                continue
            if ch == "/" and self._peek(1) == "*":
                self._advance(); self._advance()
                while True:
                    if not self._peek(): self._error("commentaire /* non fermé")
                    if self._peek() == "*" and self._peek(1) == "/":
                        self._advance(); self._advance(); break
                    self._advance()
                continue
            line, col = self.line, self.col
            if ch.isalpha() or ch == "_" or ch == "$":
                buf = []
                while self._peek() and (self._peek().isalnum() or self._peek() in "_$"):
                    buf.append(self._advance())
                value = "".join(buf)
                out.append(JToken("kw" if value in keywords else "id", value, line, col, self.lines[line - 1]))
                continue
            if ch.isdigit():
                buf = []
                while self._peek() and self._peek().isdigit():
                    buf.append(self._advance())
                out.append(JToken("int", "".join(buf), line, col, self.lines[line - 1]))
                continue
            if ch in ('"', "'"):
                quote = self._advance()
                value = []
                while True:
                    c = self._peek()
                    if not c:
                        self._error("chaîne non fermée", line, col)
                    if c == quote:
                        self._advance(); break
                    if c == "\\":
                        self._advance()
                        esc = self._peek()
                        if not esc:
                            self._error("séquence d'échappement incomplète", self.line, self.col)
                        self._advance()
                        mapping = {"n": "\n", "r": "\r", "t": "\t", "b": "\b", "f": "\f", '"': '"', "'": "'", "\\": "\\"}
                        if esc in mapping:
                            value.append(mapping[esc])
                        elif esc == "u":
                            h = ""
                            for _ in range(4):
                                if not self._peek() or self._peek() not in "0123456789abcdefABCDEF":
                                    self._error("échappement Unicode \\uXXXX invalide")
                                h += self._advance()
                            value.append(chr(int(h, 16)))
                        else:
                            self._error(f"échappement inconnu: \\{esc}")
                    else:
                        if c == "\n":
                            self._error("chaîne non fermée", line, col)
                        value.append(self._advance())
                kind = "string" if quote == '"' else "char"
                if kind == "char" and len(value) != 1:
                    self._error("un caractère Java doit contenir exactement un caractère", line, col)
                out.append(JToken(kind, "".join(value), line, col, self.lines[line - 1]))
                continue

            matched = None
            for op in self.MULTI:
                if self.source.startswith(op, self.i):
                    matched = op; break
            if matched:
                for _ in matched: self._advance()
                out.append(JToken("sym", matched, line, col, self.lines[line - 1]))
                continue
            if ch in "{}()[];,.=+-*/%<>!&|":
                self._advance()
                out.append(JToken("sym", ch, line, col, self.lines[line - 1]))
                continue
            self._error(f"caractère non reconnu : {ch!r}")
        out.append(JToken("eof", "", self.line, self.col, self.lines[self.line - 1] if self.lines and 1 <= self.line <= len(self.lines) else ""))
        return out


@dataclass
class JExpr:
    kind: str
    value: Any = None
    args: List[Any] = field(default_factory=list)
    left: Any = None
    right: Any = None
    token: Optional[JToken] = None


@dataclass
class JStmt:
    kind: str
    value: Any = None
    expr: Any = None
    body: List[Any] = field(default_factory=list)
    else_body: List[Any] = field(default_factory=list)
    init: Any = None
    cond: Any = None
    update: Any = None
    token: Optional[JToken] = None


@dataclass
class JMethodDecl:
    name: str
    return_type: str
    params: List[Tuple[str, str]]
    body: List[JStmt]
    is_static: bool
    token: JToken


@dataclass
class JClassDecl:
    name: str
    methods: List[JMethodDecl]
    token: JToken


class JavaSourceParser:
    def __init__(self, source: str):
        self.tokens = JavaLexer(source).tokenize()
        self.i = 0

    def cur(self) -> JToken:
        return self.tokens[self.i]

    def peek(self, n: int = 1) -> JToken:
        return self.tokens[min(self.i + n, len(self.tokens) - 1)]

    def take(self) -> JToken:
        t = self.cur(); self.i += 1; return t

    def accept(self, value: str) -> Optional[JToken]:
        if self.cur().value == value:
            return self.take()
        return None

    def expect(self, value: str) -> JToken:
        if self.cur().value != value:
            t = self.cur()
            raise JavaCompileError(f"'{value}' attendu, trouvé {t.value!r}", t.line, t.source, t.col)
        return self.take()

    def error(self, message: str, token: Optional[JToken] = None):
        t = token or self.cur()
        raise JavaCompileError(message, t.line, t.source, t.col)

    def parse(self) -> JClassDecl:
        # package/imports are deliberately rejected with a clear message for now.
        if self.cur().value == "package":
            self.error("package n'est pas encore supporté par le compilateur Java intégré")
        if self.cur().value == "import":
            self.error("import n'est pas encore supporté par le compilateur Java intégré")

        while self.cur().value in ("public", "private", "protected", "final", "abstract"):
            self.take()
        self.expect("class")
        name = self.take()
        if name.kind != "id": self.error("nom de classe attendu", name)
        class_name = name.value
        # Optional extends/implements are rejected for this first compiler.
        if self.cur().value == "extends":
            self.error("extends n'est pas encore supporté par le compilateur Java intégré")
        if self.cur().value == "implements":
            self.error("implements n'est pas encore supporté par le compilateur Java intégré")
        self.expect("{")
        methods: List[JMethodDecl] = []
        while self.cur().value != "}":
            if self.cur().kind == "eof": self.error("'}' attendu à la fin de la classe")
            methods.append(self.parse_method())
        self.expect("}")
        if self.cur().kind != "eof": self.error("éléments inattendus après la classe")
        return JClassDecl(class_name, methods, name)

    def parse_method(self) -> JMethodDecl:
        is_static = False
        while self.cur().value in ("public", "private", "protected", "final", "static"):
            if self.cur().value == "static": is_static = True
            self.take()
        # Type then name. Constructors aren't supported.
        typ = self.take()
        if typ.value not in ("void", "int", "boolean", "String"):
            self.error("type de retour non supporté (utilisez void, int, boolean ou String)", typ)
        name = self.take()
        if name.kind != "id": self.error("nom de méthode attendu", name)
        self.expect("(")
        params: List[Tuple[str, str]] = []
        if self.cur().value != ")":
            while True:
                ptyp = self.take()
                if ptyp.value not in ("int", "boolean", "String"):
                    self.error("type de paramètre non supporté", ptyp)
                # String[] is accepted for main's args.
                if ptyp.value == "String" and self.accept("["):
                    self.expect("]")
                    ptyp_value = "String[]"
                else:
                    ptyp_value = ptyp.value
                pname = self.take()
                if pname.kind != "id": self.error("nom de paramètre attendu", pname)
                params.append((ptyp_value, pname.value))
                if not self.accept(","): break
        self.expect(")")
        body = self.parse_block()
        if is_static is False:
            self.error("seules les méthodes static sont supportées", name)
        return JMethodDecl(name.value, typ.value, params, body, is_static, name)

    def parse_block(self) -> List[JStmt]:
        self.expect("{")
        out: List[JStmt] = []
        while self.cur().value != "}":
            if self.cur().kind == "eof": self.error("'}' attendu pour fermer le bloc")
            out.append(self.parse_statement())
        self.expect("}")
        return out

    def _type_start(self, t: JToken) -> bool:
        return t.value in ("int", "boolean", "String")

    def parse_statement(self) -> JStmt:
        t = self.cur()
        if t.value == ";": self.take(); return JStmt("empty", token=t)
        if t.value == "{": return JStmt("block", body=self.parse_block(), token=t)
        if t.value == "if":
            self.take(); self.expect("("); cond = self.parse_expression(); self.expect(")")
            then = self.parse_statement_list_or_one()
            els = []
            if self.accept("else"):
                els = self.parse_statement_list_or_one()
            return JStmt("if", cond=cond, body=then, else_body=els, token=t)
        if t.value == "while":
            self.take(); self.expect("("); cond = self.parse_expression(); self.expect(")")
            return JStmt("while", cond=cond, body=self.parse_statement_list_or_one(), token=t)
        if t.value == "for":
            self.take(); self.expect("(")
            init = None
            if self.cur().value != ";":
                if self._type_start(self.cur()): init = self.parse_var_decl(False)
                else: init = self.parse_simple_statement(False)
            self.expect(";")
            cond = None if self.cur().value == ";" else self.parse_expression(); self.expect(";")
            update = None if self.cur().value == ")" else self.parse_simple_statement(False); self.expect(")")
            return JStmt("for", init=init, cond=cond, update=update, body=self.parse_statement_list_or_one(), token=t)
        if t.value == "return":
            self.take()
            expr = None if self.cur().value == ";" else self.parse_expression()
            self.expect(";")
            return JStmt("return", expr=expr, token=t)
        if t.value in ("break", "continue"):
            self.take(); self.expect(";"); return JStmt(t.value, token=t)
        if self._type_start(t):
            return self.parse_var_decl(True)
        return self.parse_simple_statement(True)

    def parse_statement_list_or_one(self) -> List[JStmt]:
        if self.cur().value == "{": return self.parse_block()
        return [self.parse_statement()]

    def parse_var_decl(self, with_semicolon: bool) -> JStmt:
        t = self.take(); typ = t.value
        # Optional [] for String arrays.
        if typ == "String" and self.accept("["):
            self.expect("]"); typ = "String[]"
        name = self.take()
        if name.kind != "id": self.error("nom de variable attendu", name)
        expr = None
        if self.accept("="):
            expr = self.parse_expression()
        if with_semicolon: self.expect(";")
        return JStmt("var", value=(typ, name.value), expr=expr, token=t)

    def parse_simple_statement(self, with_semicolon: bool) -> JStmt:
        # assignment or expression statement
        if self.cur().kind == "id" and self.peek().value in ("=", "+=", "-=", "*=", "/=", "%="):
            name = self.take(); op = self.take().value; expr = self.parse_expression()
            if with_semicolon: self.expect(";")
            return JStmt("assign", value=(name.value, op), expr=expr, token=name)
        expr = self.parse_expression()
        if with_semicolon: self.expect(";")
        return JStmt("expr", expr=expr, token=t if (t := self.tokens[self.i - 1]) else None)

    def parse_expression(self, min_prec: int = 0) -> JExpr:
        expr = self.parse_unary()
        precs = {"||":1, "&&":2, "|":3, "^":4, "&":5, "==":6, "!=":6, "<":7, "<=":7, ">":7, ">=":7,
                 "+":8, "-":8, "*":9, "/":9, "%":9}
        while self.cur().value in precs and precs[self.cur().value] >= min_prec:
            op = self.take(); p = precs[op.value]
            rhs = self.parse_expression(p + 1)
            expr = JExpr("binary", op.value, left=expr, right=rhs, token=op)
        return expr

    def parse_unary(self) -> JExpr:
        t = self.cur()
        if t.value in ("-", "!", "+"):
            self.take(); return JExpr("unary", t.value, left=self.parse_unary(), token=t)
        if t.value == "++" or t.value == "--":
            self.take(); name = self.take()
            if name.kind != "id": self.error(f"{t.value} exige une variable", name)
            return JExpr("preinc", t.value, token=t, left=JExpr("var", name.value, token=name))
        expr = self.parse_primary()
        if self.cur().value in ("++", "--"):
            op = self.take();
            if expr.kind != "var": self.error(f"{op.value} exige une variable", op)
            return JExpr("postinc", op.value, left=expr, token=op)
        return expr

    def parse_primary(self) -> JExpr:
        t = self.take()
        if t.kind == "int": return JExpr("int", int(t.value), token=t)
        if t.kind == "string": return JExpr("string", t.value, token=t)
        if t.kind == "char": return JExpr("int", ord(t.value), token=t)
        if t.value in ("true", "false"): return JExpr("bool", t.value == "true", token=t)
        if t.kind == "id":
            # System.out.println(...) / System.out.print(...) are recognized as
            # special calls understood by the miniOS JVM runtime.
            if t.value == "System" and self.cur().value == "." and self.peek().value == "out":
                self.take()  # .
                self.take()  # out
                self.expect(".")
                member = self.take()
                if member.kind != "id": self.error("méthode attendue après System.out.", member)
                self.expect("(")
                args = []
                if self.cur().value != ")":
                    while True:
                        args.append(self.parse_expression())
                        if not self.accept(","): break
                self.expect(")")
                return JExpr("member_call", ("System.out", member.value), args=args, token=member)
            # System.getProperty(...) / System.getenv(...) : virtual system data.
            if t.value == "System" and self.cur().value == ".":
                self.take()
                member = self.take()
                if member.kind != "id": self.error("membre attendu après System.", member)
                if self.accept("("):
                    args = []
                    if self.cur().value != ")":
                        while True:
                            args.append(self.parse_expression())
                            if not self.accept(","): break
                    self.expect(")")
                    return JExpr("member_call", ("System", member.value), args=args, token=member)
                return JExpr("member", ("System", member.value), token=member)
            if self.accept("("):
                args = []
                if self.cur().value != ")":
                    while True:
                        args.append(self.parse_expression())
                        if not self.accept(","): break
                self.expect(")")
                return JExpr("call", t.value, args=args, token=t)
            if self.cur().value == ".":
                # Generic one-level member access, currently limited to fields
                # on System for clear error reporting.
                self.take()
                member = self.take()
                if member.kind != "id": self.error("membre attendu après '.'", member)
                return JExpr("member", (t.value, member.value), token=member)
            return JExpr("var", t.value, token=t)
        if t.value == "(":
            e = self.parse_expression(); self.expect(")"); return e
        self.error(f"expression inattendue : {t.value!r}", t)
        raise AssertionError


class ClassFileBuilder:
    def __init__(self):
        self.cp: List[Tuple[int, Any]] = [None]  # type: ignore
        self.cache: Dict[Tuple[Any, ...], int] = {}

    def _add(self, key: Tuple[Any, ...], tag: int, value: Any, slots: int = 1) -> int:
        if key in self.cache: return self.cache[key]
        idx = len(self.cp)
        self.cp.append((tag, value))
        if slots == 2: self.cp.append(None)  # long/double reservation
        self.cache[key] = idx
        return idx

    def utf8(self, s: str) -> int:
        return self._add((1, s), 1, s)

    def cls(self, name: str) -> int:
        return self._add((7, name), 7, self.utf8(name))

    def string(self, value: str) -> int:
        return self._add((8, value), 8, self.utf8(value))

    def integer(self, value: int) -> int:
        return self._add((3, int(value)), 3, int(value))

    def name_type(self, name: str, desc: str) -> int:
        return self._add((12, name, desc), 12, (self.utf8(name), self.utf8(desc)))

    def fieldref(self, owner: str, name: str, desc: str) -> int:
        return self._add((9, owner, name, desc), 9, (self.cls(owner), self.name_type(name, desc)))

    def methodref(self, owner: str, name: str, desc: str) -> int:
        return self._add((10, owner, name, desc), 10, (self.cls(owner), self.name_type(name, desc)))

    def classfile(self, this_name: str, methods: List[Tuple[str, str, int, int, bytes]], source_name: str = "") -> bytes:
        # Tous les éléments du constant pool doivent être ajoutés AVANT d'écrire
        # cp_count dans le classfile.
        this_idx = self.cls(this_name)
        super_idx = self.cls("java/lang/Object")
        code_name = self.utf8("Code")
        method_indices = []
        for name, desc, _access, _max_stack, _code in methods:
            method_indices.append((self.utf8(name), self.utf8(desc)))
        out = io.BytesIO()
        out.write(b"\xCA\xFE\xBA\xBE")
        out.write(struct.pack(">HH", 0, 65))  # Java 21 classfile
        out.write(struct.pack(">H", len(self.cp)))
        for e in self.cp[1:]:
            if e is None: continue
            tag, value = e
            out.write(bytes([tag]))
            if tag == 1:
                raw = value.encode("utf-8")
                out.write(struct.pack(">H", len(raw))); out.write(raw)
            elif tag == 3:
                out.write(struct.pack(">i", int(value)))
            elif tag == 7 or tag == 8:
                out.write(struct.pack(">H", value))
            elif tag == 9 or tag == 10 or tag == 11 or tag == 12:
                out.write(struct.pack(">HH", *value))
            else:
                raise ValueError(f"CP tag non supporté par le compilateur: {tag}")
        out.write(struct.pack(">HHH", 0x0021, this_idx, super_idx))  # public + super
        out.write(struct.pack(">H", 0))  # interfaces
        out.write(struct.pack(">H", 0))  # fields
        out.write(struct.pack(">H", len(methods)))
        for (name, desc, access, max_stack, code), (ni, di) in zip(methods, method_indices):
            out.write(struct.pack(">HHHH", access, ni, di, 1))
            body = struct.pack(">HHI", max_stack, 64, len(code)) + code + struct.pack(">HH", 0, 0)
            out.write(struct.pack(">HI", code_name, len(body))); out.write(body)
        out.write(struct.pack(">H", 0))
        return out.getvalue()


class JavaMethodCompiler:
    def __init__(self, cp: ClassFileBuilder, class_name: str, methods: List[JMethodDecl]):
        self.cp = cp
        self.class_name = class_name
        self.methods = methods
        self.method_map = {m.name: m for m in methods}
        self.labels: Dict[str, int] = {}
        self.fixups: List[Tuple[int, str, int]] = []
        self.code = bytearray()
        self.locals: Dict[str, Tuple[int, str]] = {}
        self.next_local = 0
        self.break_labels: List[str] = []
        self.continue_labels: List[str] = []
        self.label_counter = 0

    def label(self) -> str:
        x = f"L{self.label_counter}"; self.label_counter += 1; return x

    def mark(self, name: str): self.labels[name] = len(self.code)

    def emit(self, *bs: int): self.code.extend(bytes(bs))
    def emit_u16(self, x: int): self.code.extend(struct.pack(">H", x & 0xFFFF))

    def branch(self, opcode: int, label: str):
        pos = len(self.code); self.emit(opcode, 0, 0); self.fixups.append((pos, label, 2))

    def patch(self):
        for pos, label, width in self.fixups:
            if label not in self.labels: raise JavaCompileError(f"label interne introuvable: {label}")
            off = self.labels[label] - pos
            if not -32768 <= off <= 32767: raise JavaCompileError("méthode Java trop grande pour un branchement court")
            self.code[pos + 1:pos + 3] = struct.pack(">h", off)

    def load(self, slot: int, typ: str):
        if 0 <= slot <= 3:
            base = {"int":0x1A, "boolean":0x1A, "String":0x2A}[typ]
            self.emit(base + slot)
        else:
            op = 0x19 if typ == "String" or typ == "String[]" else 0x15
            self.emit(op, slot)

    def store(self, slot: int, typ: str):
        if 0 <= slot <= 3:
            base = 0x4B if typ == "String" or typ == "String[]" else 0x3B
            self.emit(base + slot)
        else:
            self.emit(0x3A if typ == "String" or typ == "String[]" else 0x36, slot)

    def declare(self, name: str, typ: str):
        if name in self.locals: raise JavaCompileError(f"variable déjà déclarée : {name}")
        slot = self.next_local; self.next_local += 1
        self.locals[name] = (slot, typ)
        return slot

    def lookup(self, expr: JExpr) -> Tuple[int, str]:
        if expr.value not in self.locals: raise JavaCompileError(f"variable inconnue : {expr.value}", expr.token.line, expr.token.source, expr.token.col)
        return self.locals[expr.value]

    def push_int(self, n: int):
        if -1 <= n <= 5: self.emit(0x03 + n)
        elif -128 <= n <= 127: self.emit(0x10, n & 0xFF)
        elif -32768 <= n <= 32767: self.emit(0x11); self.code.extend(struct.pack(">h", n))
        else: self.emit(0x13); self.emit_u16(self.cp.integer(n))

    def emit_expr(self, e: JExpr) -> str:
        if e.kind == "int": self.push_int(int(e.value)); return "int"
        if e.kind == "bool": self.push_int(1 if e.value else 0); return "boolean"
        if e.kind == "string": self.emit(0x12, self.cp.string(str(e.value))); return "String"
        if e.kind == "var":
            slot, typ = self.lookup(e); self.load(slot, typ); return typ
        if e.kind in ("preinc", "postinc"):
            slot, typ = self.lookup(e.left)
            if typ not in ("int", "boolean"): raise JavaCompileError("++/-- exige une variable entière", e.token.line, e.token.source, e.token.col)
            if e.kind == "postinc": self.load(slot, typ)
            self.emit(0x84, slot & 0xFF, 1 if e.value == "++" else 0xFF)
            if e.kind == "preinc": self.load(slot, typ)
            return "int"
        if e.kind == "unary":
            typ = self.emit_expr(e.left)
            if e.value == "-": self.emit(0x74); return "int"
            if e.value == "!": self.push_int(1); self.emit(0x82); return "boolean"
            return typ
        if e.kind == "binary":
            op = e.value
            if op in ("&&", "||"):
                # Eager boolean logic (no Java short-circuit side effects in this first compiler).
                self.emit_expr(e.left); self.emit_expr(e.right); self.emit(0x7E if op == "&&" else 0x80); return "boolean"
            lt = self.emit_expr(e.left); rt = self.emit_expr(e.right)
            if op == "+":
                if lt == "String" and rt == "String":
                    ref = self.cp.methodref("java/lang/String", "concat", "(Ljava/lang/String;)Ljava/lang/String;")
                    self.emit(0xB6); self.emit_u16(ref); return "String"
                if lt == "int" and rt == "int": self.emit(0x60); return "int"
                raise JavaCompileError("+ ne supporte que int+int ou String+String", e.token.line, e.token.source, e.token.col)
            if lt != "int" and lt != "boolean": raise JavaCompileError(f"opérateur {op} : type gauche non supporté", e.token.line, e.token.source, e.token.col)
            if rt != "int" and rt != "boolean": raise JavaCompileError(f"opérateur {op} : type droit non supporté", e.token.line, e.token.source, e.token.col)
            arith = {"-":0x64,"*":0x68,"/":0x6C,"%":None,"&":0x7E,"|":0x80,"^":0x82}
            if op in arith and op not in ("%",): self.emit(arith[op]); return "int"
            if op == "%":
                self.emit(0x6C)  # temporary placeholder replaced below by idiv is not enough
                # Replace last opcode with a tiny irem-free implementation is impossible without extra opcodes;
                # keep modulo unsupported in Java compiler rather than emit incorrect bytecode.
                self.code[-1] = 0x6C
                raise JavaCompileError("% n'est pas encore supporté par javac miniOS 0.5")
            if op in ("==","!=","<","<=",">",">="):
                true_label = self.label(); end_label = self.label()
                branch_op = {"==":0x9F,"!=":0xA0,"<":0xA1,"<=":0xA4,">":0xA3,">=":0xA2}[op]
                self.branch(branch_op, true_label); self.push_int(0); self.branch(0xA7, end_label); self.mark(true_label); self.push_int(1); self.mark(end_label); return "boolean"
            raise JavaCompileError(f"opérateur non supporté : {op}", e.token.line, e.token.source, e.token.col)
        if e.kind == "call":
            if e.value == "println" or e.value == "print":
                raise JavaCompileError("utilisez System.out.println(...) ou System.out.print(...)", e.token.line, e.token.source, e.token.col)
            # miniOS-specific interactive API:
            #   input([prompt]) -> String
            #   inputInt([prompt]) -> int
            if e.value in ("input", "inputInt"):
                expected_types = {"input": ("String", 0xB8, "Ljava/lang/String;", "miniOS/Runtime", "readLine"),
                                  "inputInt": ("int", 0xB8, "I", "miniOS/Runtime", "readInt")}
                ret_type, opcode, ret_desc, owner, native_name = expected_types[e.value]
                if len(e.args) > 1:
                    raise JavaCompileError(f"{e.value}() accepte zéro ou un argument", e.token.line, e.token.source, e.token.col)
                argdesc = ""
                if e.args:
                    typ = self.emit_expr(e.args[0])
                    if typ != "String":
                        raise JavaCompileError(f"{e.value}() attend un texte comme invite", e.args[0].token.line, e.args[0].token.source, e.args[0].token.col)
                    argdesc = "Ljava/lang/String;"
                desc = f"({argdesc}){ret_desc}"
                ref = self.cp.methodref(owner, native_name, desc)
                self.emit(opcode); self.emit_u16(ref)
                return ret_type
            m = self.method_map.get(e.value)
            if m is None: raise JavaCompileError(f"méthode inconnue : {e.value}", e.token.line, e.token.source, e.token.col)
            if not m.is_static: raise JavaCompileError("seules les méthodes static sont supportées", e.token.line, e.token.source, e.token.col)
            if len(e.args) != len(m.params): raise JavaCompileError(f"{e.value}() attend {len(m.params)} argument(s)", e.token.line, e.token.source, e.token.col)
            desc_parts=[]
            for arg, (typ, _) in zip(e.args, m.params):
                got=self.emit_expr(arg)
                if typ != got and not (typ == "int" and got == "boolean") and not (typ == "boolean" and got == "int"):
                    raise JavaCompileError(f"type incompatible pour l'argument de {e.value}()", arg.token.line, arg.token.source, arg.token.col)
                desc_parts.append({"int":"I","boolean":"Z","String":"Ljava/lang/String;","String[]":"[Ljava/lang/String;"}[typ])
            desc = "(" + "".join(desc_parts) + ")" + {"void":"V","int":"I","boolean":"Z","String":"Ljava/lang/String;"}[m.return_type]
            ref = self.cp.methodref(self.class_name, m.name, desc)
            self.emit(0xB8); self.emit_u16(ref)
            return m.return_type
        if e.kind == "member_call":
            obj_name, method = e.value
            if obj_name == "System":
                if method not in ("getProperty", "getenv"):
                    raise JavaCompileError(f"System.{method}() n'est pas supporté", e.token.line, e.token.source, e.token.col)
                if len(e.args) != 1:
                    raise JavaCompileError(f"System.{method}() attend exactement 1 argument", e.token.line, e.token.source, e.token.col)
                typ = self.emit_expr(e.args[0])
                if typ != "String":
                    raise JavaCompileError(f"System.{method}() attend une clé String", e.args[0].token.line, e.args[0].token.source, e.args[0].token.col)
                desc = "(Ljava/lang/String;)Ljava/lang/String;"
                ref = self.cp.methodref("java/lang/System", method, desc)
                self.emit(0xB8); self.emit_u16(ref)
                return "String"
            if obj_name == "System.out":
                if method not in ("print", "println"):
                    raise JavaCompileError(f"System.out.{method}() n'est pas supporté", e.token.line, e.token.source, e.token.col)
                # handled as a statement in emit_stmt; expression form is invalid
                raise JavaCompileError("System.out.print/println doit être utilisé comme instruction", e.token.line, e.token.source, e.token.col)
            raise JavaCompileError(f"appel membre non supporté : {obj_name}.{method}()", e.token.line, e.token.source, e.token.col)
        if e.kind == "member":
            owner, member = e.value
            if owner != "System" or member != "out":
                raise JavaCompileError(f"membre non supporté : {owner}.{member}", e.token.line, e.token.source, e.token.col)
            ref = self.cp.fieldref("java/lang/System", "out", "Ljava/io/PrintStream;")
            self.emit(0xB2); self.emit_u16(ref); return "PrintStream"
        raise JavaCompileError(f"expression interne Java inconnue : {e.kind}", e.token.line if e.token else 0)

    def emit_print(self, member: str, args: List[JExpr], token: JToken):
        if len(args) == 0: typ = "void"
        elif len(args) == 1: typ = self.emit_expr(args[0])
        else: raise JavaCompileError(f"System.out.{member} attend 0 ou 1 argument", token.line, token.source, token.col)
        if typ == "void":
            desc = "()V"
        elif typ == "int": desc = "(I)V"
        elif typ == "boolean": desc = "(Z)V"
        elif typ == "String": desc = "(Ljava/lang/String;)V"
        else: raise JavaCompileError(f"type non supporté dans System.out.{member}: {typ}", token.line, token.source, token.col)
        # Need getstatic before argument, so if expression emitted first, move is tricky.
        # This method is called from member-call AST special path; for correctness it is handled there.

    def emit_stmt(self, s: JStmt):
        if s.kind == "empty": return
        if s.kind == "block":
            for x in s.body: self.emit_stmt(x)
            return
        if s.kind == "var":
            typ, name = s.value; slot = self.declare(name, typ)
            if s.expr is None:
                if typ in ("int", "boolean"): self.push_int(0)
                elif typ == "String": self.emit(0x01)
                elif typ == "String[]": self.emit(0x01)
            else:
                got = self.emit_expr(s.expr)
                if typ != got and not (typ == "int" and got == "boolean") and not (typ == "boolean" and got == "int"):
                    raise JavaCompileError(f"type incompatible pour {name}: {typ} <- {got}", s.token.line, s.token.source, s.token.col)
            self.store(slot, typ); return
        if s.kind == "assign":
            name, op = s.value
            if name not in self.locals: raise JavaCompileError(f"variable inconnue : {name}", s.token.line, s.token.source, s.token.col)
            slot, typ = self.locals[name]
            if op == "=":
                got=self.emit_expr(s.expr)
            else:
                self.load(slot, typ); got=self.emit_expr(s.expr)
                if typ not in ("int","boolean") or got not in ("int","boolean"):
                    raise JavaCompileError(f"{op} exige des entiers", s.token.line, s.token.source, s.token.col)
                self.emit({"+=":0x60,"-=":0x64,"*=":0x68,"/=":0x6C}[op])
            if typ != got and not (typ == "int" and got == "boolean") and not (typ == "boolean" and got == "int"):
                raise JavaCompileError(f"type incompatible pour {name}", s.token.line, s.token.source, s.token.col)
            self.store(slot, typ); return
        if s.kind == "expr":
            # Special-case System.out.print/println before normal expression codegen.
            e=s.expr
            if e.kind == "member_call" and e.value[0] == "System.out" and e.value[1] in ("print","println"):
                ref_field=self.cp.fieldref("java/lang/System","out","Ljava/io/PrintStream;")
                self.emit(0xB2); self.emit_u16(ref_field)
                if len(e.args)==0:
                    desc="()V"
                elif len(e.args)==1:
                    typ=self.emit_expr(e.args[0])
                    desc={"int":"(I)V","boolean":"(Z)V","String":"(Ljava/lang/String;)V"}.get(typ)
                    if desc is None: raise JavaCompileError(f"System.out.{e.value[1]}: type {typ} non supporté", e.token.line, e.token.source, e.token.col)
                else:
                    raise JavaCompileError("System.out.print/println accepte au plus un argument", e.token.line, e.token.source, e.token.col)
                ref=self.cp.methodref("java/io/PrintStream",e.value[1],desc)
                self.emit(0xB6); self.emit_u16(ref)
                return
            typ=self.emit_expr(e)
            if typ != "void": self.emit(0x57)
            return
        if s.kind == "if":
            else_label=self.label(); end_label=self.label()
            self.emit_condition(s.cond, else_label)
            for x in s.body: self.emit_stmt(x)
            if s.else_body:
                self.branch(0xA7,end_label)
                self.mark(else_label)
                for x in s.else_body: self.emit_stmt(x)
                self.mark(end_label)
            else: self.mark(else_label)
            return
        if s.kind == "while":
            start=self.label(); end=self.label(); self.mark(start); self.continue_labels.append(start); self.break_labels.append(end)
            self.emit_condition(s.cond,end)
            for x in s.body:self.emit_stmt(x)
            self.branch(0xA7,start); self.mark(end); self.break_labels.pop(); self.continue_labels.pop(); return
        if s.kind == "for":
            if s.init:self.emit_stmt(s.init)
            start=self.label(); cont=self.label(); end=self.label(); self.mark(start); self.continue_labels.append(cont); self.break_labels.append(end)
            if s.cond:self.emit_condition(s.cond,end)
            for x in s.body:self.emit_stmt(x)
            self.mark(cont)
            if s.update:self.emit_stmt(s.update)
            self.branch(0xA7,start); self.mark(end); self.break_labels.pop(); self.continue_labels.pop(); return
        if s.kind == "break":
            if not self.break_labels: raise JavaCompileError("break en dehors d'une boucle", s.token.line, s.token.source, s.token.col)
            self.branch(0xA7,self.break_labels[-1]); return
        if s.kind == "continue":
            if not self.continue_labels: raise JavaCompileError("continue en dehors d'une boucle", s.token.line, s.token.source, s.token.col)
            self.branch(0xA7,self.continue_labels[-1]); return
        if s.kind == "return":
            if self.current_return == "void":
                if s.expr is not None: raise JavaCompileError("return avec valeur dans une méthode void", s.token.line, s.token.source, s.token.col)
                self.emit(0xB1)
            else:
                if s.expr is None: raise JavaCompileError("return sans valeur", s.token.line, s.token.source, s.token.col)
                typ=self.emit_expr(s.expr)
                if typ != self.current_return and not (self.current_return == "int" and typ == "boolean") and not (self.current_return == "boolean" and typ == "int"):
                    raise JavaCompileError("type de retour incompatible", s.token.line, s.token.source, s.token.col)
                self.emit(0xAC if self.current_return in ("int","boolean") else 0xB0)
            return
        raise JavaCompileError(f"instruction Java non supportée : {s.kind}", s.token.line if s.token else 0)

    def emit_condition(self, e: JExpr, false_label: str):
        typ=self.emit_expr(e)
        if typ not in ("int","boolean"): raise JavaCompileError("la condition doit être boolean/int", e.token.line, e.token.source, e.token.col)
        self.branch(0x99,false_label)

    def compile_method(self, m: JMethodDecl) -> Tuple[str,str,int,int,bytes]:
        self.labels.clear(); self.fixups.clear(); self.code.clear(); self.locals.clear(); self.next_local=0; self.break_labels=[]; self.continue_labels=[]; self.label_counter=0
        self.current_return=m.return_type
        for typ,name in m.params:
            self.declare(name,typ)
        for s in m.body:self.emit_stmt(s)
        if m.return_type == "void": self.emit(0xB1)
        self.patch()
        desc = "(" + "".join({"int":"I","boolean":"Z","String":"Ljava/lang/String;","String[]":"[Ljava/lang/String;"}[t] for t,_ in m.params) + ")" + {"void":"V","int":"I","boolean":"Z","String":"Ljava/lang/String;"}[m.return_type]
        max_stack = 64
        max_locals = max(self.next_local, 1)
        return m.name, desc, 0x0009 if m.is_static else 0x0001, max_stack, bytes(self.code)


class JavaSourceCompiler:
    """Compiles a deliberately small but real Java subset into JVM classfile 65."""
    def compile(self, source: str, expected_class_name: Optional[str] = None, source_name: str = "<memory>") -> Tuple[str, bytes]:
        decl = JavaSourceParser(source).parse()
        if expected_class_name and decl.name != expected_class_name:
            raise JavaCompileError(f"le nom de classe public '{decl.name}' ne correspond pas au fichier '{expected_class_name}.java'")
        main_methods=[m for m in decl.methods if m.name == "main"]
        if not main_methods:
            raise JavaCompileError("méthode main absente : ajoutez public static void main(String[] args) {...}", decl.token.line, decl.token.source, decl.token.col)
        main=main_methods[0]
        if main.return_type != "void" or len(main.params) != 1 or main.params[0][0] != "String[]":
            raise JavaCompileError("main doit être: public static void main(String[] args)", main.token.line, main.token.source, main.token.col)
        cp=ClassFileBuilder()
        compiled=[]
        for m in decl.methods:
            compiled.append(JavaMethodCompiler(cp,decl.name,decl.methods).compile_method(m))
        return decl.name, cp.classfile(decl.name,compiled,source_name)


# ================================================================
# MiniOS shell
# ================================================================

class MiniOS:
    def __init__(self):
        self.disk = VirtualDisk()
        self.cwd = "/home/user"
        self.boot_time = time.time()
        self.next_pid = 1
        self.processes: Dict[int, VirtualProcess] = {}
        self.jvm = JVM(self)
        self.graphics = GraphicsManager(self)
        self.shutdown_requested = False
        self.exit_requested = False
        self.history: List[str] = []
        self.process_lock = threading.RLock()
        self.command_lock = threading.RLock()
        self.console_input_lock = threading.RLock()
        self.env = {
            "PATH": "/bin:/path:/apps",
            "HOME": "/home/user",
            "SHELL": "minios-shell",
            "HOSTNAME": HOSTNAME,
        }

    # ------------------ path / command helpers ------------------
    def resolve(self, p: str, cwd: Optional[str] = None) -> str:
        return self.disk.norm(p, self.cwd if cwd is None else cwd)

    def resolve_host_path(self, p: str) -> str:
        """Resolve a path on the real host filesystem.

        Windows paths such as ``C:\\Users\\name\\file`` are kept intact.
        This is important because the miniOS shell has its own path resolver,
        which must never reinterpret a host path as a virtual path.
        """
        p = str(p)
        # A Windows drive path / UNC path must not have its backslashes treated
        # as shell escapes or virtual separators. On Windows, os.path.abspath
        # handles these natively; ntpath is used for recognition/normalization.
        if re.match(r"^[A-Za-z]:[\\/]", p) or p.startswith("\\\\"):
            if os.name == "nt":
                return os.path.abspath(os.path.expandvars(os.path.expanduser(p)))
            return ntpath.normpath(os.path.expandvars(os.path.expanduser(p)))
        return os.path.abspath(os.path.expandvars(os.path.expanduser(p)))

    def virtual_exists_file(self, p: str) -> bool:
        rp = self.resolve(p)
        return rp in self.disk.files

    @staticmethod
    def _has_wildcard(value: str) -> bool:
        """True if a path contains shell-style wildcard metacharacters."""
        return any(ch in str(value) for ch in ("*", "?", "["))

    @staticmethod
    def _component_glob_match(path: str, pattern: str) -> bool:
        """Match virtual POSIX paths component by component.

        Unlike fnmatch on the whole path, '*' does not cross '/' here.
        '**' matches zero or more path components.
        """
        p_parts = [x for x in pattern.strip("/").split("/") if x != ""]
        v_parts = [x for x in path.strip("/").split("/") if x != ""]

        def rec(pi: int, vi: int) -> bool:
            if pi == len(p_parts):
                return vi == len(v_parts)
            part = p_parts[pi]
            if part == "**":
                if rec(pi + 1, vi):
                    return True
                return vi < len(v_parts) and rec(pi, vi + 1)
            return (
                vi < len(v_parts)
                and fnmatchcase(v_parts[vi], part)
                and rec(pi + 1, vi + 1)
            )

        return rec(0, 0)

    def expand_virtual(self, pattern: str, *, files_only: bool = False,
                       dirs_only: bool = False) -> List[str]:
        """Expand a virtual shell pattern such as '*.mini'.

        With no wildcard, returns the normalized path only when it exists.
        With a wildcard, returns matching files/directories in sorted order.
        """
        pattern = str(pattern)
        rp = self.resolve(pattern)
        if not self._has_wildcard(pattern):
            if rp in self.disk.files or rp in self.disk.dirs:
                if files_only and rp not in self.disk.files:
                    return []
                if dirs_only and rp not in self.disk.dirs:
                    return []
                return [rp]
            return []

        matches: List[str] = []
        for candidate in sorted(self.disk.dirs):
            if self._component_glob_match(candidate, rp):
                if not files_only and candidate not in matches:
                    matches.append(candidate)
        for candidate in sorted(self.disk.files):
            if self._component_glob_match(candidate, rp):
                if not dirs_only and candidate not in matches:
                    matches.append(candidate)
        return sorted(matches)

    def expand_host_files(self, pattern: str) -> List[str]:
        """Expand a real-host wildcard pattern to files only."""
        hp = self.resolve_host_path(pattern)
        if self._has_wildcard(pattern):
            return sorted([x for x in glob.glob(hp, recursive=True) if os.path.isfile(x)])
        return [hp] if os.path.isfile(hp) else []

    def search_path(self, command: str, cwd: Optional[str] = None) -> Optional[str]:
        """Find a VM32 .mexe, d'abord dans le cwd fourni puis dans PATH."""
        command = str(command).replace("\\", "/")
        cwd = self.cwd if cwd is None else self.resolve(cwd)
        has_slash = "/" in command
        candidates: List[str] = []

        # Avec un nom simple (ex: ``run dd``), un vrai shell peut utiliser
        # le dossier courant lorsqu'on l'autorise. miniOS le fait ici pour
        # rendre ``run dd`` et ``dd`` pratiques.
        if not has_slash and not command.startswith("."):
            local_base = cwd.rstrip("/") + "/" + command
            candidates.append(local_base)
            if not command.lower().endswith(".mexe"):
                candidates.append(local_base + ".mexe")

            # Puis recherche classique dans PATH : /bin, /path, /apps...
            for directory in self.env.get("PATH", "").split(":"):
                if not directory:
                    continue
                base = directory.rstrip("/") + "/" + command
                candidates.append(base)
                if not command.lower().endswith(".mexe"):
                    candidates.append(base + ".mexe")
        else:
            candidates.extend([
                command,
                command + ".mexe" if not command.lower().endswith(".mexe") else command,
            ])

        seen = set()
        for candidate in candidates:
            rp = self.resolve(candidate)
            if rp in seen:
                continue
            seen.add(rp)
            if rp in self.disk.files and not self.disk.is_dir(rp):
                return rp
        return None

    def tokenize(self, line: str) -> List[str]:
        """Tokenize a miniOS command without destroying Windows backslashes.

        ``shlex.split`` in POSIX mode interprets a backslash as an escape character,
        turning ``C:\\Users\\2nd2`` into ``C:Users2nd2``. miniOS must instead
        preserve Windows host paths while still supporting quotes.
        """
        try:
            tokens: List[str] = []
            buf: List[str] = []
            quote: Optional[str] = None
            i = 0

            while i < len(line):
                ch = line[i]
                if quote is not None:
                    if ch == quote:
                        quote = None
                    else:
                        buf.append(ch)
                    i += 1
                    continue

                if ch in ("\"", "'"):
                    quote = ch
                    i += 1
                    continue

                if ch.isspace():
                    if buf:
                        tokens.append("".join(buf))
                        buf.clear()
                    i += 1
                    continue

                # Backslash is an ordinary character in miniOS commands.
                # This preserves C:\\Users\\... exactly as entered.
                buf.append(ch)
                i += 1

            if quote is not None:
                raise ValueError("guillemet non fermé")
            if buf:
                tokens.append("".join(buf))
            return tokens
        except ValueError as e:
            print(f"Erreur de syntaxe: {e}")
            return []

    # ------------------ VM32 ------------------
    def _create_process(self, path: str, args: Optional[List[str]] = None, stdin_data: Optional[str] = None, debug: bool = False) -> VirtualProcess:
        path = self.resolve(path)
        if path not in self.disk.files:
            raise FileNotFoundError(path)
        data = self.disk.read(path)
        if isinstance(data, str):
            data = data.encode("utf-8")
        exe = MEXE.decode(data)
        with self.process_lock:
            pid = self.next_pid
            self.next_pid += 1
            proc = VirtualProcess(
                pid, os.path.basename(path), exe, os_ref=self, argv=list(args or []),
                cwd=self.cwd, stdin_data=stdin_data, stdin_pipe=(stdin_data is not None), debug=debug
            )
            self.processes[pid] = proc
        return proc

    def _run_virtual_mexe(self, path: str, quiet: bool = False, args: Optional[List[str]] = None, background: bool = False, stdin_data: Optional[str] = None, debug: bool = False) -> int:
        proc = self._create_process(path, args=args, stdin_data=stdin_data, debug=debug)
        if background:
            proc.start_background()
            print(f"[VM32] PID={proc.pid} lancé en arrière-plan: {proc.name}")
            if proc.debug_log_path:
                print(f"[DEBUG] journal: {proc.debug_log_path}")
            return proc.pid
        try:
            if proc.debug_log_path:
                print(f"[DEBUG] journal: {proc.debug_log_path}")
            code = proc.run()
            if not quiet:
                print(f"[VM32] PID={proc.pid} terminé (code={code})")
            return int(code or 0)
        except Exception as e:
            if not quiet:
                print(f"[VM32] PID={proc.pid} CRASH: {e}")
            raise

    def _create_process_from_exe(self, name: str, exe: MEXE, args: Optional[List[str]] = None, stdin_data: Optional[str] = None, debug: bool = False) -> VirtualProcess:
        """Enregistre un processus à partir d'un MEXE déjà décodé, sans fichier requis."""
        with self.process_lock:
            pid = self.next_pid
            self.next_pid += 1
            proc = VirtualProcess(
                pid, name, exe, os_ref=self, argv=list(args or []),
                cwd=self.cwd, stdin_data=stdin_data, stdin_pipe=(stdin_data is not None), debug=debug
            )
            self.processes[pid] = proc
        return proc

    def _read_mini_source(self, target: str) -> Tuple[str, str]:
        """Lit un fichier MiniLang depuis le disque virtuel ou le PC hôte.

        Un chemin relatif privilégie le disque virtuel courant. Un chemin
        virtuel absolu (/...) est également recherché directement dans miniOS.
        Sinon, le chemin est interprété comme chemin réel du PC.
        """
        raw_arg = str(target)
        virtual_path = self.resolve(raw_arg)

        # Priorité au disque virtuel pour les chemins relatifs et /...
        if virtual_path in self.disk.files and not self.disk.is_dir(virtual_path):
            data = self.disk.read(virtual_path)
            if isinstance(data, bytes):
                raw, converted_rtf = maybe_decode_rtf(data)
                source = decode_text_bytes(raw)
                if converted_rtf:
                    self.disk.write(virtual_path, raw)
            else:
                source = str(data)
            return source, virtual_path

        # Sinon lecture sur le PC hôte.
        host_path = self.resolve_host_path(raw_arg)
        if os.path.isfile(host_path):
            with open(host_path, "rb") as f:
                raw = f.read()
            raw, _ = maybe_decode_rtf(raw)
            return decode_text_bytes(raw), host_path

        raise FileNotFoundError(target)

    def _run_mini_source(self, source: str, source_name: str, args: Optional[List[str]] = None,
                         background: bool = False, stdin_data: Optional[str] = None, debug: bool = False) -> int:
        """Compile un source MiniLang en mémoire puis l'exécute comme un MEXE."""
        exe = MiniLang.compile_placeholder(source)
        proc = self._create_process_from_exe(os.path.basename(source_name), exe, args=args, stdin_data=stdin_data, debug=debug)
        if background:
            proc.start_background()
            print(f"[MiniLang] PID={proc.pid} lancé en arrière-plan: {proc.name}")
            if proc.debug_log_path:
                print(f"[DEBUG] journal: {proc.debug_log_path}")
            return proc.pid
        try:
            if proc.debug_log_path:
                print(f"[DEBUG] journal: {proc.debug_log_path}")
            code = proc.run()
            print(f"[MiniLang] PID={proc.pid} terminé (code={code})")
            return int(code or 0)
        except Exception as e:
            print(f"[MiniLang] PID={proc.pid} CRASH: {e}")
            raise

    def cmd_run(self, args: List[str], stdin_data: Optional[str] = None):
        if not args:
            print("Usage: run [-debug|-debg] <programme> [args...] [&]")
            print("       run [-debug|-debg] -mini <fichier.mini> [args...] [&]")
            return

        background = args[-1] == "&"
        if background:
            args = args[:-1]
        debug_mode = False
        debug_flags = {"-debug", "--debug", "-debg", "--debg"}
        kept = []
        for item in args:
            if str(item).lower() in debug_flags:
                debug_mode = True
            else:
                kept.append(item)
        args = kept
        if not args:
            print("Usage: run [-debug|-debg] <programme> [args...] [&]")
            print("       run [-debug|-debg] -mini <fichier.mini> [args...] [&]")
            return

        # Mode MiniLang source : compilation en mémoire, sans créer de .mexe.
        if args[0].lower() == "-mini":
            if len(args) < 2:
                print("Usage: run -mini <fichier.mini> [args...] [&]")
                return
            target = args[1]
            if not target.lower().endswith(".mini"):
                print(f"run -mini: fichier source attendu avec l'extension .mini: {target}")
                return
            try:
                source, source_name = self._read_mini_source(target)
                self._run_mini_source(source, source_name, args=args[2:],
                                      background=background, stdin_data=stdin_data, debug=debug_mode)
            except MiniLangCompileError as e:
                self._report_compile_error(e)
            except FileNotFoundError:
                print(f"run -mini: fichier introuvable: {target}")
            except Exception as e:
                print(f"run -mini: {e}")
            return

        target = args[0]
        path = self.search_path(target, self.cwd) if "/" not in target and not target.startswith(".") else self.resolve(target)
        if not path:
            print(f"run: programme introuvable: {target}")
            return
        try:
            self._run_virtual_mexe(path, args=args[1:], background=background, stdin_data=stdin_data, debug=debug_mode)
        except Exception as e:
            print(f"run: {e}")

    def cmd_exec(self, args: List[str]):
        self.cmd_run(args)

    def cmd_wait(self, args: List[str]):
        if not args:
            print("Usage: wait <pid>")
            return
        try:
            pid = int(args[0])
            proc = self.processes.get(pid)
            if not proc:
                print("wait: PID introuvable")
                return
            proc.done_event.wait()
            print(f"PID {pid}: {proc.state} code={proc.exit_code if proc.exit_code is not None else 0}")
        except ValueError:
            print("wait: PID invalide")

    def cmd_which(self, args: List[str]):
        if not args:
            print("Usage: which <commande>")
            return
        cmd = args[0]
        handlers = {
            "help", "clear", "echo", "uname", "version", "whoami", "hostname", "uptime", "date",
            "reboot", "shutdown", "exit", "ls", "cd", "pwd", "mkdir", "rmdir", "touch", "cat",
            "write", "edit", "append", "rm", "cp", "mv", "find", "tree", "stat", "head", "tail", "wc",
            "run", "exec", "wait", "jobs", "java", "javac", "ps", "kill", "debug", "gdebug", "newapp", "compile", "build", "apps",
            "install", "uninstall", "mem", "cpu", "regs", "stack", "heap", "info", "disk", "path",
            "env", "set", "history", "import", "export", "net", "ifconfig", "ipconfig", "ping", "nslookup", "netstat", "route", "networktest", "test", "which", "helpfile",
        }
        if cmd.lower() in handlers:
            print(f"builtin {cmd}")
            return
        found = self.search_path(cmd)
        if found:
            print(found)
        else:
            print(f"which: {cmd}: introuvable")

    def cmd_path(self, args: List[str]):
        print("PATH=" + self.env.get("PATH", ""))
        print("Répertoires exécutables:")
        for d in self.env.get("PATH", "").split(":"):
            print(f"  {d}")

    def cmd_env(self, args: List[str]):
        for k, v in sorted(self.env.items()):
            print(f"{k}={v}")

    def cmd_set(self, args: List[str]):
        if not args or "=" not in args[0]:
            print("Usage: set NOM=VALEUR")
            return
        key, value = args[0].split("=", 1)
        key = key.strip()
        if not key:
            print("set: nom invalide")
            return
        self.env[key] = value
        print(f"{key}={value}")

    def cmd_history(self, args: List[str]):
        for i, line in enumerate(self.history[-100:], 1):
            print(f"{i:>4}  {line}")

    def cmd_download(self, args: List[str]):
        """Télécharge une ressource HTTP/HTTPS vers le disque virtuel."""
        if len(args) < 2 or len(args) > 3:
            print("Usage: download <url> <fichier> [timeout]")
            return 2

        url = str(args[0]).strip()
        path = self.resolve(str(args[1]))
        timeout = 15.0
        if len(args) == 3:
            try:
                timeout = max(1.0, min(300.0, float(args[2])))
            except ValueError:
                print("download: délai invalide (secondes)")
                return 2

        if not url.lower().startswith(("http://", "https://")):
            print("download: seuls http:// et https:// sont acceptés")
            return 2

        try:
            _status, _headers, body = Syscalls._http_get(url, timeout)
            if len(body) > 8 * 1024 * 1024:
                print("download: fichier trop grand (maximum 8 MiB)")
                return 1
            self.disk.write(path, body)
            print(f"download: {url} -> {path} ({len(body)} octets)")
            return 0
        except Exception as exc:
            print(f"download: erreur: {exc}")
            return 1

    def cmd_import(self, args: List[str]):
        if not args:
            print("Usage: import <fichier_réel|motif> [chemin_virtuel]")
            return

        source_arg = str(args[0])
        hosts = self.expand_host_files(source_arg)
        if not hosts:
            host = self.resolve_host_path(source_arg)
            print(f"import: fichier(s) réel(s) introuvable(s): {host}")
            return

        destination_arg = str(args[1]) if len(args) > 1 else None
        multi = len(hosts) > 1
        if destination_arg is None:
            destination_is_dir = True
            destination = self.cwd
        else:
            destination = self.resolve(destination_arg)
            destination_is_dir = self.disk.is_dir(destination) or destination_arg.endswith(("/", "\\"))
            if multi and not destination_is_dir:
                print("import: un motif correspondant à plusieurs fichiers nécessite un dossier virtuel destination")
                return
            if destination_is_dir and not self.disk.is_dir(destination):
                self.disk.mkdir(destination, parents=True)

        for host in hosts:
            try:
                vpath = (destination.rstrip("/") + "/" + os.path.basename(host)) if destination_is_dir else destination
                with open(host, "rb") as f:
                    data = f.read()
                data, converted_rtf = normalize_imported_text(data, host)
                self.disk.write(vpath, data)
                suffix = " [RTF converti en UTF-8]" if converted_rtf else ""
                if not converted_rtf and (os.path.splitext(host)[1].lower() in TEXT_EXTENSIONS):
                    suffix = " [texte normalisé en UTF-8]"
                print(f"import: {host} -> {vpath} ({len(data)} octets){suffix}")
            except Exception as e:
                print(f"import: {host}: {e}")


    def cmd_export(self, args: List[str]):
        if len(args) < 2:
            print("Usage: export <fichier_virtuel|motif> <fichier_réel_ou_dossier>")
            return

        matches = self.expand_virtual(args[0], files_only=True)
        if not matches:
            print(f"export: aucun fichier virtuel ne correspond à: {args[0]}")
            return

        destination_arg = str(args[1])
        host_destination = self.resolve_host_path(destination_arg)
        multi = len(matches) > 1
        is_dir_destination = os.path.isdir(host_destination) or destination_arg.endswith(("/", "\\"))
        if multi and not is_dir_destination:
            print("export: un motif correspondant à plusieurs fichiers nécessite un dossier réel destination")
            return
        if is_dir_destination:
            os.makedirs(host_destination, exist_ok=True)

        for vpath in matches:
            host = os.path.join(host_destination, os.path.basename(vpath)) if is_dir_destination else host_destination
            parent = os.path.dirname(host)
            if parent:
                os.makedirs(parent, exist_ok=True)
            data = self.disk.read(vpath)
            if isinstance(data, bytes):
                raw = data
                if os.path.splitext(vpath)[1].lower() in TEXT_EXTENSIONS:
                    raw = encode_text_utf8(decode_text_bytes(raw))
            else:
                raw = encode_text_utf8(str(data))
            try:
                with open(host, "wb") as f:
                    f.write(raw)
                print(f"export: {vpath} -> {host} ({len(raw)} octets)")
            except PermissionError:
                print(f"export: permission refusée: {host}")
            except IsADirectoryError:
                print(f"export: la destination est un dossier: {host}")


    def _execute_path_command(self, cmd: str, args: List[str], stdin_data: Optional[str] = None) -> bool:
        path = self.search_path(cmd, self.cwd)
        if not path:
            return False
        background = bool(args and args[-1] == "&")
        run_args = args[:-1] if background else args
        try:
            self._run_virtual_mexe(path, args=run_args, background=background, stdin_data=stdin_data)
        except Exception as e:
            print(f"{cmd}: impossible d'exécuter {path}: {e}")
        return True

    # ------------------ Java ------------------
    def _compile_java_source(self, source: str, source_name: str = "<memory>", expected_name: Optional[str] = None) -> Tuple[str, bytes]:
        source, _ = maybe_decode_rtf(source.encode("utf-8"))
        text_source = decode_text_bytes(source)
        return JavaSourceCompiler().compile(text_source, expected_name, source_name)

    def cmd_javac(self, args: List[str]):
        if not args:
            print("Usage: javac <fichier.java> [sortie.class]")
            return
        src_arg = args[0]
        try:
            host = self.resolve_host_path(src_arg)
            host_source = os.path.isfile(host)
            if host_source:
                with open(host, "rb") as f:
                    raw = f.read()
                raw, converted = maybe_decode_rtf(raw)
                source = decode_text_bytes(raw)
                expected = os.path.splitext(os.path.basename(host))[0]
                name, blob = JavaSourceCompiler().compile(source, expected, host)
                out = self.resolve_host_path(args[1]) if len(args) > 1 else os.path.splitext(host)[0] + ".class"
                os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
                with open(out, "wb") as f: f.write(blob)
                if converted: print(f"[JAVAC] RTF détecté et converti: {host}")
                print(f"[JAVAC] compilé: {out}")
                return

            vpath = self.resolve(src_arg)
            if not self.disk.exists(vpath) or self.disk.is_dir(vpath):
                print(f"javac: source introuvable: {src_arg}")
                return
            data = self.disk.read(vpath)
            raw = data if isinstance(data, bytes) else str(data).encode("utf-8")
            raw, converted = maybe_decode_rtf(raw)
            source = decode_text_bytes(raw)
            expected = os.path.splitext(os.path.basename(vpath))[0]
            name, blob = JavaSourceCompiler().compile(source, expected, vpath)
            out_v = self.resolve(args[1]) if len(args) > 1 else self.resolve(os.path.splitext(vpath)[0] + ".class")
            self.disk.write(out_v, blob)
            if converted:
                self.disk.write(vpath, source)
                print(f"[JAVAC] RTF détecté et converti: {vpath}")
            print(f"[JAVAC] compilé: {out_v}")
        except JavaCompileError as e:
            print("\x1b[31m[JAVAC] ERREUR\x1b[0m")
            print(f"[JAVAC] {e}")
        except Exception as e:
            print(f"[JAVAC] ERREUR: {e}")

    def _load_virtual_java_source(self, vpath: str) -> Tuple[JVMClass, str]:
        data = self.disk.read(vpath)
        raw = data if isinstance(data, bytes) else str(data).encode("utf-8")
        raw, converted = maybe_decode_rtf(raw)
        source = decode_text_bytes(raw)
        expected = os.path.splitext(os.path.basename(vpath))[0]
        name, blob = JavaSourceCompiler().compile(source, expected, vpath)
        self.jvm.loader.load_class_bytes(vpath + "[compiled]", blob, vpath)
        klass = self.jvm.loader.get(name)
        assert klass is not None
        self.jvm.register(klass)
        return klass, source

    def cmd_java(self, args: List[str]):
        if not args:
            print("Usage: java <fichier.class|fichier.jar> [arguments...]")
            print("       java <Classe>       (classe déjà chargée)")
            return

        # Dans miniOS, comme avec java classique, le premier argument après
        # 'java' désigne le programme à lancer. Les arguments suivants sont
        # transmis à main(String[] args).
        target = args[0]
        if target.lower().endswith(".java"):
            try:
                host = self.resolve_host_path(target)
                if os.path.isfile(host):
                    with open(host, "rb") as f: raw = f.read()
                    raw, _ = maybe_decode_rtf(raw)
                    source = decode_text_bytes(raw)
                    expected = os.path.splitext(os.path.basename(host))[0]
                    name, blob = JavaSourceCompiler().compile(source, expected, host)
                    klass = self.jvm.loader.load_class_bytes(host + "[source-run]", blob, host)
                    self.jvm.register(klass)
                else:
                    vpath = self.resolve(target)
                    if not self.disk.exists(vpath) or self.disk.is_dir(vpath):
                        print(f"java: fichier source introuvable: {target}")
                        return
                    klass, _ = self._load_virtual_java_source(vpath)
                print(f"[JAVAC] source compilé en mémoire: {klass.name}.class")
                code = self.jvm.run_main(klass, args[1:])
                print(f"[JVM] programme terminé (code={code})")
            except JavaCompileError as e:
                print("\x1b[31m[JAVAC] ERREUR\x1b[0m")
                print(f"[JAVAC] {e}")
            except Exception as e:
                print(f"[JVM] EXCEPTION: {e}")
            return
        host = self.resolve_host_path(target)
        # For convenience, also allow files copied into the virtual filesystem by reading their bytes.
        if os.path.isfile(host):
            try:
                klass = self.jvm.load_any(host)
            except Exception as e:
                print(f"[JVM] Chargement impossible: {e}")
                return
        else:
            vpath = self.resolve(target)
            if self.disk.exists(vpath) and not self.disk.is_dir(vpath):
                blob = self.disk.read(vpath)
                if isinstance(blob, str): blob = blob.encode()
                try:
                    if target.lower().endswith(".class"):
                        klass = self.jvm.loader.load_class_bytes(vpath, bytes(blob), vpath)
                    elif target.lower().endswith(".jar"):
                        # JAR in virtual filesystem.
                        tmp = io.BytesIO(bytes(blob))
                        with zipfile.ZipFile(tmp) as z:
                            main = None
                            try:
                                mf = z.read("META-INF/MANIFEST.MF").decode(errors="replace")
                                for line in mf.splitlines():
                                    if line.lower().startswith("main-class:"):
                                        main = line.split(":", 1)[1].strip().replace(".", "/")
                            except KeyError:
                                pass
                            for info in z.infolist():
                                if info.filename.endswith(".class"):
                                    k = JVMClass.parse(z.read(info), f"{vpath}!/{info.filename}")
                                    self.jvm.register(k)
                            if not main:
                                raise JavaException("java/lang/NoSuchMethodException", "Main-Class absent")
                            klass = self.jvm.load_class(main)
                    else:
                        raise ValueError("extension Java inconnue")
                except Exception as e:
                    print(f"[JVM] Chargement impossible: {e}")
                    return
            else:
                print(f"java: fichier introuvable: {target}")
                return

        print(f"[JVM] {klass.name} | classfile {klass.major}.{klass.minor} | source={klass.source}")
        try:
            code = self.jvm.run_main(klass, args[1:])
            print(f"[JVM] programme terminé (code={code})")
        except Exception as e:
            print(f"[JVM] EXCEPTION: {e}")

    # ------------------ filesystem ------------------
    def cmd_ls(self, args):
        path_arg = args[0] if args else self.cwd
        try:
            matches = self.expand_virtual(path_arg)
            if self._has_wildcard(path_arg):
                if not matches:
                    print(f"ls: aucun fichier ou répertoire ne correspond à: {path_arg}")
                    return
                for match in matches:
                    if match in self.disk.dirs:
                        print(match + "/")
                    else:
                        print(match)
                return
            path = self.resolve(path_arg)
            for name, isdir in self.disk.ls(path, self.cwd):
                print(name + ("/" if isdir else ""))
        except Exception as e:
            print(f"ls: {e}")

    def cmd_cd(self, args):
        p = args[0] if args else "/home/user"
        rp = self.resolve(p)
        if not self.disk.is_dir(rp):
            print(f"cd: pas un répertoire: {rp}")
            return
        self.cwd = rp
        print(self.cwd)

    def cmd_pwd(self, args):
        print(self.cwd)

    def cmd_mkdir(self, args):
        if not args:
            print("Usage: mkdir [-p] <dir>")
            return
        parents = any(a in ("-p", "--parents") for a in args)
        targets = [a for a in args if a not in ("-p", "--parents")]
        if len(targets) != 1:
            print("Usage: mkdir [-p] <dir>")
            return
        try:
            p = self.resolve(targets[0])
            self.disk.mkdir(p, parents=parents)
            print(f"mkdir: {p}")
        except Exception as e:
            print(f"mkdir: {e}")

    def cmd_rmdir(self, args):
        if len(args) != 1:
            print("Usage: rmdir <dir|motif>")
            return
        pattern = args[0]
        try:
            matches = self.expand_virtual(pattern, dirs_only=True)
            if not matches:
                print(f"rmdir: répertoire introuvable: {pattern}")
                return
            for p in matches:
                self.disk.delete(p, recursive=False)
                print(f"rmdir: {p}")
        except Exception as e:
            print(f"rmdir: {e}")

    def cmd_touch(self, args):
        if not args:
            print("Usage: touch <fichier>")
            return
        p = self.resolve(args[0])
        if self.disk.exists(p) and self.disk.is_dir(p):
            print("touch: répertoire")
            return
        if not self.disk.exists(p):
            self.disk.write(p, "")

    def cmd_cat(self, args):
        if not args:
            print("Usage: cat <fichier|motif>")
            return
        try:
            matches = self.expand_virtual(args[0], files_only=True)
            if not matches:
                print(f"cat: fichier introuvable: {args[0]}")
                return
            for p in matches:
                x = self.disk.read(p)
                if isinstance(x, bytes):
                    sys.stdout.buffer.write(x)
                    sys.stdout.buffer.flush()
                    if not x.endswith(b"\n"):
                        print()
                else:
                    print(x, end="" if str(x).endswith("\n") else "\n")
        except Exception as e:
            print(f"cat: {e}")

    def _write_editor(self, p: str, initial: str = ""):
        """Simple cross-platform multi-line editor used by write/edit."""
        print(f"Éditeur miniOS — {p}")
        print("  .save   enregistrer et quitter")
        print("  .cancel annuler")
        print("  .show   afficher le contenu courant")
        print("  .clear  effacer tout le contenu")
        print("  .editligne X   éditer directement la ligne X")
        print("Entrez votre texte ligne par ligne :")

        lines = initial.splitlines() if initial else []
        if lines:
            print("--- contenu existant ---")
            for i, line in enumerate(lines, 1):
                print(f"{i:04d} | {line}")
            print("--- nouvelles lignes à la fin ---")

        while True:
            try:
                line = input(f"{len(lines) + 1:04d} | ")
            except EOFError:
                print("\nÉditeur fermé par EOF ; fichier enregistré.")
                break
            except KeyboardInterrupt:
                print("\nÉditeur annulé.")
                return False

            if line == ".save":
                break
            if line == ".cancel":
                print("Éditeur annulé : aucune modification enregistrée.")
                return False
            if line == ".show":
                print("--- contenu ---")
                for i, item in enumerate(lines, 1):
                    print(f"{i:04d} | {item}")
                print("--- fin ---")
                continue
            if line == ".clear":
                lines.clear()
                print("Contenu effacé.")
                continue
            if line.startswith(".editligne"):
                parts = line.split(None, 1)
                if len(parts) != 2:
                    print("Usage : .editligne <numero_de_ligne>")
                    continue
                try:
                    line_no = int(parts[1].strip())
                except ValueError:
                    print(".editligne : numéro de ligne invalide")
                    continue
                if line_no < 1 or line_no > len(lines):
                    print(f".editligne : ligne {line_no} inexistante (1-{len(lines)})")
                    continue
                old_line = lines[line_no - 1]
                print(f"Ligne {line_no} actuelle : {old_line}")
                try:
                    replacement = input(f"{line_no:04d} | ")
                except EOFError:
                    print(".editligne : édition annulée par EOF")
                    continue
                except KeyboardInterrupt:
                    print(".editligne : édition annulée")
                    continue
                if replacement == ".cancel":
                    print(".editligne : édition annulée")
                    continue
                lines[line_no - 1] = replacement
                print(f"Ligne {line_no} modifiée.")
                continue
            lines.append(line)

        content = "\n".join(lines)
        if lines:
            content += "\n"
        self.disk.write(p, content)
        print(f"Écrit : {p} ({len(content.encode('utf-8'))} octets)")
        return True

    def cmd_write(self, args):
        if not args:
            print("Usage: write <fichier> [texte]")
            print("       write <fichier> --line <ligne> [texte]")
            print("Sans texte, ouvre l'éditeur multi-lignes.")
            return

        p = self.resolve(args[0])
        if self.disk.is_dir(p):
            print(f"write: {p}: est un répertoire")
            return

        # Remplacement ciblé d'une ligne :
        #   write fichier.mini --line 12 nouveau contenu
        # Les numéros de ligne sont 1-based.
        if len(args) >= 3 and args[1] in ("-l", "--line", "--ligne"):
            try:
                line_no = int(args[2])
            except ValueError:
                print("write: numéro de ligne invalide")
                return
            if line_no < 1:
                print("write: le numéro de ligne doit être supérieur ou égal à 1")
                return
            if not self.disk.exists(p):
                print(f"write: fichier introuvable: {p}")
                return
            try:
                old = self.disk.read(p)
                if isinstance(old, bytes):
                    old = decode_text_bytes(old)
                old = str(old)
                had_final_newline = old.endswith("\n")
                lines = old.splitlines()
                if line_no > len(lines):
                    print(f"write: ligne {line_no} inexistante (fichier: {len(lines)} ligne(s))")
                    return
                replacement = " ".join(args[3:]) if len(args) > 3 else ""
                lines[line_no - 1] = replacement
                content = "\n".join(lines)
                if had_final_newline:
                    content += "\n"
                self.disk.write(p, content)
                print(f"Écrit : {p} (ligne {line_no} remplacée)")
            except Exception as e:
                print(f"write: {e}")
            return

        if len(args) == 1:
            self._write_editor(p, "")
            return

        self.disk.write(p, " ".join(args[1:]))
        print(f"Écrit : {p}")

    def cmd_edit(self, args):
        """Éditeur de fichier avec sélection optionnelle d'une ligne.

        Formes acceptées :
          edit <fichier>
          edit <fichier> -l <ligne>
          edit <fichier> -l <ligne> <nouveau texte...>
        Quand aucun nouveau texte n'est fourni avec --line/-l, la nouvelle
        ligne est demandée interactively. Les numéros de ligne commencent à 1.
        """
        if not args:
            print("Usage: edit <fichier> -l <ligne> [texte]")
            return

        p = self.resolve(args[0])
        if self.disk.is_dir(p):
            print(f"edit: {p}: est un répertoire")
            return

        line_no = None
        text_parts = []
        i = 1
        while i < len(args):
            a = args[i]
            if a in ("-l", "--line"):
                if i + 1 >= len(args):
                    print("edit: argument manquant après --line/-l")
                    return
                try:
                    line_no = int(args[i + 1])
                except ValueError:
                    print("edit: numéro de ligne invalide")
                    return
                i += 2
                text_parts = args[i:]
                break
            elif i == 1 and a.isdigit():
                # Alias pratique : edit fichier 5
                line_no = int(a)
                text_parts = args[2:]
                break
            else:
                print("Usage: edit <fichier> -l <ligne> [texte]")
                return

        try:
            old = self.disk.read(p) if self.disk.exists(p) else ""
            if isinstance(old, bytes):
                old = decode_text_bytes(old)
            old = str(old)

            if line_no is None:
                self._write_editor(p, old)
                return

            if line_no < 1:
                print("edit: le numéro de ligne doit être supérieur ou égal à 1")
                return

            had_final_newline = old.endswith("\n")
            lines = old.splitlines()
            if line_no > len(lines):
                print(f"edit: ligne {line_no} inexistante (1-{len(lines)})")
                return

            old_line = lines[line_no - 1]
            print(f"Ligne {line_no} actuelle : {old_line}")

            if text_parts:
                replacement = " ".join(text_parts)
            else:
                try:
                    replacement = input(f"{line_no:04d} | ")
                except (EOFError, KeyboardInterrupt):
                    print("edit: édition annulée")
                    return

            if replacement == ".cancel":
                print("edit: édition annulée")
                return

            lines[line_no - 1] = replacement
            content = "\n".join(lines)
            if had_final_newline:
                content += "\n"
            self.disk.write(p, content)
            print(f"edit: ligne {line_no} modifiée dans {p}")
        except Exception as e:
            print(f"edit: {e}")

    def cmd_append(self, args):
        if not args:
            print("Usage: append <fichier|motif> [texte]")
            return
        pattern = args[0]
        if len(args) == 1 and self._has_wildcard(pattern):
            print("append: un motif nécessite un texte explicite; l'éditeur ne peut pas modifier plusieurs fichiers à la fois")
            return
        if len(args) == 1:
            p = self.resolve(pattern)
            try:
                old = self.disk.read(p) if self.disk.exists(p) else ""
                if isinstance(old, bytes):
                    old = decode_text_bytes(old)
                self._write_editor(p, str(old))
            except Exception as e:
                print(f"append: {e}")
            return
        matches = self.expand_virtual(pattern, files_only=True)
        if not matches:
            print(f"append: fichier introuvable: {pattern}")
            return
        data = " ".join(args[1:])
        for p in matches:
            self.disk.append(p, data)
            print(f"append: {p}")

    def cmd_rm(self, args):
        if not args:
            print("Usage: rm [-r] <fichier|dossier|motif>")
            return
        recursive = any(a in ("-r", "-R", "--recursive") for a in args)
        targets = [a for a in args if a not in ("-r", "-R", "--recursive")]
        if not targets:
            print("Usage: rm [-r] <fichier|dossier|motif> [...]")
            return
        for pattern in targets:
            try:
                matches = self.expand_virtual(pattern)
                if not matches:
                    print(f"rm: introuvable: {pattern}")
                    continue
                for p in sorted(matches, key=len, reverse=True):
                    self.disk.delete(p, recursive=recursive)
                    print(f"rm: {p}")
            except Exception as e:
                print(f"rm: {pattern}: {e}")

    def cmd_cp(self, args):
        if len(args) != 2:
            print("Usage: cp <source|motif> <destination>")
            return
        source_arg, destination_arg = args
        matches = self.expand_virtual(source_arg)
        if not matches:
            print(f"cp: source introuvable: {source_arg}")
            return
        destination = self.resolve(destination_arg)
        multi = len(matches) > 1
        if multi and not self.disk.is_dir(destination):
            print("cp: plusieurs sources nécessitent un répertoire destination")
            return
        try:
            for src in matches:
                dst = destination if not self.disk.is_dir(destination) else destination.rstrip("/") + "/" + os.path.basename(src)
                self.disk.copy(src, dst)
                print(f"cp: {src} -> {dst}")
        except Exception as e:
            print(f"cp: {e}")

    def cmd_mv(self, args):
        if len(args) != 2:
            print("Usage: mv <source|motif> <destination>")
            return
        source_arg, destination_arg = args
        matches = self.expand_virtual(source_arg)
        if not matches:
            print(f"mv: source introuvable: {source_arg}")
            return
        destination = self.resolve(destination_arg)
        multi = len(matches) > 1
        if multi and not self.disk.is_dir(destination):
            print("mv: plusieurs sources nécessitent un répertoire destination")
            return
        try:
            for src in matches:
                dst = destination if not self.disk.is_dir(destination) else destination.rstrip("/") + "/" + os.path.basename(src)
                self.disk.move(src, dst)
                print(f"mv: {src} -> {dst}")
        except Exception as e:
            print(f"mv: {e}")

    def cmd_find(self, args):
        start = self.resolve(args[0]) if args else self.cwd
        needle = args[1] if len(args) > 1 else ""
        for d in sorted(self.disk.dirs):
            if d == start or d.startswith(start.rstrip("/") + "/"):
                if needle in os.path.basename(d):
                    print(d)
        for f in sorted(self.disk.files):
            if f == start or f.startswith(start.rstrip("/") + "/"):
                if needle in os.path.basename(f):
                    print(f)

    def cmd_tree(self, args):
        start = self.resolve(args[0]) if args else self.cwd
        def rec(p: str, indent: str = ""):
            print(indent + ("/" if p == "/" else os.path.basename(p) + "/"))
            try:
                items = self.disk.ls(p, self.cwd)
            except Exception:
                return
            for name, isdir in items:
                child = p.rstrip("/") + "/" + name
                if isdir:
                    rec(child, indent + "  ")
                else:
                    print(indent + "  " + name)
        rec(start)

    def cmd_stat(self, args):
        if not args:
            print("Usage: stat <path|motif>")
            return
        matches = self.expand_virtual(args[0])
        if not matches:
            print("stat: introuvable")
            return
        for p in matches:
            if p in self.disk.dirs:
                print(f"type=directory path={p}")
            elif p in self.disk.files:
                data = self.disk.files[p]
                n = len(data if isinstance(data, bytes) else str(data).encode())
                print(f"type=file path={p} size={n}")

    def cmd_head_tail_wc(self, cmd: str, args: List[str]):
        if not args:
            print(f"Usage: {cmd} <fichier|motif>")
            return
        try:
            matches = self.expand_virtual(args[-1], files_only=True)
            if not matches:
                print(f"{cmd}: fichier introuvable: {args[-1]}")
                return
            for p in matches:
                data = self.disk.read(p)
                text_ = decode_text_bytes(data) if isinstance(data, bytes) else str(data)
                lines = text_.splitlines(True)
                if len(matches) > 1:
                    print(f"==> {p} <==")
                if cmd == "head":
                    print("".join(lines[:10]), end="")
                elif cmd == "tail":
                    print("".join(lines[-10:]), end="")
                else:
                    print(len(text_.split()), len(lines), len(text_.encode()))
                if len(matches) > 1:
                    print()
        except Exception as e:
            print(f"{cmd}: {e}")

    # ------------------ system ------------------
    def _minilang_help_text(self) -> str:
        """Génère la documentation complète de MiniLang à partir des fonctions natives."""
        docs = {
            "print": ("print(expression[, end=fin[, flush=bool]])", "Affiche une expression; end personnalise ce qui est écrit après la valeur. flush est accepté pour compatibilité Python et les sorties VM32 sont déjà immédiates."),
            "input": ("input([question])", "Lit une chaîne saisie par l'utilisateur."),
            "inputInt": ("inputInt([question])", "Lit un entier; redemande si la saisie est invalide."),
            "len": ("len(valeur)", "Retourne la longueur d'une chaîne ou d'un tableau."),
            "int": ("int(valeur)", "Convertit une valeur en entier."),
            "str": ("str(valeur)", "Convertit une valeur en chaîne."),
            "system": ("system(cle)", "Retourne une information du système miniOS."),
            "env": ("env(nom)", "Lit une variable d'environnement virtuelle."),
            "envSet": ("envSet(nom, valeur)", "Définit une variable d'environnement virtuelle."),
            "exists": ("exists(chemin)", "Teste l'existence d'un fichier ou répertoire virtuel."),
            "isDir": ("isDir(chemin)", "Teste si un chemin virtuel est un répertoire."),
            "read": ("read(chemin)", "Lit un fichier texte du disque virtuel."),
            "write": ("write(chemin, texte)", "Crée ou remplace un fichier virtuel."),
            "append": ("append(chemin, texte)", "Ajoute du texte à un fichier virtuel."),
            "mkdir": ("mkdir(chemin[, parents])", "Crée un répertoire virtuel; parents active la création des parents."),
            "remove": ("remove(chemin[, recursive])", "Supprime un fichier/répertoire; recursive autorise la suppression récursive."),
            "copy": ("copy(source, destination)", "Copie un fichier ou répertoire virtuel."),
            "move": ("move(source, destination)", "Déplace ou renomme un fichier ou répertoire virtuel."),
            "fileSize": ("fileSize(chemin)", "Retourne la taille d'un fichier en octets."),
            "fileByte": ("fileByte(chemin, index)", "Lit un octet d'un fichier."),
            "setFileByte": ("setFileByte(chemin, index, valeur)", "Modifie un octet d'un fichier."),
            "list": ("list(chemin)", "Retourne le contenu d'un répertoire sous forme de chaîne."),
            "shell": ("shell(commande)", "Exécute une commande du terminal miniOS."),
            "run": ("run(programme[, arg1, arg2, arg3, arg4])", "Lance un programme VM32 et retourne son code."),
            "sleep": ("sleep(ms)", "Suspend le processus pendant un nombre de millisecondes."),
            "time": ("time()", "Retourne le temps Unix en secondes."),
            "timeMs": ("timeMs()", "Retourne le temps Unix en millisecondes."),
            "random": ("random(max)", "Retourne un entier aléatoire dans [0, max)."),
            "randomRange": ("randomRange(min, max)", "Retourne un entier aléatoire entre min et max."),
            "argc": ("argc()", "Retourne le nombre d'arguments du programme."),
            "arg": ("arg(index)", "Retourne un argument du programme."),
            "cwd": ("cwd()", "Retourne le dossier courant du processus."),
            "chdir": ("chdir(chemin)", "Change le dossier courant du processus."),
            "array": ("array(taille)", "Crée un tableau d'entiers."),
            "arrayLen": ("arrayLen(tableau)", "Retourne la taille d'un tableau."),
            "arrayGet": ("arrayGet(tableau, index)", "Lit un entier dans un tableau."),
            "arraySet": ("arraySet(tableau, index, valeur)", "Écrit un entier dans un tableau."),
            "arrayGetStr": ("arrayGetStr(tableau, index)", "Lit une valeur de tableau comme chaîne."),
            "arraySetStr": ("arraySetStr(tableau, index, valeur)", "Écrit une valeur chaîne dans un tableau."),
            "split": ("split(texte, separateur)", "Découpe un texte et retourne un tableau de chaînes."),
            "join": ("join(tableau, separateur)", "Assemble un tableau de chaînes."),
            "substr": ("substr(texte, debut[, longueur])", "Retourne une sous-chaîne."),
            "replace": ("replace(texte, ancien, nouveau)", "Remplace toutes les occurrences d'un texte."),
            "contains": ("contains(texte, morceau)", "Teste si un texte contient un morceau."),
            "startsWith": ("startsWith(texte, prefixe)", "Teste le préfixe d'un texte."),
            "endsWith": ("endsWith(texte, suffixe)", "Teste le suffixe d'un texte."),
            "lower": ("lower(texte)", "Convertit en minuscules."),
            "upper": ("upper(texte)", "Convertit en majuscules."),
            "trim": ("trim(texte)", "Retire les espaces aux extrémités."),
            "chr": ("chr(code)", "Retourne le caractère Unicode correspondant au code."),
            "ord": ("ord(texte)", "Retourne le code du premier caractère."),
            "read8": ("read8(adresse)", "Lit 8 bits dans la mémoire VM32."),
            "read32": ("read32(adresse)", "Lit 32 bits dans la mémoire VM32."),
            "write8": ("write8(adresse, valeur)", "Écrit 8 bits dans la mémoire VM32."),
            "write32": ("write32(adresse, valeur)", "Écrit 32 bits dans la mémoire VM32."),
            "alloc": ("alloc(taille)", "Alloue une zone de mémoire VM32."),
            "free": ("free(adresse)", "Libère une zone de mémoire VM32. Retourne 0 si la libération réussit, 1 si l'adresse est invalide."),
            "memTotal": ("memTotal()", "Retourne la RAM VM32 totale."),
            "memFree": ("memFree()", "Retourne la RAM VM32 libre exposée."),
            "system": ("system(cle)", "Retourne une propriété de miniOS."),
            "ping": ("ping(hote)", "Effectue un ping réel vers le réseau de la machine hôte; retourne 0 si joignable et 1 sinon."),
            "httpGet": ("httpGet(url[, timeout])", "Effectue une requête HTTP/HTTPS GET et retourne le corps texte."),
            "httpPost": ("httpPost(url, corps[, typeContenu[, timeout]])", "Envoie une requête HTTP/HTTPS POST et retourne le corps texte de réponse."),
            "httpDownload": ("httpDownload(url, chemin[, timeout])", "Télécharge une ressource HTTP/HTTPS vers le disque virtuel et retourne sa taille."),
            "download": ("download(url, chemin[, timeout])", "Alias de httpDownload : télécharge une ressource HTTP/HTTPS vers le disque virtuel et retourne sa taille."),
            "dnsResolve": ("dnsResolve(hote)", "Résout un nom DNS avec le réseau réel du système hôte."),
            "tcpConnect": ("tcpConnect(hote, port[, timeout])", "Ouvre une connexion TCP réelle vers Internet/réseau et retourne un handle."),
            "tcpSend": ("tcpSend(handle, texte)", "Envoie des octets UTF-8 sur une connexion TCP."),
            "tcpRecv": ("tcpRecv(handle[, maxOctets[, timeout]])", "Reçoit des octets TCP et les retourne comme chaîne UTF-8."),
            "tcpClose": ("tcpClose(handle)", "Ferme un socket TCP; retourne 0 si succès, 1 sinon."),
            "tcpIsOpen": ("tcpIsOpen(handle)", "Teste si un handle TCP appartient toujours au processus."),
            "udpOpen": ("udpOpen()", "Crée un socket UDP réel."),
            "udpSend": ("udpSend(handle, hote, port, texte)", "Envoie des données UTF-8 par UDP."),
            "udpRecv": ("udpRecv(handle[, maxOctets[, timeout]])", "Reçoit un datagramme UDP comme chaîne UTF-8."),
            "udpClose": ("udpClose(handle)", "Ferme un socket UDP; retourne 0 si succès, 1 sinon."),
            "pid": ("pid()", "Retourne le PID courant."),
            "program": ("program()", "Retourne le nom du programme courant."),
            "hostname": ("hostname()", "Retourne le nom de la machine miniOS."),
            "importHost": ("importHost(fichierReel, fichierVirtuel)", "Copie un fichier du PC réel vers le disque virtuel."),
            "exportHost": ("exportHost(fichierVirtuel, fichierReel)", "Copie un fichier virtuel vers le PC réel."),
            "hostExists": ("hostExists(cheminReel)", "Teste l'existence d'un chemin sur le PC réel."),
            "hostRead": ("hostRead(cheminReel)", "Lit un fichier texte du PC réel."),
            "hostWrite": ("hostWrite(cheminReel, texte)", "Écrit un fichier texte sur le PC réel."),
            "hostAppend": ("hostAppend(cheminReel, texte)", "Ajoute du texte à un fichier réel."),
            "hostDelete": ("hostDelete(cheminReel)", "Supprime un fichier du PC réel."),
            "hostMkdir": ("hostMkdir(repertoireReel)", "Crée un répertoire sur le PC réel."),
            "hostList": ("hostList(repertoireReel)", "Liste un répertoire du PC réel."),
            "hostIsDir": ("hostIsDir(cheminReel)", "Teste si un chemin réel est un répertoire."),
            "hostSize": ("hostSize(cheminReel)", "Retourne la taille d'un fichier réel."),
            "exec": ("exec(commande)", "Exécute une commande miniOS et capture sa sortie."),
            "command": ("command(commande)", "Alias de shell(commande)."),
            "sysf": ("sysf(fonction[, arg1, ..., arg5])", "Appelle indirectement une fonction système native; le nom doit être une chaîne littérale."),
            "window": ("window(titre, largeur, hauteur)", "Crée une fenêtre graphique."),
            "clear": ("clear(couleur)", "Efface la surface graphique avec une couleur."),
            "pixel": ("pixel(x, y, couleur)", "Dessine un pixel."),
            "rect": ("rect(x, y, largeur, hauteur, couleur)", "Dessine un rectangle rempli."),
            "line": ("line(x1, y1, x2, y2, couleur)", "Dessine une ligne."),
            "circle": ("circle(x, y, rayon, couleur)", "Dessine un cercle rempli."),
            "text": ("text(x, y, texte, couleur)", "Dessine du texte."),
            "present": ("present()", "Affiche le rendu préparé à l'écran."),
            "close": ("close()", "Ferme la fenêtre graphique du processus."),
            "minimize": ("minimize()", "Réduit la fenêtre graphique dans la barre des tâches sans fermer le processus."),
            "keyDown": ("keyDown(touche)", "Teste si une touche est enfoncée."),
            "keyPressed": ("keyPressed(touche)", "Indique si la touche vient d’être pressée; un même appui ne renvoie vrai qu’une fois."),
            "textInput": ("textInput([action])", "Capture les caractères saisis; action=start/get/stop/clear."),
            "mouseX": ("mouseX()", "Retourne la position X de la souris."),
            "mouseY": ("mouseY()", "Retourne la position Y de la souris."),
            "mouseDown": ("mouseDown(bouton)", "Teste si un bouton de souris est enfoncé."),
            "closeRequested": ("closeRequested()", "Indique si l'utilisateur a demandé la fermeture."),
            "windowAlive": ("windowAlive()", "Indique si la fenêtre du processus est encore ouverte."),
            "rgb": ("rgb(r, g, b)", "Construit une couleur RGB 24 bits."),
            "imageLoad": ("imageLoad(chemin)", "Charge une image du disque virtuel; formats supportés : PNG, BMP 24/32 bits et PPM."),
            "imageDraw": ("imageDraw(image, x, y)", "Dessine une image à sa taille native."),
            "imageDrawScaled": ("imageDrawScaled(image, x, y, largeur, hauteur)", "Dessine une image redimensionnée par voisin le plus proche."),
            "imageWidth": ("imageWidth(image)", "Retourne la largeur d'une image chargée."),
            "imageHeight": ("imageHeight(image)", "Retourne la hauteur d'une image chargée."),
            "imageFree": ("imageFree(image)", "Libère un handle image; 0 = succès, 1 = handle invalide."),
        }

        # Corrige automatiquement la documentation en cas d'ajout futur d'un builtin.
        specs = MiniLangCompiler.BUILTIN_SPECS
        lines = [
            "MINILANG — DOCUMENTATION COMPLÈTE",
            "",
            "Toutes les fonctions natives actuellement reconnues par le compilateur.",
            "La notation [...] indique un argument optionnel. Le nombre d'arguments attendu",
            "est donné entre crochets à droite. Type = type de valeur retournée.",
            "",
        ]

        for name in specs:
            spec = specs[name]
            min_args, max_args, ret_type, _syscall = spec
            sig, desc = docs.get(name, (f"{name}(...)", "Fonction native MiniLang."))
            # Cas où la signature est laissée générique : indique quand même l'arité réelle.
            if name not in docs:
                if min_args == max_args:
                    sig = f"{name}({', '.join('arg' + str(i+1) for i in range(min_args))})" if min_args else f"{name}()"
                else:
                    sig = f"{name}({min_args} à {max_args} arguments)"
            arity = f"{min_args}" if min_args == max_args else f"{min_args}..{max_args}"
            lines.append(f"  {sig:<48} [{arity} argument(s)] -> {ret_type:<7} {desc}")

        lines += [
            "",
            "EXÉCUTION DE FICHIERS MINILANG",
            "  run -mini fichier.mini [args...] [&]    Compile le source en mémoire puis l'exécute sans créer de .mexe.",
            "  Les arguments fournis après le nom du fichier sont disponibles avec argc() et arg(index).",
            "",
            "SYNTAXE DU LANGAGE",
            "  let nom = expression                    Déclaration ou redéclaration.",
            "  nom = expression                       Affectation.",
            "  nom += expression                      Addition + affectation.",
            "  nom -= expression                      Soustraction + affectation.",
            "  nom *= expression                      Multiplication + affectation.",
            "  nom /= expression                      Division + affectation.",
            "  nom %= expression                      Modulo + affectation.",
            "  nom++ / nom--                          Incrémentation / décrémentation.",
            "  if (condition) { ... }                 Condition.",
            "  else { ... }                           Branche alternative.",
            "  while (condition) { ... }              Boucle conditionnelle.",
            "  for (init; condition; update) { ... }  Boucle for.",
            "  function nom(a, b) { ... }             Fonction utilisateur.",
            "  return expression                      Retour d'une fonction.",
            "  break                                  Sort de la boucle courante.",
            "  continue                               Passe à l'itération suivante.",
            "  exit expression                        Termine le processus avec un code.",
            "  print(expression)                      Affiche une expression avec fin de ligne.",
            "  print(expression, end=\"\")             Affiche sans ajouter de retour à la ligne.",
            "  print(expression, end=texte)           Utilise une fin personnalisée.",
            "  print(expression, flush=true)          Accepte flush pour compatibilité Python; les sorties sont déjà immédiates.",
            "",
            "LITTÉRAUX",
            "  123                                    Entier.",
            "  true / false                           Booléen.",
            '  "texte"                                Chaîne UTF-8.',
            "",
            "OPÉRATEURS",
            "  + - * / %                             Arithmétique; + concatène si une chaîne est impliquée.",
            "  == != < <= > >=                       Comparaisons.",
            "  && || !                               Logique booléenne.",
            "  & | ^ ~ << >>                         Opérations bit à bit.",
            "  ( ... )                                Groupement.",
            "  tableau[index]                         Indexation des tableaux.",
            "  texte[index]                           Accès à un caractère.",
            "",
            "COMMENTAIRES",
            "  # commentaire",
            "  // commentaire",
            "",
            "EXEMPLE",
            '  let nom = input("Nom : ")',
            '  let n = inputInt("Nombre : ")',
            '  write("/home/user/bonjour.txt", "Bonjour " + nom)',
            '  if (n > 10) {',
            '      print("Grand")',
            '  } else {',
            '      print("Petit")',
            '  }',
        ]
        return "\n".join(lines)

    @staticmethod
    def _unwrap_minilang_command_source(source: str) -> str:
        """Retire les guillemets utilisés uniquement pour grouper le code MiniLang.

        Le shell laisse volontairement le code source brut à la commande
        `minilang` pour ne pas casser les chaînes MiniLang internes. Cela signifie
        toutefois que `minilang 'print("TEST")'` arrivait auparavant au parseur
        avec les guillemets simples autour de *tout* le programme et était donc
        interprété comme une simple chaîne. Ici, une paire externe est décodée
        avec le même échappement Python que le lexer MiniLang, sans toucher aux
        guillemets qui appartiennent au code.
        """
        source = str(source).strip()
        if len(source) < 2 or source[0] not in ("\"", "'") or source[-1] != source[0]:
            return source
        try:
            value = ast.literal_eval(source)
        except Exception:
            return source
        return value if isinstance(value, str) else source

    def cmd_minilang(self, source: str, stdin_data: Optional[str] = None, quiet_result: bool = False):
        """Exécute directement une instruction/un petit programme MiniLang depuis le terminal.

        Exemple :
          minilang print("Bonjour")
          minilang mkdir("/tmp/test")
          minilang write("/tmp/test.txt", "Bonjour")
        """
        source = str(source).strip()
        if not source:
            print("Usage: minilang <code MiniLang>")
            print("Exemples:")
            print('  minilang print("Bonjour")')
            print('  minilang let x = 42')
            print('  minilang write("/tmp/test.txt", "Bonjour")')
            return

        try:
            # On passe par le compilateur officiel MiniLang -> MEXE2 :
            # les mêmes fonctions natives et les mêmes vérifications que pour
            # un vrai .mini sont donc disponibles.
            program = MiniLang.parse(source)
            exe = MiniLangCompiler(program).compile()

            with self.process_lock:
                pid = self.next_pid
                self.next_pid += 1
                proc = VirtualProcess(
                    pid,
                    "<minilang>",
                    exe,
                    os_ref=self,
                    argv=[],
                    cwd=self.cwd,
                    stdin_data=stdin_data,
                    stdin_pipe=(stdin_data is not None),
                )
                self.processes[pid] = proc

            code = proc.run()
            if not quiet_result:
                if proc.error is not None:
                    print(f"minilang: PID={pid} CRASH: {proc.error}")
                else:
                    print(f"[MiniLang] PID={pid} terminé (code={int(code or 0)})")
        except MiniLangCompileError as e:
            print("\x1b[31m[MINILANG] ERREUR\x1b[0m")
            print(f"[MINILANG] {e}")
        except Exception as e:
            print(f"minilang: erreur: {e}")

    def _command_argument_notes(self):
        """Référence centralisée des arguments des commandes miniOS.

        Cette table est partagée par `help` et `helpfile` afin que la
        documentation ne puisse plus diverger ou provoquer un NameError.
        """
        return {

            "help": [
                ("[sujet]", "Topic ou nom d'une commande à documenter."),
            ],
            "helpfile": [("[fichier.txt]", "Chemin virtuel du fichier de documentation. Défaut : /home/user/miniOS_help.txt.")],
            "minilangc": [("<code>", "Code source MiniLang à exécuter directement depuis le terminal; input() peut lire depuis un pipe.")],
            "echo": [("<texte...>", "Texte à afficher; plusieurs mots sont acceptés.")],
            "cd": [("<chemin>", "Chemin virtuel absolu ou relatif." )],
            "ls": [("[chemin|motif]", "Répertoire à lister; un motif comme *.mini sélectionne les correspondances.")],
            "mkdir": [("<chemin>", "Répertoire à créer."), ("[-p]", "Crée aussi les répertoires parents manquants.")],
            "rmdir": [("<chemin>", "Répertoire vide à supprimer.")],
            "touch": [("<fichier>", "Chemin du fichier à créer.")],
            "cat": [("<fichier|motif>", "Fichier virtuel à afficher; un motif peut sélectionner plusieurs fichiers.")],
            "write": [("<fichier>", "Fichier virtuel cible."), ("[texte]", "Texte à écrire; absent = éditeur multi-lignes."), ("[-l|--line <ligne> [texte]]", "Remplace directement la ligne indiquée (numérotation à partir de 1). Cette forme est facultative; l'éditeur propose aussi .editligne <ligne>.")],
            "edit": [("<fichier>", "Fichier virtuel à éditer."), ("-l <ligne>", "Sélectionne une ligne précise, numérotation à partir de 1."), ("[texte]", "Nouveau contenu de la ligne; absent = saisie interactive.")],
            "append": [("<fichier>", "Fichier virtuel cible."), ("[texte]", "Texte à ajouter; absent = éditeur.")],
            "rm": [("<fichier|répertoire|motif>", "Élément ou motif virtuel à supprimer; plusieurs cibles sont acceptées."), ("[-r]", "Autorise la suppression récursive d'un répertoire.")],
            "cp": [("<source|motif>", "Fichier/répertoire ou motif source."), ("<destination>", "Cible; plusieurs sources exigent un répertoire.")],
            "mv": [("<source|motif>", "Fichier/répertoire ou motif source."), ("<destination>", "Nouvel emplacement; plusieurs sources exigent un répertoire.")],
            "find": [("[chemin]", "Racine de recherche; défaut : cwd."), ("[motif]", "Nom/motif recherché.")],
            "tree": [("[chemin]", "Arbre à afficher; défaut : cwd.")],
            "stat": [("<chemin>", "Fichier ou répertoire à examiner.")],
            "head": [("<fichier>", "Fichier à lire.")],
            "tail": [("<fichier>", "Fichier à lire.")],
            "wc": [("<fichier>", "Fichier à compter.")],
            "run": [("[-debug|-debg]", "Active le journal ultra-précis VM32/graphique et écrit un fichier de trace sur le PC."), ("<programme>", "Nom ou chemin d'un .mexe en mode normal."), ("-mini", "Active le mode source MiniLang."), ("<fichier.mini>", "Source MiniLang à compiler en mémoire et exécuter sans créer de .mexe."), ("[args...]", "Arguments transmis à l'application, dans le même ordre; ils sont accessibles avec argc()/arg(index)."), ("&", "Option finale pour lancer en arrière-plan.")],
            "exec": [("<programme>", "Programme VM32 à exécuter."), ("[args...]", "Arguments transmis au programme, dans le même ordre.")],
            "wait": [("<pid>", "PID à attendre.")],
            "kill": [("<pid>", "PID du processus à arrêter.")],
            "debug": [("<pid>", "PID à inspecter."), ("[--graphics|-g]", "Ajoute le diagnostic complet du sous-système graphique du processus.")],
            "gdebug": [("<pid>", "PID de l’application graphique à diagnostiquer.")],
            "which": [("<commande>", "Nom de commande ou application à rechercher.")],
            "newapp": [("<nom>", "Nom de l'application MiniLang.")],
            "compile": [("<source.mini>", "Source MiniLang."), ("[sortie.mexe]", "Nom/chemin de sortie; défaut dérivé de la source.")],
            "build": [("<source.mini>", "Source MiniLang."), ("[sortie.mexe]", "Nom/chemin de sortie optionnel.")],
            "java": [("<.class|.jar|.java>", "Fichier Java à exécuter/charger."), ("[args...]", "Arguments Java." )],
            "javac": [("<source.java>", "Source Java."), ("[sortie.class]", "Classe de sortie optionnelle." )],
            "import": [("<fichier réel|motif>", "Fichier ou motif sur le PC hôte; *.ext est accepté."), ("[chemin virtuel]", "Destination dans miniOS; pour plusieurs fichiers, doit être un répertoire." )],
            "export": [("<fichier virtuel|motif>", "Source située dans le disque virtuel; *.ext est accepté."), ("<fichier réel>", "Fichier ou dossier de destination sur le PC; plusieurs sources exigent un dossier." )],
            "download": [("<url>", "URL HTTP ou HTTPS de la ressource à télécharger."), ("<fichier>", "Chemin de destination sur le disque virtuel."), ("[timeout]", "Délai en secondes; défaut 15, borné entre 1 et 300.")],
            "set": [("NOM=VALEUR", "Nom et nouvelle valeur de variable virtuelle." )],
            "net": [],
            "ifconfig": [],
            "ipconfig": [],
            "ping": [("[hôte]", "Adresse IP ou nom DNS à tester; défaut : 127.0.0.1."), ("[timeout_ms]", "Délai maximal en millisecondes; défaut : 2000, borné entre 100 et 10000.")],
            "nslookup": [("<hôte>", "Nom DNS ou adresse à résoudre avec le résolveur de la machine.")],
            "netstat": [],
            "route": [],
            "networktest": [("[hôte]", "Hôte réel à utiliser pour les tests Internet; défaut : example.com."), ("[port]", "Port TCP réel optionnel; défaut : 443.")],
        }

    def _command_examples(self):
        """Exemples partagés entre `help` et `helpfile`."""
        return {
            "help": ["help", "help ls", "help minilang", "help minilangc"],
            "helpfile": ["helpfile", "helpfile /home/user/commandes.txt"],
            "minilangc": ['minilang print("Bonjour")', 'minilang write("/tmp/test.txt", "Bonjour")', 'echo Bonjour | minilang print(input())'],
            "ls": ["ls", "ls /path", "ls *.mini"],
            "cd": ["cd /path", "cd .."],
            "write": ["write test.txt Bonjour", "write programme.mini", "write programme.mini --line 3 print(\"Bonjour\")", "write programme.mini -l 3 print(\"Bonjour\")"],
            "run": ["run monapp", "run monapp bonjour 123", "run monapp bonjour 123 &", "run -debug monapp", "run -debug monapp &", "run -mini test.mini", "run -debug -mini test.mini &"],
            "which": ["which monapp"],
            "compile": ["compile hello.mini", "compile hello.mini /path/hello.mexe"],
            "java": ["java Test.class", "java test.jar", "java Test.java"],
            "javac": ["javac Test.java", "javac Test.java /path/Test.class"],
            "import": [r"import C:\Users\Moi\Desktop\test.mini", r"import C:\Users\Moi\Desktop\miniapp\*.mini /home/user/miniapp/"],
            "export": [r"export /home/user/*.mini C:\Users\Moi\Desktop\miniapp", r"export /home/user/test.txt C:\Users\Moi\Desktop\test.txt"],
            "download": ["download https://example.com/test.txt /home/user/test.txt", "download https://example.com/test.txt /home/user/test.txt 30"],
            "kill": ["kill 2"],
            "ps": ["ps"],
            "env": ["env"],
            "set": ["set LANG=fr"],
            "path": ["path"],
            "disk": ["disk"],
            "net": ["net"],
            "ifconfig": ["ifconfig"],
            "ipconfig": ["ipconfig"],
            "ping": ["ping 127.0.0.1", "ping example.com 3000"],
            "nslookup": ["nslookup example.com"],
            "netstat": ["netstat"],
            "route": ["route"],
            "networktest": ["networktest", "networktest example.com"],
        }

    def cmd_help(self, args):
        """Aide concise, topics complets et documentation détaillée des commandes."""
        topic = args[0].lower() if args else None

        # Documentation complète de MiniLang : conservée telle quelle et générée
        # à partir de la liste des fonctions natives.
        sections = {
            "systeme": """MINIOS — AIDE RAPIDE

COMMANDES UTILES
  help [sujet]                         Aide générale ou documentation détaillée.
  help <commande>                      Documentation complète d'une commande.
  run -debug <programme>                Lance un programme avec une trace VM/GUI ultra-précise.
  commande1 | commande2               Pipe: sortie de commande1 vers l'entrée standard de commande2.
  help minilang                        Référence complète du langage MiniLang.
  help minilangc                       Documentation de la commande minilangc.
  help os                              Référence complète de toutes les commandes du terminal miniOS.
  help graphics                        API graphique + moteur de rendu 2D MiniLang.
  help filesystem                      Commandes du disque virtuel.
  help executables                     Exécution et PATH.
  help compiler                        MiniLang, compilation et éditeur.
  help java                            Java / JVM.
  help process                         Processus et arrière-plan.
  help vm                              VM32 et mémoire.
  help storage                         Disque virtuel + import/export.
  help network                         Réseau virtuel.
  help internet                        Réseau et API Internet des applications.
  help os                              Référence complète des commandes du terminal.
  helpfile [fichier.txt]               Génère toute la documentation dans un fichier.
  commande1 | commande2               Envoie la sortie standard de la première commande à la suivante.

SYSTÈME
  clear   echo   uname   version   whoami   hostname   uptime   date   exit

FICHIERS
  ls  cd  pwd  mkdir  rmdir  touch  cat  write  edit  append  rm  cp  mv
  find  tree  stat  head  tail  wc

PROGRAMMES
  run  exec  wait  jobs  ps  kill  debug  gdebug  which  path
  newapp  compile  build  java  javac  apps  install  uninstall

SYSTÈME / STOCKAGE / RÉSEAU
  mem  cpu  regs  stack  heap  info  disk  import  export
  env  set  history  net  ifconfig  ipconfig  ping  nslookup  netstat  route  networktest  test
  Internet pour .mexe : httpGet/httpPost/httpDownload/dnsResolve
  Images MiniLang : imageLoad/imageDraw/imageDrawScaled/imageWidth/imageHeight/imageFree

TOPICS
  os  filesystem  executables  compiler  java  process  vm  storage  network  internet
  minilang  minilangc  graphics  strings  arrays  memory  host  system-api  arguments

CONSEIL
  Utilise `help <commande>` pour voir sa syntaxe, ses arguments et des exemples.
  Utilise `help minilang` pour la référence complète du langage.
""",
            "os": """MINIOS — COMMANDES DU SYSTÈME

SYSTÈME
  clear                                  Efface le terminal.
  echo <texte...>                       Affiche du texte.
  uname                                 Affiche l’architecture miniOS.
  version                               Affiche la version.
  whoami                                Affiche l’utilisateur courant.
  hostname                              Affiche le nom de la machine.
  uptime                                Affiche le temps depuis le démarrage.
  date                                  Affiche la date et l’heure locales.
  reboot                                Redémarrage simulé.
  shutdown                              Demande l’arrêt.
  exit                                  Quitte miniOS.

FICHIERS
  ls cd pwd mkdir rmdir touch cat write edit append rm cp mv
  find tree stat head tail wc             Gestion du disque virtuel.
  import <réel> [virtuel]                 Importe depuis le PC réel.
  export <virtuel> <réel>                Exporte vers le PC réel.
  download <url> <fichier> [timeout]     Télécharge HTTP/HTTPS vers le disque virtuel (8 MiB max).

PROGRAMMES / VM
  run exec wait jobs ps kill debug gdebug which path
  newapp compile build java javac apps install uninstall
  mem cpu regs stack heap info test       Outils VM32 et diagnostic.

ENVIRONNEMENT
  env set history                         Variables et historique.

RÉSEAU
  net ifconfig ipconfig ping nslookup netstat route networktest

AIDE
  help [sujet]                            Aide générale ou détaillée.
  help <commande>                         Syntaxe, arguments et exemples.
  help internet                           API réseau/Internet pour les applications.
  help minilang                           Référence complète de MiniLang.
  helpfile [fichier.txt]                  Génère la documentation complète.
""",
            "internet": """MINIOS — INTERNET / RÉSEAU POUR LES APPLICATIONS

COMMANDES DU TERMINAL
  net                                   État et connectivité réseau.
  ifconfig / ipconfig                   Interfaces et adresses locales.
  ping [hôte] [timeout_ms]              Ping ICMP.
  nslookup <hôte>                       Résolution DNS.
  netstat                               Sockets visibles.
  route                                 Table de routage accessible.
  networktest [hôte] [port]             Test de la pile réseau et d’Internet.

API MINILANG / MEXE
  httpGet(url[, timeout])               GET HTTP/HTTPS; retourne le corps texte.
  httpPost(url, corps[, type[, timeout]]) POST HTTP/HTTPS; retourne le corps texte.
  httpDownload(url, chemin[, timeout])  Télécharge vers le disque virtuel.
  download(url, chemin[, timeout])      Alias de httpDownload.
  dnsResolve(hôte)                      Résolution DNS réelle.
  tcpConnect(hôte, port[, timeout])     Ouvre une connexion TCP et retourne un handle.
  tcpSend(handle, texte)                Envoie des données TCP UTF-8.
  tcpRecv(handle[, max[, timeout]])     Reçoit des données TCP.
  tcpClose(handle)                      Ferme une connexion TCP.
  tcpIsOpen(handle)                     Vérifie un handle TCP.
  udpOpen()                             Crée un socket UDP.
  udpSend(handle, hôte, port, texte)    Envoie un datagramme UDP.
  udpRecv(handle[, max[, timeout]])     Reçoit un datagramme UDP.
  udpClose(handle)                      Ferme un socket UDP.

TÉLÉCHARGEMENT
  Shell : download https://exemple/fichier.txt /home/user/fichier.txt
  MiniLang : download("https://exemple/fichier.txt", "/home/user/fichier.txt")
  timeout est en secondes; valeur par défaut 15 s, bornée à 300 s pour download.
  HTTP et HTTPS uniquement; taille maximale d’un téléchargement : 8 MiB.
  Le fichier est écrit sur le disque virtuel de miniOS, pas directement sur le PC.

REMARQUE
  Les API réseau utilisent les fonctions réseau Python de l’hôte et n’exécutent pas
  les commandes externes ping, curl, wget, ipconfig, netstat ou route.
""",
            "os": """MINIOS — COMMANDES DU SYSTÈME
  help [sujet]                          Aide générale ou documentation détaillée.
  clear echo uname version whoami       Commandes système.
  hostname uptime date reboot shutdown exit
  ls cd pwd mkdir rmdir touch cat write edit append rm cp mv find tree stat head tail wc
  run exec wait jobs ps kill debug gdebug which path newapp compile build java javac apps install uninstall
  mem cpu regs stack heap info test      Outils VM32 et diagnostic.
  env set history                        Environnement.
  import <réel> [virtuel]               PC réel -> disque virtuel.
  export <virtuel> <réel>               Disque virtuel -> PC réel.
  download <url> <fichier> [timeout]    HTTP/HTTPS -> disque virtuel, maximum 8 MiB.
  net ifconfig ipconfig ping nslookup netstat route networktest

Voir aussi : help internet et help minilang.
""",
            "internet": """MINIOS — INTERNET / RÉSEAU POUR LES APPLICATIONS
  net / ifconfig / ipconfig             État et interfaces réseau.
  ping [hôte] [timeout_ms]              ICMP.
  nslookup <hôte>                       DNS.
  netstat / route                       Informations réseau accessibles à Python.
  networktest [hôte] [port]             Tests réseau et Internet.

API MiniLang / MEXE
  httpGet(url[, timeout])               GET HTTP/HTTPS.
  httpPost(url, corps[, type[, timeout]]) POST HTTP/HTTPS.
  httpDownload(url, chemin[, timeout])  Téléchargement vers le disque virtuel.
  download(url, chemin[, timeout])      Alias de httpDownload.
  dnsResolve(hôte)                      Résolution DNS.
  tcpConnect/tcpSend/tcpRecv/tcpClose/tcpIsOpen
  udpOpen/udpSend/udpRecv/udpClose

download shell : download <url> <fichier> [timeout]
HTTP/HTTPS uniquement, 8 MiB maximum; timeout 15 s par défaut, 1..300 s.
""",
            "filesystem": """SYSTÈME DE FICHIERS VIRTUEL
  pwd                                   Affiche le dossier courant.
  cd <chemin>                           Change de dossier et affiche le nouveau chemin.
  ls [chemin]                           Liste fichiers et répertoires.
  mkdir <chemin> [-p]                   Crée un répertoire; -p crée les parents.
  rmdir <chemin>                        Supprime un répertoire vide.
  touch <fichier>                       Crée un fichier vide.
  cat <fichier>                         Affiche un fichier.
  write <fichier> [texte]               Écrit/remplace un fichier; sans texte ouvre l'éditeur.
  write <fichier> [-l|--line <ligne> [texte]] Remplace une ligne précise (numérotation à partir de 1).
  edit <fichier>                        Ouvre l'éditeur multi-lignes.
  edit <fichier> -l <ligne>             Édite directement une ligne précise.
  edit <fichier> -l <ligne> texte        Remplace directement une ligne.
  append <fichier> [texte]              Ajoute du texte; sans texte ouvre l'éditeur.
  rm <fichier|répertoire> [-r]          Supprime un élément; -r autorise le récursif.
  cp <source> <destination>             Copie.
  mv <source> <destination>             Déplace/renomme.
  find [chemin] [nom]                   Recherche récursive.
  tree [chemin]                         Affiche l'arborescence.
  stat <chemin>                         Affiche type et taille.
  head <fichier>                        Affiche les 10 premières lignes.
  tail <fichier>                        Affiche les 10 dernières lignes.
  wc <fichier>                          Compte mots, lignes et octets.

CHEMINS
  /                                     Racine.
  .                                     Dossier courant.
  ..                                    Dossier parent.
  ~                                     /home/user.
  /path                                 Répertoire d'exécutables.
  /bin /apps                            Répertoires recherchés dans PATH.
""",
            "executables": """EXÉCUTION ET PROGRAMMES
  run <programme> [args...]             Premier plan.
  run <programme> [args...] &           Arrière-plan; le terminal reste libre.
  exec <programme> [args...]            Alias d'exécution VM32.
  wait <pid>                             Attend la fin du processus.
  jobs                                  Alias de ps.
  <programme> [args...]                  Lance automatiquement un .mexe trouvé.
  which <commande>                       Affiche builtin ou chemin trouvé.
  path                                  Affiche PATH.
  ps                                    Liste les processus.
  kill <pid>                            Arrête un processus VM32.
  debug <pid>                           État détaillé d'un processus.
  debug <pid> --graphics                État VM32 + diagnostic graphique détaillé.
  gdebug <pid>                          Alias direct du diagnostic graphique.
  apps                                  Liste /apps.
  install <...>                         Gestion d'application.
  uninstall <...>                       Désinstallation d'application.

EXEMPLE
  mv monapp.mexe /path/
  monapp argument1 argument2 &
""",
            "compiler": """COMPILATEUR / ÉDITEUR
  minilang <code>                     Exécute directement du code MiniLang depuis le terminal; input() lit aussi un pipe.
  newapp <nom>                          Crée un squelette .mini.
  compile <source.mini> [sortie.mexe]   Compile vers MEXE2/VM32.
  build <source.mini> [sortie.mexe]     Alias de compile.

ÉDITEUR MULTI-LIGNES
  write programme.mini                  Ouvre l'éditeur si aucun texte n'est fourni.
  edit programme.mini                   Ouvre l'éditeur multi-lignes d'un fichier.
  edit programme.mini -l 5              Édite directement la ligne 5.
  edit programme.mini --line 5 texte    Remplace directement la ligne 5.
  .save                                 Enregistre et quitte.
  .cancel                               Annule.
  .show                                 Affiche le contenu courant.
  .clear                                Efface tout.
  .editligne <ligne>                    Édite directement la ligne indiquée.

ERREURS
  Les erreurs indiquent ligne/colonne lorsque possible et la cause de l'erreur.
""",
            "java": """JAVA / JVM
  javac <source.java> [sortie.class]    Compile le sous-ensemble Java intégré.
  java <fichier.class> [args...]        Exécute une classe.
  java <fichier.jar> [args...]          Exécute le Main-Class d'un JAR.
  java <fichier.java> [args...]         Compile en mémoire puis exécute.

SUPPORT ACTUEL
  int, boolean, String, variables, calculs, if/else, while, for,
  méthodes static, return, System.out.print/println et concaténation.

ENTRÉE / SYSTÈME
  input(["Question"])                    Entrée texte.
  inputInt(["Question"])                 Entrée entière.
  System.getProperty("user.dir")       Dossier courant.
  System.getenv("PATH")                 Environnement virtuel.

REMARQUE
  Le compilateur Java intégré reste un sous-ensemble et n'est pas OpenJDK/javac complet.
""",
            "process": """PROCESSUS
  ps                                    Liste PID, état, durée et nom.
  run <programme> [args...]             Lance un processus VM32 avec ses arguments.
  run <programme> [args...] &           Lance en arrière-plan avec ses arguments.
  jobs                                  Alias de ps.
  wait <pid>                             Attend sa fin.
  kill <pid>                            Demande l'arrêt.
  debug <pid>                           Affiche l'état détaillé.

ARGUMENTS DES MEXE
  run monapp bonjour 42                 Le .mexe reçoit 2 arguments.
  Dans MiniLang : argc() -> 2, arg(0) -> "bonjour", arg(1) -> "42".
  L'appel direct `monapp bonjour 42` transmet les mêmes arguments.

ÉTATS
  RUNNING   SLEEPING   WAITING_INPUT   EXITED   KILLED   CRASHED
""",
            "vm": """VM32
  mem                                   RAM VM32.
  cpu                                   Caractéristiques CPU VM32.
  regs                                  Registres R0..R7.
  stack                                 Informations de pile.
  heap                                  État du heap.
  info                                  Synthèse miniOS / VM / JVM / disque.
  test                                  Tests internes.

FORMAT
  MEXE2                                 Format des exécutables VM32.
""",
            "storage": """STOCKAGE
  disk                                  Emplacement et état du disque persistant.
  import <réel> [virtuel]               PC réel -> disque virtuel.
  export <virtuel> <réel>               Disque virtuel -> PC réel.

PERSISTANCE
  Le disque virtuel est sauvegardé dans minios_disk.json.
  Les chemins Windows C:\\... et UNC \\\\serveur\\... sont pris en charge.
  Les fichiers RTF importés peuvent être convertis en texte brut.
""",
            "network": """RÉSEAU HÔTE
  net                                   État réseau et connectivité via Python/socket.
  ifconfig                              Interfaces et adresses détectées via Python.
  ipconfig                              Alias de ifconfig, sans appeler ipconfig.exe.
  ping [hôte] [timeout_ms]              Ping ICMP via socket brut, sans ping.exe.
  nslookup <hôte>                       DNS via socket.getaddrinfo, sans nslookup.exe.
  netstat                               Sockets via /proc sous Linux, sans netstat/ss.
  route                                 Routes accessibles via Python/procfs, sans programme externe.
  networktest [hôte] [port]             Teste une à une les fonctions réseau miniOS et Internet réel.
  Ping ICMP localhost                     Test obligatoire de la pile ICMP locale.
  Ping ICMP Internet                      Test informatif : son échec ne fait pas échouer networktest.
  Codes 101-112                          Voir `help networktest`; 0 = succès.

INTERNET POUR LES APPLICATIONS
  httpGet(url[, timeout])              GET HTTP/HTTPS réel, retourne le corps texte.
  httpPost(url, corps[, type[, timeout]]) POST HTTP/HTTPS réel.
  httpDownload(url, chemin[, timeout]) Télécharge directement dans le disque virtuel.
  download(url, chemin[, timeout])      Alias de httpDownload.
  dnsResolve(hôte)                     Résolution DNS réelle.
  tcpConnect(hôte, port[, timeout])    Ouvre un socket TCP réel; retourne un handle par processus.
  tcpSend/tcpRecv/tcpClose             Échange des données via TCP réel.
  udpOpen/udpSend/udpRecv/udpClose     Échange des datagrammes UDP réels.
  timeout est en secondes (0 = 15 s par défaut, maximum 120 s).

NOTE
  Les commandes réseau n'exécutent aucun programme comme ping.exe, ipconfig,
  netstat, ss ou route. Elles utilisent les sockets Python, le DNS Python et,
  sous Linux, les fichiers /proc pour obtenir les informations disponibles.
""",
            "minilangc": """COMMANDE — minilang

SYNTAXE
  minilang <code>                        Exécute directement du code MiniLang depuis le terminal.

DESCRIPTION
  Lance un programme MiniLang court directement depuis la ligne de commande.
  Pour la référence complète du langage, utilise : help minilang

ARGUMENTS
  <code>                                 Code MiniLang à exécuter.

EXEMPLES
  minilang print("Bonjour")
  minilang let x = 10; print(x)

DOCUMENTATION
  help minilangc                         Affiche cette documentation de la commande minilang.
""",
            "minilang": self._minilang_help_text(),
            "strings": """MINILANG — CHAÎNES
  len(s)                               Longueur.
  str(x)                               Convertit en chaîne.
  int(x)                               Convertit en entier.
  substr(s, debut[, longueur])         Sous-chaîne.
  replace(s, ancien, nouveau)          Remplacement.
  contains(s, morceau)                 Contient ?
  startsWith(s, prefixe)               Préfixe ?
  endsWith(s, suffixe)                 Suffixe ?
  lower(s) / upper(s)                  Casse.
  trim(s)                              Espaces aux extrémités.
  chr(n) / ord(s)                     Unicode.
  split(s, separateur) / join(tab,s)  Découpe / assemble.
  +                                    Concatène si un opérande est une chaîne.
  s[index]                             Caractère.
""",
            "arrays": """MINILANG — TABLEAUX
  array(taille)                        Crée un tableau.
  arrayLen(tab)                        Taille.
  arrayGet(tab, index)                 Lit un entier.
  arraySet(tab, index, valeur)         Écrit un entier.
  arrayGetStr(tab, index)              Lit une chaîne.
  arraySetStr(tab, index, valeur)      Écrit une chaîne.
  tab[index]                            Accès direct.
  split(...) / join(...)                Tableaux de chaînes.
""",
            "memory": """MINILANG — MÉMOIRE VM32
  alloc(taille)                        Alloue.
  free(ptr)                            Libère ; retourne 0 si succès, 1 si adresse invalide.
  read8(adresse)                       Lit 1 octet.
  read32(adresse)                      Lit 32 bits.
  write8(adresse, valeur)              Écrit 1 octet.
  write32(adresse, valeur)             Écrit 32 bits.
  memTotal()                           RAM totale exposée.
  memFree()                            RAM libre exposée.
""",
            "host": """MINILANG — FICHIERS RÉELS
  importHost(réel, virtuel)            Importe depuis le PC.
  exportHost(virtuel, réel)            Exporte vers le PC.
  hostExists(réel)                     Teste l'existence.
  hostRead(réel)                       Lit un fichier.
  hostWrite(réel, texte)               Écrit un fichier.
  hostAppend(réel, texte)              Ajoute au fichier.
  hostDelete(réel)                     Supprime.
  hostMkdir(répertoire)                Crée un dossier.
  hostList(répertoire)                 Liste.
  hostIsDir(chemin)                    Teste un dossier.
  hostSize(chemin)                     Taille.
""",
            "system-api": """MINILANG — API SYSTÈME
  input([question])                      Saisie texte.
  inputInt([question])                   Saisie entier.
  system(cle)                          Propriété miniOS.
  env(nom) / envSet(nom,valeur)       Environnement virtuel.
  argc() / arg(index)                  Arguments du programme.
  - argc() retourne le nombre d'arguments reçus par le .mexe.
  - arg(index) retourne l'argument à l'index demandé (0 = premier argument).
  - Si l'index est hors limites, arg(index) retourne une chaîne vide.
  - Les arguments sont transmis par `run`, `exec` ou l'appel direct d'un .mexe.
  cwd() / chdir(chemin)                Dossier courant.
  shell(commande) / command(commande)  Commande miniOS.
  exec(commande)                       Commande + sortie capturée.
  sysf(fonction[, args...])            Appel dynamique d'une fonction système native.
  run(programme[, args...])            Lance un .mexe.
  sleep(ms)                             Pause.
  time() / timeMs()                     Heure Unix.
  random(max) / randomRange(min,max)   Aléatoire.
  ping(hôte)                            Ping virtuel.
  httpGet(url[, timeout])              GET HTTP/HTTPS réel ; retourne le texte.
  httpPost(url, corps[, type[, timeout]]) POST HTTP/HTTPS réel ; retourne le texte.
  httpDownload(url, chemin[, timeout]) Télécharge vers le disque virtuel.
  download(url, chemin[, timeout])      Alias de httpDownload.
  dnsResolve(hôte)                     Résolution DNS réelle.
  pid() / program() / hostname()       Informations processus/système.
""",
            "arguments": """ARGUMENTS DES PROGRAMMES VM32 / MEXE
  run <programme> [args...]             Transmet les arguments au processus.
  run <programme> [args...] &           Idem en arrière-plan.
  <programme> [args...]                  Appel direct d'un programme trouvé dans PATH.
  exec <programme> [args...]             Transmet également les arguments.

MINILANG
  argc()                                 Nombre d'arguments reçus.
  arg(index)                             Valeur d'un argument; index 0 = premier.

EXEMPLE
  run demo bonjour 123
  -> argc() = 2
  -> arg(0) = "bonjour"
  -> arg(1) = "123"

NOTE
  Les arguments sont des chaînes de caractères. Convertis-les avec int(...)
  si ton application attend un nombre.
""",
            "graphics": """MINILANG — MOTEUR GRAPHIQUE 2D
  Moteur : SoftwareRenderer (framebuffer CPU, indépendant du toolkit).
  Présentation : framebuffer présenté par un backend natif de la plateforme (Win32/X11/Cocoa via ctypes; iOS via hôte UIKit).
  Chrome : barre de titre graphique miniOS avec boutons minimiser et fermer, dessinée par le renderer.
  Rendu v1 : pixels, lignes, rectangles, cercles et texte bitmap 5x7.
  Plateformes : Windows=Win32, Linux=X11/XWayland, macOS=Cocoa/AppKit, iOS=UIKit via une application hôte.
  Linux : backend X11 natif via libX11 et DISPLAY (compatible XWayland) ; pas de toolkit Python.
  macOS : backend Cocoa/AppKit + CoreGraphics via Objective-C runtime ; pas de toolkit Python.

  window(titre, largeur, hauteur)      Crée une fenêtre.
  clear(couleur)                        Efface.
  pixel(x, y, couleur)                  Pixel.
  rect(x,y,largeur,hauteur,couleur)    Rectangle.
  line(x1,y1,x2,y2,couleur)             Ligne.
  circle(x,y,rayon,couleur)             Cercle.
  text(x,y,texte,couleur)               Texte.
  present()                             Affiche le rendu.
  close()                               Ferme la fenêtre.
  windowAlive()                         Fenêtre ouverte ?
  closeRequested()                     Demande de fermeture ?
  keyDown(touche)                       Touche enfoncée ?
  keyPressed(touche)                    Nouvel appui de touche ?
  mouseX() / mouseY()                  Position souris.
  mouseDown(bouton)                    Bouton souris enfoncé ?
  rgb(r,g,b)                            Encode une couleur RGB.
  imageLoad(chemin)                      Charge une image PNG, BMP 24/32 bits ou PPM.
  imageDraw(image,x,y)                   Dessine l'image à sa taille native.
  imageDrawScaled(image,x,y,w,h)        Dessine l'image redimensionnée.
  imageWidth(image) / imageHeight(image) Dimensions de l'image.
  imageFree(image)                       Libère le handle image (0 = succès).

EXEMPLE
  window("Test", 800, 600)
  clear(rgb(20,20,20))
  rect(100,100,200,120,rgb(255,0,0))
  text(120,130,"Bonjour",rgb(255,255,255))
  present()
""",
        }

        # Chaque commande a une syntaxe et une description. Les arguments sont
        # extraits automatiquement de la syntaxe pour offrir une aide uniforme.
        command_help = {
            "help": "help [sujet] — affiche l'aide générale, d'un topic ou d'une commande.",
            "helpfile": "helpfile [fichier.txt] — génère toute la documentation dans un fichier texte.",
            "minilangc": "minilang <code> — exécute directement une instruction ou un petit programme MiniLang.",
            "clear": "clear — efface le terminal.",
            "echo": "echo <texte...> — affiche le texte fourni.",
            "uname": "uname — affiche l'architecture miniOS.",
            "version": "version — affiche la version de miniOS.",
            "whoami": "whoami — affiche l'utilisateur courant.",
            "hostname": "hostname — affiche le nom de la machine virtuelle.",
            "uptime": "uptime — affiche depuis combien de temps miniOS tourne.",
            "date": "date — affiche la date et l'heure locales.",
            "reboot": "reboot — redémarrage simulé de miniOS.",
            "shutdown": "shutdown — demande l'arrêt de miniOS.",
            "exit": "exit — quitte miniOS.",
            "ls": "ls [chemin|motif] — liste le contenu du répertoire indiqué; un motif comme *.mini sélectionne les correspondances.",
            "cd": "cd <chemin> — change le dossier courant et affiche le nouveau chemin.",
            "pwd": "pwd — affiche le dossier courant.",
            "mkdir": "mkdir <chemin> [-p] — crée un répertoire; -p crée les parents.",
            "rmdir": "rmdir <chemin> — supprime un répertoire vide.",
            "touch": "touch <fichier> — crée un fichier vide.",
            "cat": "cat <fichier|motif> — affiche le contenu d'un ou plusieurs fichiers correspondants.",
            "write": "write <fichier> [texte] | write <fichier> [-l|--line <ligne> [texte]] — écrit/remplace un fichier; sans texte ouvre l'éditeur multi-lignes. Commandes de l'éditeur: .save, .cancel, .show, .clear, .editligne <ligne>.",
            "edit": "edit <fichier> -l <ligne> [texte] — remplace une ligne précise; sans texte, la nouvelle ligne est demandée interactively. Sans -l, ouvre l'éditeur multi-lignes.",
            "append": "append <fichier> [texte] — ajoute du texte; sans texte ouvre l'éditeur.",
            "rm": "rm <fichier|répertoire|motif> [-r] [... ] — supprime un ou plusieurs éléments; les jokers sont acceptés.",
            "cp": "cp <source|motif> <destination> — copie un ou plusieurs fichiers/répertoires; les jokers sont acceptés.",
            "mv": "mv <source|motif> <destination> — déplace ou renomme un ou plusieurs éléments; les jokers sont acceptés.",
            "find": "find [chemin] [motif] — recherche récursive dans l'arborescence.",
            "tree": "tree [chemin] — affiche l'arborescence.",
            "stat": "stat <chemin> — affiche le type, chemin et taille.",
            "head": "head <fichier> — affiche les 10 premières lignes.",
            "tail": "tail <fichier> — affiche les 10 dernières lignes.",
            "wc": "wc <fichier> — affiche mots, lignes et octets.",
            "run": "run [-debug|-debg] <programme> [args...] [&] | run [-debug|-debg] -mini <fichier.mini> [args...] [&] — lance un .mexe ou compile/exécute un source MiniLang sans créer de .mexe; & le met en arrière-plan.",
            "exec": "exec <programme> [args...] — exécute un programme VM32 et lui transmet ses arguments.",
            "wait": "wait <pid> — attend la fin d'un processus de fond.",
            "jobs": "jobs — affiche les processus (alias de ps).",
            "ps": "ps — liste les processus, leur état, durée et nom.",
            "kill": "kill <pid> — arrête un processus VM32.",
            "debug": "debug <pid> [--graphics] — affiche l'état détaillé d'un processus; --graphics ajoute le diagnostic GUI.",
            "gdebug": "gdebug <pid> — affiche directement le diagnostic graphique détaillé du processus.",
            "which": "which <commande> — indique builtin ou chemin du programme trouvé.",
            "path": "path — affiche le PATH et ses répertoires de recherche.",
            "newapp": "newapp <nom> — crée un squelette d'application MiniLang.",
            "compile": "compile <source.mini> [sortie.mexe] — compile MiniLang vers MEXE2/VM32.",
            "build": "build <source.mini> [sortie.mexe] — alias de compile.",
            "java": "java <.class|.jar|.java> [args...] — exécute Java ou compile/exécute un source .java.",
            "javac": "javac <source.java> [sortie.class] — compile le sous-ensemble Java intégré.",
            "apps": "apps — liste les applications disponibles dans /apps.",
            "install": "install <...> — installe une application selon les capacités de miniOS 0.5.",
            "uninstall": "uninstall <...> — désinstalle une application selon les capacités de miniOS 0.5.",
            "mem": "mem — affiche la RAM VM32.",
            "cpu": "cpu — affiche les caractéristiques du CPU VM32.",
            "regs": "regs — affiche les registres R0..R7.",
            "stack": "stack — affiche les informations de pile VM32.",
            "heap": "heap — affiche l'état du heap VM32.",
            "info": "info — affiche une synthèse de miniOS, VM, JVM et stockage.",
            "disk": "disk — affiche le fichier de persistance et l'état du disque virtuel.",
            "import": "import <fichier réel|motif> [chemin virtuel] — copie un ou plusieurs fichiers du PC réel vers le disque virtuel; les jokers sont acceptés.",
            "export": "export <fichier virtuel|motif> <fichier réel> — copie un ou plusieurs fichiers vers le PC réel; les jokers sont acceptés.",
            "download": "download <url> <fichier> [timeout] — télécharge une ressource HTTP/HTTPS vers le disque virtuel (8 MiB max; timeout 15 s par défaut, 1..300 s).",
            "env": "env — affiche les variables d'environnement virtuelles.",
            "set": "set NOM=VALEUR — définit une variable d'environnement virtuelle.",
            "history": "history — affiche l'historique des commandes.",
            "net": "net — affiche l'état du réseau réel de la machine (adresses et connectivité Internet).",
            "ifconfig": "ifconfig — affiche les interfaces réseau détectées par les API Python; aucun outil externe n'est lancé.",
            "ping": "ping [hôte] [timeout_ms] — effectue un ping ICMP sans lancer ping.exe ou ping.",
            "ipconfig": "ipconfig — alias de ifconfig; affiche les interfaces réseau réelles.",
            "nslookup": "nslookup <hôte> — résout un nom via socket.getaddrinfo, sans nslookup.exe.",
            "netstat": "netstat — affiche les sockets exposées par miniOS via Python/procfs; aucun netstat/ss n'est lancé.",
            "route": "route — affiche la table de routage accessible sans outil externe.",
            "networktest": "networktest [hôte] [port] — teste une à une les fonctions réseau miniOS et le véritable accès Internet : interfaces, adresses, DNS, TCP, ping ICMP localhost obligatoire, ping ICMP Internet informatif, HTTPS GET/POST/téléchargement, UDP DNS et handles TCP. Codes 101-112 ; 0 = succès. Le ping Internet ne fait jamais échouer le bilan global.",
            "test": "test — lance les tests internes disponibles.",
        }

        argument_notes = self._command_argument_notes()

        examples = self._command_examples()

        if topic in {"os", "oscommands", "commandes-os", "commandes_os", "terminal"}:
            # Documentation complète de toutes les commandes du shell miniOS,
            # sur le même principe que help minilang : signature, arité,
            # arguments et description. La source est la table command_help
            # ci-dessus, complétée par argument_notes.
            categories = {
                "SYSTÈME": ["help", "clear", "echo", "uname", "version", "whoami", "hostname", "uptime", "date", "reboot", "shutdown", "exit"],
                "FICHIERS ET CHEMINS": ["ls", "cd", "pwd", "mkdir", "rmdir", "touch", "cat", "write", "edit", "append", "rm", "cp", "mv", "find", "tree", "stat", "head", "tail", "wc"],
                "PROGRAMMES ET PROCESSUS": ["run", "exec", "wait", "jobs", "ps", "kill", "debug", "gdebug", "which", "path", "newapp", "compile", "build", "minilangc", "java", "javac", "apps", "install", "uninstall"],
                "VM ET STOCKAGE": ["mem", "cpu", "regs", "stack", "heap", "info", "disk", "import", "export"],
                "ENVIRONNEMENT ET RÉSEAU": ["env", "set", "history", "net", "ifconfig", "ipconfig", "ping", "nslookup", "netstat", "route", "networktest", "test", "helpfile"],
            }
            print("MINIOS — COMMANDES DE L'OS — DOCUMENTATION COMPLÈTE")
            print("=" * 78)
            print("Toutes les commandes disponibles dans le terminal miniOS 0.5.")
            print("La notation [...] indique un argument optionnel. La notation <...> indique un argument obligatoire.")
            print("L'arité donnée ci-dessous correspond au nombre d'arguments attendus par la commande.")
            print("")
            print("JOKERS / MOTIFS DE FICHIERS")
            print("-" * 78)
            print("  *    Remplace une suite de caractères dans un même niveau de dossier.")
            print("  ?    Remplace un seul caractère.")
            print("  [...] Permet un motif de caractères, comme dans un shell.")
            print("  **   Avec un chemin virtuel, peut traverser plusieurs sous-dossiers.")
            print("")
            print("Exemples :")
            print("  ls *.mini")
            print("  rm *.mini")
            print("  cp *.mini /path/")
            print("  mv *.mexe /apps/")
            print(r"  import C:\Users\Moi\Desktop\miniapp\*.mini /home/user/")
            print(r"  export /home/user/*.mini C:\Users\Moi\Desktop\miniapp")
            print("")

            import re
            documented = set()
            for category, names in categories.items():
                print(category)
                print("-" * 78)
                for name in names:
                    if name not in command_help:
                        continue
                    documented.add(name)
                    entry = command_help[name]
                    syntax, description = entry.split(" — ", 1) if " — " in entry else (entry, "")
                    cmd_name = syntax.split()[0]
                    tail = syntax[len(cmd_name):]
                    tokens = re.findall(r"<[^>]+>|\[[^\]]+\]|\&", tail)
                    mandatory = sum(1 for t in tokens if not t.startswith("[") and t != "&")
                    optional = sum(1 for t in tokens if t.startswith("["))
                    extras = 0
                    if any("..." in t for t in tokens):
                        # Un nombre maximal exact n'est pas toujours borné (ex. args...).
                        arity = f"{mandatory}..+" if optional or extras else f"{mandatory}+"
                    else:
                        arity = f"{mandatory}" if optional == 0 else f"{mandatory}..{mandatory + optional}"
                    print(f"  {syntax:<46} [{arity} argument(s)]")
                    print(f"    Description : {description}")
                    notes = argument_notes.get(name)
                    if notes:
                        print("    Arguments :")
                        for token, desc in notes:
                            print(f"      {token:<20} {desc}")
                    elif tokens:
                        print("    Arguments :")
                        for token in tokens:
                            if token == "&":
                                print(f"      {token:<20} Lance la commande en arrière-plan.")
                            elif token.startswith("["):
                                print(f"      {token:<20} Argument optionnel.")
                            else:
                                print(f"      {token:<20} Argument obligatoire.")
                    ex = examples.get(name, [])
                    if ex:
                        print("    Exemples :")
                        for line in ex:
                            print(f"      {line}")
                    print("")

            # Toute nouvelle commande ajoutée à command_help apparaîtra quand même.
            missing = [name for name in sorted(command_help) if name not in documented]
            if missing:
                print("AUTRES COMMANDES")
                print("-" * 78)
                for name in missing:
                    syntax, description = command_help[name].split(" — ", 1) if " — " in command_help[name] else (command_help[name], "")
                    print(f"  {syntax:<46} {description}")
            return

        if topic is None or topic in {"all", "commands", "commande", "commandes", "systeme", "système"}:
            print(sections["systeme"])
            return

        if topic in command_help:
            entry = command_help[topic]
            syntax, description = entry.split(" — ", 1) if " — " in entry else (entry, "")
            cmd_name = syntax.split()[0]
            print(f"COMMANDE — {cmd_name}")
            print("=" * 78)
            print(f"SYNTAXE\n  {syntax}")
            if topic in argument_notes:
                print("\nARGUMENTS")
                for token, desc in argument_notes[topic]:
                    print(f"  {token:<24} {desc}")
            else:
                import re
                found = re.findall(r"<[^>]+>|\[[^\]]+\]", syntax[len(cmd_name):])
                if found:
                    print("\nARGUMENTS")
                    for token in found:
                        optional = token.startswith("[")
                        label = token[1:-1] if optional else token[1:-1]
                        desc = "Argument optionnel." if optional else "Argument obligatoire."
                        if label.endswith("..."):
                            desc = "Arguments supplémentaires optionnels." if optional else "Liste d'arguments."
                        print(f"  {token:<24} {desc}")
            print("\nDESCRIPTION")
            print(f"  {description}")
            if topic == "write":
                print("\nÉDITEUR MULTI-LIGNES")
                print("  .save               Enregistre et quitte")
                print("  .cancel             Annule les modifications")
                print("  .show               Affiche le contenu courant")
                print("  .clear              Efface tout le contenu")
                print("  .editligne <ligne>  Sélectionne et remplace directement une ligne")
            if topic == "run":
                print("\nRECHERCHE")
                print("  Cherche d'abord dans le dossier courant, puis dans PATH pour les .mexe.")
                print("  Un .mexe peut être appelé avec ou sans son extension.")
                print("\nMODE MINILANG SOURCE")
                print("  run -mini fichier.mini [args...] [&]")
                print("  Le source est compilé en mémoire puis exécuté; aucun .mexe n'est créé.")
                print("  Les arguments sont accessibles dans le programme avec argc() et arg(index).")
            if topic == "import":
                print("\nFORMATS")
                print("  Les chemins Windows sont acceptés. Les RTF peuvent être convertis en texte brut.")
            if topic == "export":
                print("\nDESTINATION")
                print("  Le dernier argument peut être un fichier réel ou un dossier réel existant.")
            ex = examples.get(topic, [])
            if ex:
                print("\nEXEMPLES")
                for line in ex:
                    print(f"  {line}")
            return

        if topic in sections:
            print(sections[topic])
            return

        print(f"help: sujet inconnu : {topic}")
        print("Utilise `help` pour la liste rapide ou `help <commande>` pour une commande précise.")
        print("Topics : os, filesystem, executables, compiler, java, process, vm, storage, network, internet,")
        print("         minilang, minilangc, graphics, strings, arrays, memory, host, system-api, arguments")

    def cmd_helpfile(self, args):
        """Génère un fichier texte contenant la documentation des commandes miniOS et de MiniLang."""
        destination = self.resolve(args[0]) if args else "/home/user/miniOS_help.txt"
        argument_notes = self._command_argument_notes()
        examples = self._command_examples()

        # Réutilise la source de vérité de cmd_help pour éviter que le fichier
        # d'aide ne diverge de l'aide affichée dans le terminal.
        sections = {
            "systeme": """SYSTÈME
  help [topic]                         Affiche l'aide générale ou un topic.
  clear                                Efface l'écran du terminal.
  echo <texte...>                      Affiche du texte.
  uname                                Affiche l'architecture miniOS.
  version                              Affiche la version de miniOS.
  whoami                               Affiche l'utilisateur courant.
  hostname                             Affiche le nom de la machine virtuelle.
  uptime                               Affiche depuis combien de temps miniOS tourne.
  date                                 Affiche la date/heure locale.
  reboot                               Redémarre (simulation dans 0.5).
  shutdown                             Demande l'arrêt de miniOS.
  exit                                 Quitte miniOS.

TOPICS: os, filesystem, executables, compiler, java, process, vm, storage, network, internet,
        minilang, minilangc, graphics, strings, arrays, memory, host, system-api

PIPES / ENTRÉE STANDARD
  commande1 | commande2                Envoie la sortie de commande1 vers l'entrée standard de commande2.
  input() / input("Question")          Lit depuis le pipe lorsqu'une entrée est fournie, sinon depuis le terminal.
  inputInt() / inputInt("Question")    Même principe pour un entier.
""",
            "filesystem": """SYSTÈME DE FICHIERS VIRTUEL
  pwd                                   Affiche le dossier courant.
  cd <chemin>                           Change de dossier et affiche le nouveau chemin.
  ls [chemin]                           Liste fichiers et répertoires.
  mkdir <chemin> [-p]                   Crée un répertoire; -p crée les parents.
  rmdir <chemin>                        Supprime un répertoire vide.
  touch <fichier>                       Crée un fichier vide.
  cat <fichier>                         Affiche un fichier.
  write <fichier> [texte]               Écrit/remplace un fichier.
  write <fichier>                       Ouvre l'éditeur multi-lignes.
  write <fichier> [-l|--line <ligne> [texte]] Remplace une ligne précise (numérotation à partir de 1).
  Éditeur: .save, .cancel, .show, .clear, .editligne <ligne>.
  edit <fichier>                        Ouvre l'éditeur multi-lignes.
  edit <fichier> -l <ligne>             Édite directement une ligne précise.
  edit <fichier> -l <ligne> texte        Remplace directement une ligne.
  append <fichier> [texte]              Ajoute du texte au fichier.
  rm <fichier> [-r]                     Supprime un fichier; -r supprime récursivement.
  cp <source> <destination>             Copie un fichier ou répertoire.
  mv <source> <destination>             Déplace/renomme un fichier ou répertoire.
  find [chemin] [nom]                   Recherche dans l'arborescence.
  tree [chemin]                         Affiche l'arborescence.
  stat <chemin>                         Affiche les informations d'un fichier/répertoire.
  head <fichier>                        Affiche les 10 premières lignes.
  tail <fichier>                        Affiche les 10 dernières lignes.
  wc <fichier>                          Affiche mots, lignes et octets.

JOKERS / MOTIFS
  *                                     Plusieurs caractères du même niveau de dossier.
  ?                                     Un seul caractère.
  [...]                                Classe de caractères.
  **                                   Peut traverser plusieurs sous-dossiers virtuels.
  Exemple : rm *.mini, cp *.mexe /path/, export /home/user/*.mini D:\\miniapp

CHEMINS
  /                                     Racine du disque virtuel.
  .                                     Dossier courant.
  ..                                    Dossier parent.
  ~                                     /home/user.
  /path                                 Répertoire d'exécutables privilégié.
  /bin, /apps                           Autres répertoires recherchés dans PATH.
""",
            "executables": """EXÉCUTION ET PROGRAMMES
  run <programme> [args...]             Lance un .mexe en premier plan.
  run <programme> [args...] &           Lance un .mexe en arrière-plan; le shell reste libre.
  exec <programme> [args...]            Alias de run.
  wait <pid>                             Attend la fin d’un processus de fond.
  jobs                                   Alias de ps.
  <programme> [args...]                 Lance automatiquement un .mexe trouvé dans PATH.
  which <commande>                      Indique builtin ou chemin du .mexe trouvé.
  path                                  Affiche PATH et ses répertoires.
  ps                                    Liste les processus connus.
  kill <pid>                            Arrête un processus VM32.
  debug <pid>                           Affiche l'état d'un processus VM32.
  apps                                  Liste /apps.
  install <...>                         Gestionnaire d'applications (minimal en 0.5).
  uninstall <...>                       Gestionnaire d'applications (minimal en 0.5).

EXEMPLE
  mv monapp.mexe /path/
  monapp
  monapp argument1 argument2
  monapp argument1 &                      Lance en arrière-plan.
""",
            "compiler": """COMPILATEUR MINILANG
  newapp <nom>                          Crée un squelette .mini.
  compile <source.mini> [sortie.mexe]   Compile MiniLang vers MEXE2/VM32.
  build <source.mini> [sortie.mexe]     Alias de compile.

ÉDITEUR MULTI-LIGNES
  write programme.mini
  edit programme.mini
  .save                                 Enregistre et quitte.
  .cancel                               Annule les modifications.
  .show                                 Affiche le contenu courant.
  .clear                                Efface tout le contenu.
  .editligne <ligne>                    Édite directement la ligne indiquée.

ERREURS
  Les erreurs de syntaxe/compilation indiquent ligne et colonne lorsque possible.
  Un identifiant non déclaré produit une erreur de compilation explicite.
""",
            "java": """JAVA / JVM
  javac <fichier.java> [sortie.class]   Compile un sous-ensemble Java vers .class.
  java <fichier.class> [args...]        Exécute une classe JVM.
  java <fichier.jar> [args...]          Charge un JAR et son Main-Class.
  java <fichier.java> [args...]         Compile le source en mémoire puis l'exécute.

JAVA ACTUELLEMENT RECONNU
  int, boolean, String, variables, calculs, if/else, while, for,
  méthodes static, return, System.out.print/println, concaténation.

ENTRÉE/SYSTÈME JAVA
  input(["Question"])                     Lecture d'une chaîne utilisateur.
  inputInt(["Question"])                  Lecture d'un entier.
  System.getProperty("os.name")        Informations du runtime miniOS.
  System.getenv("PATH")                 Environnement virtuel.

REMARQUE
  Le compilateur Java intégré reste un sous-ensemble: ce n'est pas encore javac/OpenJDK complet.
""",
            "process": """PROCESSUS
  ps                                    Liste PID, état et nom.
  kill <pid>                            Marque un processus comme tué.
  debug <pid>                           Affiche PID, PC, SP et nombre d'instructions.
  run / exec <programme> [args...]      Crée un processus VM32.
  run ... &                              Processus de fond; le terminal reste utilisable.
  wait <pid>                             Attend la fin d’un processus.
  jobs                                   Affiche les processus (alias de ps).
""",
            "vm": """VM32
  mem                                   Affiche la taille de RAM VM32.
  cpu                                   Décrit le CPU VM32.
  regs                                  Affiche les registres R0..R7.
  stack                                 Décrit la pile VM32.
  heap                                  Affiche la zone de heap VM32.
  info                                  Affiche les informations générales VM/JVM/disque.
  test                                  Lance les tests internes disponibles.

FORMAT EXÉCUTABLE
  MEXE2                                 Format binaire des applications VM32.
""",
            "storage": """STOCKAGE RÉEL / VIRTUEL
  disk                                  Affiche le fichier de persistance du disque virtuel.
  import <réel> [virtuel]               Copie PC réel -> disque virtuel.
  export <virtuel> <réel>               Copie disque virtuel -> PC réel.

IMPORT
  import détecte automatiquement un fichier RTF et le convertit en texte brut.
  Les chemins Windows C:\\... et UNC \\\\serveur\\... sont conservés.

PERSISTANCE
  Le disque virtuel est sauvegardé dans minios_disk.json (emplacement configurable).
""",
            "network": """RÉSEAU HÔTE
  net                                   État et connectivité du réseau réel.
  ifconfig                              Interfaces/adresses détectées via Python.
  ipconfig                              Alias de ifconfig.
  ping [hôte] [timeout_ms]              Ping ICMP implémenté avec socket brut.
  nslookup <hôte>                       Résolution DNS via socket.getaddrinfo.
  netstat                               Sockets via /proc sur Linux (sans netstat/ss).
  route                                 Routes via /proc sur Linux, fallback Python ailleurs.

INTERNET POUR LES APPLICATIONS
  Les applications .mexe peuvent utiliser httpGet/httpPost/httpDownload/dnsResolve.
  Ces fonctions utilisent HTTP/HTTPS et DNS du système hôte, sans paquet externe.
""",
            "minilangc": """COMMANDE — minilang

SYNTAXE
  minilang <code>                        Exécute directement du code MiniLang depuis le terminal.

DESCRIPTION
  Lance un programme MiniLang court directement depuis la ligne de commande.
  Pour la référence complète du langage, utilise : help minilang

ARGUMENTS
  <code>                                 Code MiniLang à exécuter.

EXEMPLES
  minilang print("Bonjour")
  minilang let x = 10; print(x)

DOCUMENTATION
  help minilangc                         Affiche cette documentation de la commande minilang.
""",
            "minilang": self._minilang_help_text(),
            "strings": """MINILANG — CHAÎNES
  len(s)                               Longueur.
  str(x)                               Convertit en chaîne.
  int(x)                               Convertit en entier.
  substr(s, debut[, longueur])         Sous-chaîne.
  replace(s, ancien, nouveau)          Remplacement.
  contains(s, morceau)                 Contient ?
  startsWith(s, prefixe)               Commence par ?
  endsWith(s, suffixe)                 Finit par ?
  lower(s)                             Minuscules.
  upper(s)                             Majuscules.
  trim(s)                              Retire les espaces aux extrémités.
  chr(n)                               Caractère Unicode correspondant.
  ord(s)                               Code du premier caractère.
  split(s, separateur)                 Découpe en tableau de chaînes.
  join(tab, separateur)                Assemble un tableau de chaînes.
  +                                    Concatène si au moins un opérande est une chaîne.
  s[index]                             Accès à un caractère.
""",
            "arrays": """MINILANG — TABLEAUX
  array(taille)                        Crée un tableau d'entiers.
  arrayLen(tab)                        Taille du tableau.
  arrayGet(tab, index)                 Lit un entier.
  arraySet(tab, index, valeur)         Écrit un entier.
  arrayGetStr(tab, index)              Lit une valeur de tableau comme chaîne.
  arraySetStr(tab, index, valeur)      Écrit une chaîne.
  tab[index]                           Lecture/écriture directe supportée.
  split(...)                            Crée un tableau de chaînes.
  join(...)                             Convertit un tableau de chaînes en texte.
""",
            "memory": """MINILANG — MÉMOIRE VM32
  alloc(taille)                        Alloue une zone mémoire.
  free(ptr)                            Libère une allocation ; retourne 0 si succès, 1 si adresse invalide.
  read8(adresse)                       Lit 1 octet.
  read32(adresse)                      Lit 32 bits.
  write8(adresse, valeur)              Écrit 1 octet.
  write32(adresse, valeur)             Écrit 32 bits.
  memTotal()                           RAM totale exposée au processus.
  memFree()                            RAM libre exposée au processus.
""",
            "host": """MINILANG — SYSTÈME DE FICHIERS RÉEL (HÔTE)
  importHost(réel, virtuel)            Importe un fichier du PC dans miniOS.
  exportHost(virtuel, réel)            Exporte un fichier vers le PC.
  hostExists(réel)                     Teste l'existence sur le PC.
  hostRead(réel)                       Lit un fichier texte réel.
  hostWrite(réel, texte)               Écrit un fichier texte réel.
  hostAppend(réel, texte)              Ajoute au fichier texte réel.
  hostDelete(réel)                     Supprime sur le PC.
  hostMkdir(répertoire)                Crée un répertoire réel.
  hostList(répertoire)                 Liste un répertoire réel.
  hostIsDir(chemin)                    Teste si un chemin réel est un dossier.
  hostSize(chemin)                     Taille d'un fichier réel.

ATTENTION
  Ces fonctions touchent le système de fichiers du PC hôte et doivent être utilisées volontairement.
""",
            "system-api": """MINILANG — API SYSTÈME
  input([question])                      Saisie chaîne.
  inputInt([question])                   Saisie entier.
  system(cle)                          Propriété miniOS.
  env(nom)                             Variable d'environnement virtuelle.
  envSet(nom, valeur)                  Définit une variable virtuelle.
  argc()                               Nombre d'arguments.
  arg(index)                           Argument du programme.
  cwd()                                Dossier courant du processus.
  chdir(chemin)                        Change le dossier courant.
  shell(commande) / command(commande)  Exécute une commande miniOS.
  exec(commande)                       Exécute une commande et capture sa sortie.
  sysf(fonction[, args...])            Appelle une fonction système native par son nom.
  run(programme[, args...])            Lance un .mexe.
  sleep(ms)                            Pause en millisecondes.
  time()                               Temps Unix en secondes.
  timeMs()                             Temps Unix en millisecondes.
  random(max)                          Entier aléatoire dans [0,max).
  randomRange(min,max)                 Entier aléatoire dans [min,max].
  ping(hôte)                           Ping virtuel.
  httpGet(url[, timeout])              Requête GET HTTP/HTTPS réelle.
  httpPost(url, corps[, type[, timeout]]) Requête POST HTTP/HTTPS réelle.
  httpDownload(url, chemin[, timeout]) Téléchargement vers le disque virtuel.
  dnsResolve(hôte)                     Résolution DNS réelle.
  pid()                                PID courant.
  program()                            Nom du programme courant.
  hostname()                           Nom de la machine miniOS.
""",
            "graphics": """MINILANG — MOTEUR GRAPHIQUE 2D
  Moteur : SoftwareRenderer (framebuffer CPU, indépendant du toolkit).
  Présentation : framebuffer présenté par un backend natif de la plateforme (Win32/X11/Cocoa via ctypes; iOS via hôte UIKit).
  Chrome : barre de titre graphique miniOS avec boutons minimiser et fermer, dessinée par le renderer.
  Rendu v1 : pixels, lignes, rectangles, cercles et texte bitmap 5x7.
  Plateformes : Windows=Win32, Linux=X11/XWayland, macOS=Cocoa/AppKit, iOS=UIKit via une application hôte.
  Linux : backend X11 natif via libX11 et DISPLAY (compatible XWayland) ; pas de toolkit Python.
  macOS : backend Cocoa/AppKit + CoreGraphics via Objective-C runtime ; pas de toolkit Python.

  window(titre, largeur, hauteur)      Crée/ouvre une fenêtre.
  clear(couleur)                       Efface la surface.
  pixel(x, y, couleur)                 Dessine un pixel.
  rect(x,y,largeur,hauteur,couleur)    Rectangle.
  line(x1,y1,x2,y2,couleur)            Ligne.
  circle(x,y,rayon,couleur)            Cercle.
  text(x,y,texte,couleur)              Texte.
  present()                            Présente le framebuffer.
  close()                              Ferme la fenêtre courante.
  windowAlive()                        Fenêtre encore ouverte ?
  closeRequested()                    L'utilisateur a demandé la fermeture ?
  Barre de fenêtre                     Boutons graphiques _ (minimiser) et X (fermer).
  keyDown(touche)                      Touche enfoncée ?
  keyPressed(touche)                   Nouvel appui de touche ?
  textInput([action])                  Capture du texte saisi (start/get/stop/clear).
  mouseX()                             Position X de la souris.
  mouseY()                             Position Y de la souris.
  mouseDown(bouton)                    Bouton souris enfoncé ?
  rgb(r,g,b)                           Encode une couleur RGB 24 bits.
  imageLoad(chemin)                      Charge une image PNG, BMP 24/32 bits ou PPM.
  imageDraw(image,x,y)                   Dessine l'image à sa taille native.
  imageDrawScaled(image,x,y,w,h)        Dessine l'image redimensionnée.
  imageWidth(image) / imageHeight(image) Dimensions de l'image.
  imageFree(image)                       Libère le handle image (0 = succès).

EXEMPLE
  window("Test", 800, 600)
  clear(rgb(20, 20, 20))
  rect(100, 100, 200, 120, rgb(255, 0, 0))
  circle(500, 300, 50, rgb(0, 255, 0))
  text(120, 130, "Bonjour", rgb(255, 255, 255))
  present()
""",
        }

        command_help = {
            "help": "help [topic] — affiche l'aide générale ou la documentation d'un topic.",
            "clear": "clear — efface le terminal.",
            "echo": "echo <texte...> — affiche du texte; sa sortie peut être envoyée dans un pipe avec |.",
            "uname": "uname — affiche l'architecture miniOS.",
            "version": "version — affiche la version.",
            "whoami": "whoami — affiche l'utilisateur courant.",
            "hostname": "hostname — affiche le nom de la machine virtuelle.",
            "uptime": "uptime — affiche le temps depuis le démarrage.",
            "date": "date — affiche la date et l'heure locales.",
            "reboot": "reboot — redémarrage simulé.",
            "shutdown": "shutdown — demande l'arrêt de miniOS.",
            "exit": "exit — quitte miniOS.",
            "ls": "ls [chemin|motif] — liste le contenu d'un répertoire ou les correspondances d'un motif.",
            "cd": "cd <chemin> — change le dossier courant et affiche le nouveau chemin.",
            "pwd": "pwd — affiche le dossier courant.",
            "mkdir": "mkdir <chemin> [-p] — crée un répertoire.",
            "rmdir": "rmdir <chemin> — supprime un répertoire vide.",
            "touch": "touch <fichier> — crée un fichier vide.",
            "cat": "cat <fichier|motif> — affiche un ou plusieurs fichiers.",
            "write": "write <fichier> [texte] | write <fichier> [-l|--line <ligne> [texte]] — écrit/remplace un fichier ou une ligne précise. Sans texte, ouvre l'éditeur multi-lignes; commandes: .save, .cancel, .show, .clear, .editligne <ligne>.",
            "edit": "edit <fichier> -l <ligne> [texte] — remplace une ligne précise; sans texte, la nouvelle ligne est demandée interactively. Sans -l, ouvre l'éditeur multi-lignes.",
            "append": "append <fichier> [texte] — ajoute au fichier.",
            "rm": "rm <fichier|répertoire|motif> [-r] — supprime un ou plusieurs éléments; les jokers sont acceptés.",
            "cp": "cp <source|motif> <destination> — copie un ou plusieurs éléments; les jokers sont acceptés.",
            "mv": "mv <source|motif> <destination> — déplace/renomme un ou plusieurs éléments; les jokers sont acceptés.",
            "find": "find [chemin] [motif] — recherche récursive.",
            "tree": "tree [chemin] — affiche l'arborescence.",
            "stat": "stat <chemin> — affiche type et taille.",
            "head": "head <fichier> — dix premières lignes.",
            "tail": "tail <fichier> — dix dernières lignes.",
            "wc": "wc <fichier> — compte mots, lignes et octets.",
            "run": "run [-debug|-debg] <programme> [args...] [&] ou run [-debug|-debg] -mini <fichier.mini> [args...] [&] — lance un .mexe ou un source MiniLang compilé en mémoire.",
            "exec": "exec <programme> [args...] — alias d'exécution VM32.",
            "which": "which <commande> — indique builtin ou chemin du programme trouvé.",
            "path": "path — affiche la variable PATH et ses répertoires.",
            "ps": "ps — liste les processus.",
            "kill": "kill <pid> — termine un processus VM32.",
            "debug": "debug <pid> [--graphics] — affiche l'état détaillé d'un processus; --graphics ajoute le diagnostic GUI.",
            "gdebug": "gdebug <pid> — affiche directement le diagnostic graphique détaillé du processus.",
            "newapp": "newapp <nom> — crée un squelette MiniLang.",
            "compile": "compile <source.mini> [sortie.mexe] — compile MiniLang vers MEXE2.",
            "build": "build <source.mini> [sortie.mexe] — alias de compile.",
            "java": "java <.class|.jar|.java> [args...] — exécute ou compile puis exécute du Java.",
            "javac": "javac <source.java> [sortie.class] — compile le sous-ensemble Java intégré.",
            "apps": "apps — liste les applications disponibles dans /apps.",
            "install": "install <...> — installation d'application (minimal en 0.5).",
            "uninstall": "uninstall <...> — désinstallation d'application (minimal en 0.5).",
            "mem": "mem — affiche la RAM VM32.",
            "cpu": "cpu — affiche les caractéristiques du CPU VM32.",
            "regs": "regs — affiche les registres VM32.",
            "stack": "stack — affiche la pile VM32.",
            "heap": "heap — affiche le heap VM32.",
            "info": "info — affiche une synthèse de miniOS, VM, JVM et disque.",
            "test": "test — lance les tests internes.",
            "disk": "disk — affiche le stockage persistant du disque virtuel.",
            "import": "import <fichier réel|motif> [chemin virtuel] — copie un ou plusieurs fichiers du PC vers miniOS; les jokers sont acceptés.",
            "download": "download <url> <fichier> [timeout] — télécharge un fichier HTTP/HTTPS vers le disque virtuel.",
            "export": "export <fichier virtuel|motif> <fichier réel> — copie un ou plusieurs fichiers de miniOS vers le PC; les jokers sont acceptés.",
            "env": "env — affiche les variables d'environnement virtuelles.",
            "set": "set NOM=VALEUR — définit une variable d'environnement virtuelle.",
            "history": "history — affiche l'historique des commandes.",
            "net": "net — affiche l'état du réseau réel de la machine (adresses et connectivité Internet).",
            "ifconfig": "ifconfig — affiche les interfaces réseau détectées par les API Python; aucun outil externe n'est lancé.",
            "ipconfig": "ipconfig — alias de ifconfig; affiche les interfaces réseau réelles.",
            "ping": "ping [hôte] [timeout_ms] — effectue un ping ICMP sans lancer ping.exe ou ping.",
            "nslookup": "nslookup <hôte> — résout un nom via socket.getaddrinfo, sans nslookup.exe.",
            "netstat": "netstat — affiche les sockets exposées par miniOS via Python/procfs; aucun netstat/ss n'est lancé.",
            "route": "route — affiche la table de routage accessible sans outil externe.",
            "networktest": "networktest [hôte] [port] — teste le réseau réel miniOS et l'accès Internet avec des codes d'erreur. Le ping localhost est obligatoire ; le ping Internet est informatif. Codes 101-112.",
            "helpfile": "helpfile [fichier.txt] — génère un fichier texte avec toute la documentation disponible.",
            "minilangc": "minilang <code> — exécute directement une instruction ou un petit programme MiniLang.",
        }

        lines = []
        lines.append(f"{VERSION} — DOCUMENTATION COMPLÈTE")
        lines.append("=" * 78)
        lines.append("")
        lines.append("Ce fichier est généré par la commande 'helpfile'.")
        lines.append(f"Destination : {destination}")
        lines.append("")

        lines.append("COMMANDES DU TERMINAL — RÉFÉRENCE COMPLÈTE")
        lines.append("-" * 78)
        lines.append("Chaque commande est donnée avec sa syntaxe, son arité et une description.")
        lines.append("")
        for name in sorted(command_help):
            syntax, description = command_help[name].split(" — ", 1) if " — " in command_help[name] else (command_help[name], "")
            lines.append(f"  {syntax}")
            lines.append(f"    Description : {description}")
            notes = argument_notes.get(name)
            if notes:
                lines.append("    Arguments :")
                for token, desc in notes:
                    lines.append(f"      {token:<20} {desc}")
            examples_for_cmd = examples.get(name, [])
            if examples_for_cmd:
                lines.append("    Exemples :")
                for ex in examples_for_cmd:
                    lines.append(f"      {ex}")
            lines.append("")

        for topic in (
            "systeme", "os", "filesystem", "executables", "compiler", "java", "process",
            "vm", "storage", "network", "internet", "minilang", "minilangc", "strings", "arrays",
            "memory", "host", "system-api", "graphics"
        ):
            lines.append(sections[topic].rstrip())
            lines.append("")

        lines.append("NOTES")
        lines.append("-" * 78)
        lines.append("Les applications .mexe utilisent la VM32 de miniOS et peuvent accéder aux API MiniLang.")
        lines.append("Le PATH par défaut contient /bin:/path:/apps.")
        lines.append("Le disque virtuel est persistant et est sauvegardé dans minios_disk.json.")
        lines.append("Les fonctions host* peuvent toucher le système de fichiers réel du PC.")
        lines.append("Le support Java/JVM est encore un sous-ensemble et évoluera avec les prochaines versions.")

        content = "\n".join(lines) + "\n"
        try:
            self.disk.write(destination, content)
            print(f"helpfile: documentation générée dans {destination} ({len(content.encode('utf-8'))} octets)")
        except Exception as e:
            print(f"helpfile: {e}")

    def cmd_clear(self, args):
        os.system("cls" if os.name == "nt" else "clear")

    def cmd_uname(self, args): print("miniOS VM32 + JVM 0.5")
    def cmd_version(self, args): print(VERSION)
    def cmd_whoami(self, args): print("user")
    def cmd_hostname(self, args): print(HOSTNAME)
    def cmd_uptime(self, args): print(f"up {int(time.time() - self.boot_time)}s")
    def cmd_date(self, args): print(datetime.datetime.now().astimezone().isoformat(timespec="seconds"))
    def cmd_echo(self, args): print(" ".join(args))

    # ------------------ processes / VM ------------------
    def cmd_ps(self, args):
        print("PID  STATE          AGE     STEPS   NAME")
        with self.process_lock:
            for pid, p in sorted(self.processes.items()):
                print(f"{pid:<4} {p.state:<14} {p.runtime:>6.1f}s {p.cpu.steps:>7}   {p.name}")

    def cmd_jobs(self, args):
        self.cmd_ps(args)

    def cmd_kill(self, args):
        if not args: print("Usage: kill <pid>"); return
        try:
            pid = int(args[0]); p = self.processes.get(pid)
            if not p: print("kill: PID introuvable"); return
            p.request_stop()
            print(f"PID {pid}: arrêt demandé")
        except ValueError: print("kill: PID invalide")

    def cmd_debug(self, args):
        if not args:
            print("Usage: debug <pid> [--graphics]")
            return
        graphics_mode = any(str(a).lower() in ("--graphics", "-g", "gfx", "graphics") for a in args[1:])
        try:
            pid = int(args[0])
            p = self.processes[pid]
            print(f"PID={p.pid} state={p.state} pc=0x{p.cpu.pc:04X} sp=0x{p.cpu.sp:08X} steps={p.cpu.steps} age={p.runtime:.1f}s background={p.background}")
            if p.error is not None:
                print(f"Erreur processus : {type(p.error).__name__}: {p.error}")
            if graphics_mode:
                info = self.graphics.debug_snapshot(pid)
                print("GRAPHICS DEBUG")
                print(f"  Backend           : {info.get('backend')}")
                print(f"  Mainloop          : {info.get('mainloop')}")
                print(f"  Thread graphique  : {info.get('main_thread')}")
                print(f"  Thread appelant   : {info.get('current_thread')}")
                print(f"  Queue GUI         : {info.get('queue_size')}")
                print(f"  Window ID         : {info.get('window_id')}")
                print(f"  Fenêtre logique   : {info.get('logical_alive')}")
                print(f"  Fermeture demandée: {info.get('close_requested')}")
                stats = info.get('stats', {})
                if stats:
                    print(f"  Appels GUI        : {stats.get('calls', 0)}")
                    print(f"  Erreurs GUI       : {stats.get('errors', 0)}")
                    print(f"  presents()        : {stats.get('presents', 0)}")
                    print(f"  Fenêtres créées   : {stats.get('windows_created', 0)}")
                    print(f"  Dernier appel     : {stats.get('last_op', '')}")
                    print(f"  Dernière durée    : {stats.get('last_duration_ms', 0.0):.3f} ms")
                    if stats.get('last_error'):
                        print(f"  Dernière erreur   : {stats['last_error']}")
                    recent = stats.get('recent', [])
                    if recent:
                        print("  Derniers appels   :")
                        for entry in recent[-10:]:
                            line = f"    {entry.get('op')} ({entry.get('ms', 0):.3f} ms)"
                            if entry.get('error'):
                                line += f" -> {entry['error']}"
                            print(line)
                w = info.get('window')
                if isinstance(w, dict):
                    print("  Fenêtre :")
                    print(f"    titre            : {w.get('title')}")
                    print(f"    taille           : {w.get('width')}x{w.get('height')}")
                    print(f"    alive             : {w.get('alive')}")
                    print(f"    close_requested   : {w.get('close_requested')}")
                    print(f"    souris            : {w.get('mouse_x')},{w.get('mouse_y')}")
                    print(f"    touches           : {', '.join(w.get('keys', [])) or 'aucune'}")
                    print(f"    boutons           : {', '.join(map(str, w.get('buttons', []))) or 'aucun'}")
                elif info.get('window_error'):
                    print(f"  Fenêtre            : erreur: {info['window_error']}")
        except (ValueError, KeyError):
            print("debug: PID invalide ou introuvable")
        except Exception as e:
            print(f"debug: {e}")

    def cmd_gdebug(self, args):
        if not args:
            print("Usage: gdebug <pid>")
            return
        self.cmd_debug([args[0], "--graphics"])

    def cmd_mem(self, args): print(f"RAM VM32: {RAM_SIZE} octets")
    def cmd_cpu(self, args): print("VM32 CPU: 8 registres 32-bit, PC/SP, flags Z/N/C")
    def cmd_regs(self, args): print("R0..R7:", " ".join(f"R{i}=0x{v:08X}" for i, v in enumerate([0]*8)))
    def cmd_stack(self, args): print("Stack VM32: SP haut-mémoire")
    def cmd_heap(self, args): print(f"Heap VM32: 0x{MemoryManager.HEAP_START:08X}-0x{MemoryManager.HEAP_END:08X} (bump allocator)")
    def cmd_info(self, args):
        print(VERSION)
        print("CPU: VM32")
        print(f"RAM VM32: {RAM_SIZE // 1024} KiB")
        print(f"JVM classes chargées: {len(self.jvm.loaded)}")
        print(f"JVM heap objets: {len(self.jvm.heap)}")
        print(f"Disque virtuel: {self.disk.storage_path}")

    def cmd_disk(self, args):
        """Affiche l'état du disque virtuel persistant."""
        try:
            file_count = len(self.disk.files)
            dir_count = len(self.disk.dirs)
            real_size = 0
            try:
                if os.path.isfile(self.disk.storage_path):
                    real_size = os.path.getsize(self.disk.storage_path)
            except OSError:
                real_size = 0
            print(f"Disque virtuel: {self.disk.storage_path}")
            print(f"Répertoires: {dir_count} | Fichiers: {file_count}")
            print(f"Taille du disque réel: {real_size} octets")
        except Exception as e:
            print(f"disk: erreur: {e}")

    # ------------------ MiniLang / app / compiler ------------------
    def cmd_newapp(self, args):
        if not args:
            print("Usage: newapp <nom>")
            return
        name = args[0]
        if not name or not all(ch.isalnum() or ch == "_" for ch in name) or name[0].isdigit():
            print("newapp: nom invalide (lettres, chiffres et _)" )
            return
        path = self.resolve(name + ".mini")
        if self.disk.exists(path):
            print(f"newapp: existe déjà: {path}")
            return
        source = (
            f"# Application MiniLang {name}\n"
            "# Exemple avec variable, boucle et condition\n"
            "let total = 0\n"
            "for (let i = 1; i <= 5; i++) {\n"
            "    total += i\n"
            "}\n"
            f'print("Application {name}")\n'
            'print("Total =")\n'
            'print(total)\n'
        )
        self.disk.write(path, source)
        print(f"application créée: {path}")
        print(f"compile {name}.mini {name}.mexe")

    def _compile_host(self, src_path: str, out_path: str):
        with open(src_path, "rb") as f:
            raw = f.read()
        raw, converted_rtf = maybe_decode_rtf(raw)
        src = decode_text_bytes(raw)
        exe = MiniLang.compile_placeholder(src)
        with open(out_path, "wb") as f:
            f.write(exe.encode())
        if converted_rtf:
            print(f"[COMPILATION] Source RTF détecté et converti en texte brut: {src_path}")
        return exe

    def _report_compile_error(self, e: Exception):
        print("[31m[COMPILATION] ERREUR[0m")
        print(f"[COMPILATION] {e}")

    def cmd_compile(self, args):
        if not args:
            print("Usage: compile <source.mini> [sortie.mexe]")
            return

        try:
            # Un nom relatif (ex: test.mini) désigne d'abord le fichier du
            # disque virtuel courant. Cela évite qu'un fichier homonyme du
            # dossier réel de miniOS soit compilé à la place.
            raw_arg = str(args[0])
            virtual_arg = self.resolve(raw_arg)
            prefer_virtual = not os.path.isabs(raw_arg) and self.disk.exists(virtual_arg) and not self.disk.is_dir(virtual_arg)
            src = self.resolve_host_path(raw_arg)
            if prefer_virtual:
                src = ""
            if not src or not os.path.isfile(src):
                v = virtual_arg
                if self.disk.exists(v) and not self.disk.is_dir(v):
                    data = self.disk.read(v)
                    if isinstance(data, bytes):
                        raw, converted_rtf = maybe_decode_rtf(data)
                        source = decode_text_bytes(raw)
                        if converted_rtf:
                            # Met à jour le fichier virtuel pour éviter de le reconvertir.
                            self.disk.write(v, raw)
                            print(f"[COMPILATION] Source RTF détecté et converti: {v}")
                    else:
                        source = str(data)
                    exe = MiniLang.compile_placeholder(source)
                    out = self.resolve(args[1] if len(args) > 1 else args[0].rsplit(".", 1)[0] + ".mexe")
                    self.disk.write(out, exe.encode())
                    print(f"compilé: {out}")
                    return
                print(f"compile: source introuvable: {args[0]}")
                return

            out = self.resolve_host_path(args[1]) if len(args) > 1 else os.path.splitext(src)[0] + ".mexe"
            self._compile_host(src, out)
            print(f"compilé: {out}")
        except MiniLangCompileError as e:
            self._report_compile_error(e)
        except SyntaxError as e:
            print("[COMPILATION] ERREUR de syntaxe")
            print(f"[COMPILATION] Ligne {getattr(e, 'lineno', '?')}: {e.msg}")
        except Exception as e:
            print(f"[COMPILATION] ERREUR: {e}")

    def cmd_build(self, args): self.cmd_compile(args)
    def cmd_apps(self, args):
        for name, isdir in self.disk.ls("/apps"):
            if isdir: print(name + "/")
            else: print(name)

    def cmd_install(self, args): print("install: gestionnaire d'applications virtuel minimal en 0.5")
    def cmd_uninstall(self, args): print("uninstall: gestionnaire d'applications virtuel minimal en 0.5")

    def cmd_net(self, args):
        """Affiche l'état réseau réel sans lancer d'outil système."""
        hostname = socket.gethostname()
        ips = _host_ip_addresses()
        interfaces = _network_interfaces()
        ok, detail = _host_internet_check()
        print("RÉSEAU HÔTE")
        print(f"  Nom machine : {hostname}")
        print(f"  Interfaces  : {', '.join(interfaces) if interfaces else 'détection indisponible'}")
        print(f"  Adresses    : {', '.join(ips)}")
        print(f"  Internet    : {'OK' if ok else 'INDISPONIBLE'}")
        print(f"  Test        : {detail}")
        print("  Implémentation : Python/socket (aucune commande réseau externe)")

    def cmd_ifconfig(self, args):
        """Affiche les informations réseau disponibles via l'API Python."""
        interfaces = _network_interfaces()
        addresses = _network_local_addresses()
        print("INTERFACES RÉSEAU miniOS")
        if interfaces:
            for idx, name in enumerate(interfaces, 1):
                print(f"{idx}: {name}")
        else:
            print("(noms d'interfaces indisponibles via l'API Python de cette plateforme)")
        print("\nADRESSES LOCALES CONNUES")
        for addr in addresses:
            print(f"  {addr}")
        print("\nNote: aucun binaire ifconfig/ipconfig n'est exécuté.")

    def cmd_ipconfig(self, args):
        """Alias de ifconfig, indépendant de la commande Windows ipconfig."""
        self.cmd_ifconfig(args)

    def cmd_ping(self, args, quiet=False):
        """Effectue un ping ICMP IPv4 avec un socket Python brut."""
        target = args[0] if args else "127.0.0.1"
        timeout = 2000
        if len(args) >= 2:
            try:
                timeout = max(100, min(10000, int(args[1])))
            except ValueError:
                if not quiet:
                    print("ping: délai invalide (millisecondes)")
                return 1
        ok, latency, detail = _host_ping(target, timeout)
        if not quiet:
            print(f"PING {target}")
            if ok:
                print(f"Réponse de {detail}: temps={latency:.2f} ms")
                print("ping: hôte joignable")
            else:
                print(f"Erreur: {detail}")
                print("ping: hôte inaccessible ou ping ICMP interdit")
        return 0 if ok else 1

    def cmd_nslookup(self, args):
        """Résout un nom DNS via socket.getaddrinfo, sans nslookup.exe."""
        if not args:
            print("Usage: nslookup <hôte>")
            return
        host = args[0]
        try:
            addresses = _host_dns_resolve(host)
            print(f"Nom: {host}")
            for addr in addresses:
                print(f"Adresse: {addr}")
        except OSError as exc:
            print(f"nslookup: résolution impossible pour {host}: {exc}")

    def cmd_netstat(self, args):
        """Affiche les sockets Linux via /proc, ou un état minimal ailleurs."""
        rows = _network_netstat_rows()
        print("NETSTAT miniOS")
        if rows:
            print(f"{'Proto':<6} {'Local':<24} {'Distant':<24} État")
            for row in rows:
                print(f"{row.get('proto','?'):<6} {row.get('local','?'):<24} {row.get('remote','?'):<24} {row.get('state','?')}")
        else:
            print("La table des sockets hôte n'est pas exposée par la bibliothèque standard sur cette plateforme.")
            print("Les connexions ouvertes par les API réseau miniOS restent néanmoins utilisables.")
        print("Implémentation : Python + API système/fichiers, aucune commande netstat/ss.")

    def cmd_route(self, args):
        """Affiche la table de routage via les informations accessibles à Python."""
        print("ROUTE miniOS")
        for row in _network_route_rows():
            print(row)
        print("Implémentation : Python/procfs ou primitives socket, aucune commande route/ip.")

    def cmd_networktest(self, args):
        """Teste séparément les fonctions réseau miniOS.

        Le ping localhost est un test obligatoire de la pile ICMP locale.
        Le ping Internet est seulement informatif : beaucoup de réseaux,
        pare-feu et fournisseurs bloquent ICMP sans empêcher HTTP/TCP/DNS.
        Aucun exécutable réseau de l'hôte n'est lancé.
        """
        requested_host = args[0] if args else "example.com"
        port = 443
        if len(args) > 1:
            try:
                port = int(args[1])
            except ValueError:
                print("networktest: port invalide")
                return 2
        results = []

        def report(num, label, ok, detail="", code=None, informational=False):
            final_code = 0 if ok else int(code if code is not None else 199)
            if informational:
                state = "INFO" if not ok else "OK"
                # Un test informatif ne compte jamais comme échec global.
                reported_code = final_code if not ok else 0
            else:
                state = "OK" if ok else "ERREUR"
                reported_code = final_code
                results.append(reported_code)
            suffix = f" — {detail}" if detail else ""
            print(f"[{num:02d}] {label:<40} {state} (code={reported_code}){suffix}")

        print("NETWORKTEST — RÉSEAU RÉEL miniOS")
        print("=" * 96)
        print("Aucun outil réseau externe n'est exécuté.")
        print(f"Cible Internet : {requested_host}:{port}")
        print("Le ping Internet est informatif et ne fait pas échouer le test global.")
        print("")

        # 1. Interfaces
        try:
            interfaces = _network_interfaces()
            report(1, "Interfaces / ifconfig", bool(interfaces),
                   f"{len(interfaces)} interface(s) détectée(s)" if interfaces else "aucune interface détectée", 101)
        except Exception as exc:
            report(1, "Interfaces / ifconfig", False, str(exc), 101)

        # 2. Adresses
        try:
            addresses = _network_local_addresses()
            report(2, "Adresses / ipconfig", bool(addresses),
                   f"{len(addresses)} adresse(s) locale(s)" if addresses else "aucune adresse locale", 102)
        except Exception as exc:
            report(2, "Adresses / ipconfig", False, str(exc), 102)

        # 3. DNS réel vers la cible Internet
        try:
            addrs = _host_dns_resolve(requested_host)
            report(3, f"DNS {requested_host}", bool(addrs),
                   ", ".join(addrs[:4]) if addrs else "aucune adresse", 103)
        except Exception as exc:
            report(3, f"DNS {requested_host}", False, str(exc), 103)

        # 4. TCP réel vers Internet
        tcp_ok, tcp_detail = _host_internet_check(timeout=4.0)
        report(4, "TCP Internet", tcp_ok, tcp_detail, 104)

        # 5. TCP cible réelle (même mécanisme que tcpConnect des MEXE)
        try:
            sock = socket.create_connection((requested_host, port), timeout=5.0)
            peer = sock.getpeername()
            sock.close()
            report(5, f"TCP {requested_host}:{port}", True,
                   f"connexion vers {peer[0]}:{peer[1]}", 105)
        except Exception as exc:
            report(5, f"TCP {requested_host}:{port}", False, str(exc), 105)

        # 6. Ping ICMP localhost : obligatoire pour valider la pile ICMP.
        try:
            ping_ok, latency, detail = _host_ping("127.0.0.1", 2500)
            report(6, "Ping ICMP localhost (127.0.0.1)", ping_ok,
                   f"{detail}, {latency:.2f} ms" if ping_ok else detail, 106)
        except Exception as exc:
            report(6, "Ping ICMP localhost (127.0.0.1)", False, str(exc), 106)

        # 7. Ping ICMP Internet : informatif, jamais compté comme échec global.
        try:
            ping_ok, latency, detail = _host_ping(requested_host, 2500)
            if ping_ok:
                report(7, f"Ping ICMP Internet {requested_host}", True,
                       f"{detail}, {latency:.2f} ms", 107, informational=True)
            else:
                report(7, f"Ping ICMP Internet {requested_host}", False,
                       f"{detail} (ICMP peut être bloqué sans empêcher Internet)", 107, informational=True)
        except Exception as exc:
            report(7, f"Ping ICMP Internet {requested_host}", False,
                   f"{exc} (ICMP peut être bloqué sans empêcher Internet)", 107, informational=True)

        # 8. HTTPS GET externe réel
        try:
            status, _headers, body = Syscalls._http_get("https://" + requested_host + "/", 10.0)
            ok = 200 <= status < 400 and len(body) > 0
            report(8, f"HTTPS GET https://{requested_host}/", ok,
                   f"HTTP {status}, {len(body)} octets" if ok else f"HTTP {status}", 108)
        except Exception as exc:
            report(8, "HTTPS GET externe", False,
                   Syscalls._http_error(exc, "https://" + requested_host + "/").__str__(), 108)

        # 9. HTTPS POST externe vers une référence de test publique.
        try:
            status, _headers, body = Syscalls._http_post(
                "https://httpbin.org/post", b"miniOS-networktest",
                "text/plain; charset=utf-8", 10.0
            )
            ok = 200 <= status < 400 and b"miniOS-networktest" in body
            report(9, "HTTPS POST externe", ok,
                   f"HTTP {status}, {len(body)} octets" if ok else f"HTTP {status}, réponse inattendue", 109)
        except Exception as exc:
            report(9, "HTTPS POST externe", False,
                   Syscalls._http_error(exc, "https://httpbin.org/post").__str__(), 109)

        # 10. HTTPS téléchargement externe réel (vérifie la récupération d'octets).
        try:
            status, _headers, body = Syscalls._http_get("https://example.com/", 10.0)
            ok = 200 <= status < 400 and len(body) > 0
            report(10, "HTTPS DOWNLOAD externe", ok,
                   f"HTTP {status}, {len(body)} octets" if ok else f"HTTP {status}", 110)
        except Exception as exc:
            report(10, "HTTPS DOWNLOAD externe", False, str(exc), 110)

        # 11. UDP DNS réel : paquet DNS minimal vers 1.1.1.1:53
        try:
            transaction = os.getpid() & 0xFFFF
            qname = b"".join(bytes([len(part)]) + part.encode("ascii") for part in "example.com".split(".")) + b"\x00"
            packet = struct.pack(">HHHHHH", transaction, 0x0100, 1, 0, 0, 0) + qname + struct.pack(">HH", 1, 1)
            usock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            usock.settimeout(4.0)
            started = time.perf_counter()
            usock.sendto(packet, ("1.1.1.1", 53))
            data, addr = usock.recvfrom(4096)
            elapsed = (time.perf_counter() - started) * 1000.0
            usock.close()
            ok = len(data) >= 12 and struct.unpack(">H", data[:2])[0] == transaction
            report(11, "UDP DNS réel 1.1.1.1:53", ok,
                   f"réponse de {addr[0]}, {elapsed:.2f} ms" if ok else "transaction DNS invalide", 111)
        except Exception as exc:
            report(11, "UDP DNS réel 1.1.1.1:53", False, str(exc), 111)

        # 12. Test API tcpConnect/tcpClose comme une MEXE, vers la cible.
        test_handle = 0
        try:
            sock = socket.create_connection((requested_host, port), timeout=5.0)
            test_handle = NETWORK_SOCKETS.open(0, sock, "tcp-test")
            open_ok = NETWORK_SOCKETS.get(0, test_handle, "tcp-test") is sock
            close_ok = NETWORK_SOCKETS.close(0, test_handle)
            test_handle = 0
            report(12, "Gestion des handles TCP miniOS", open_ok and close_ok,
                   "ouverture/get/fermeture OK" if open_ok and close_ok else "échec du handle", 112)
        except Exception as exc:
            if test_handle:
                NETWORK_SOCKETS.close(0, test_handle)
            report(12, "Gestion des handles TCP miniOS", False, str(exc), 112)

        failed = [code for code in results if code != 0]
        print("")
        print("RÉSUMÉ")
        print("-" * 96)
        if failed:
            print(f"{len(failed)} test(s) en échec : {', '.join(map(str, failed))}")
            print("Le test ICMP Internet (code 107) n'est jamais compté comme échec : un réseau peut filtrer ICMP tout en autorisant Internet.")
            return 1
        print(f"Tous les {len(results)} tests obligatoires ont réussi.")
        print("Le ping ICMP Internet est uniquement informatif.")
        return 0

    def cmd_test(self, args):
        print("[test] VM32 MEXE2")
        exe = MEXE(bytes([CPU.MOVI, 0]) + struct.pack(">I", 42) + bytes([CPU.PRINT, 0, CPU.HALT]))
        proc = VirtualProcess(0, "test", exe)
        proc.run()
        assert proc.exit_code == 0
        print("[test] MEXE OK")

        print("[test] JVM parser / runtime")
        # Hand-built minimal class with System.out.println("OK") is cumbersome;
        # instead we only verify helper behavior here.
        assert self.jvm.runtime.java_string("x").value == "x"
        print("[test] JVM runtime OK")
        print("[test] OK")

    # ------------------ dispatch / pipelines ------------------
    @staticmethod
    def _split_pipeline(line: str) -> Optional[List[str]]:
        """Découpe une ligne shell en stages séparés par un pipe ``|``.

        Le pipe doit être hors guillemets et être un opérateur simple ``|`` ;
        ``||`` n'est pas interprété comme un pipe. Les pipelines sont donc
        compatibles avec les chaînes MiniLang entre guillemets.
        """
        stages: List[str] = []
        start = 0
        quote: Optional[str] = None
        i = 0
        found = False
        while i < len(line):
            ch = line[i]
            if quote is not None:
                if ch == quote:
                    quote = None
                i += 1
                continue
            if ch in ("\"", "'"):
                quote = ch
                i += 1
                continue
            if ch == "|":
                prev = line[i - 1] if i > 0 else ""
                nxt = line[i + 1] if i + 1 < len(line) else ""
                if prev != "|" and nxt != "|":
                    # Un opérateur shell est normalement entouré d'espaces ;
                    # cette règle évite de casser la plupart des expressions
                    # MiniLang compactes comme ``1|2``.
                    if (not prev or prev.isspace()) and (not nxt or nxt.isspace()):
                        stage = line[start:i].strip()
                        if not stage:
                            raise ValueError("pipe sans commande à gauche")
                        stages.append(stage)
                        start = i + 1
                        found = True
            i += 1
        if not found:
            return None
        last = line[start:].strip()
        if not last:
            raise ValueError("pipe sans commande à droite")
        stages.append(last)
        return stages

    def _execute_pipeline(self, line: str):
        stages = self._split_pipeline(line)
        if not stages:
            return False
        stdin_data: Optional[str] = None
        for index, stage in enumerate(stages):
            last = index == len(stages) - 1
            if last:
                self.execute(stage, stdin_data=stdin_data, _pipeline_stage=True)
            else:
                buffer = io.StringIO()
                with contextlib.redirect_stdout(buffer):
                    self.execute(stage, stdin_data=stdin_data, _pipeline_stage=True)
                stdin_data = buffer.getvalue()
        return True

    def execute(self, line: str, stdin_data: Optional[str] = None, _pipeline_stage: bool = False):
        line = line.strip()
        if not line:
            return

        if not _pipeline_stage:
            try:
                if self._execute_pipeline(line):
                    return
            except ValueError as e:
                print(f"pipe: erreur de syntaxe: {e}")
                return

        # `minilang` reçoit le code source brut : ne pas passer par le tokenizer
        # du shell, sinon les guillemets de "print(\"Bonjour\")" seraient supprimés.
        raw_head = line.split(None, 1)
        if raw_head and raw_head[0].lower() == "minilang":
            self.history.append(line)
            self.history = self.history[-1000:]
            source = raw_head[1] if len(raw_head) > 1 else ""
            source = self._unwrap_minilang_command_source(source)
            try:
                self.cmd_minilang(source, stdin_data=stdin_data, quiet_result=_pipeline_stage)
            except Exception as e:
                print(f"minilang: erreur: {e}")
            return

        args = self.tokenize(line)
        if not args:
            return
        self.history.append(line)
        self.history = self.history[-1000:]
        cmd, rest = args[0].lower(), args[1:]
        handlers = {
            "help": self.cmd_help, "helpfile": self.cmd_helpfile, "minilang": self.cmd_minilang, "clear": self.cmd_clear, "echo": self.cmd_echo,
            "uname": self.cmd_uname, "version": self.cmd_version, "whoami": self.cmd_whoami,
            "hostname": self.cmd_hostname, "uptime": self.cmd_uptime, "date": self.cmd_date,
            "reboot": lambda a: print("reboot: simulation"),
            "shutdown": lambda a: setattr(self, "shutdown_requested", True),
            "exit": lambda a: setattr(self, "exit_requested", True),
            "ls": self.cmd_ls, "cd": self.cmd_cd, "pwd": self.cmd_pwd, "mkdir": self.cmd_mkdir,
            "rmdir": self.cmd_rmdir, "touch": self.cmd_touch, "cat": self.cmd_cat,
            "write": self.cmd_write, "edit": self.cmd_edit, "append": self.cmd_append, "rm": self.cmd_rm,
            "cp": self.cmd_cp, "mv": self.cmd_mv, "find": self.cmd_find, "tree": self.cmd_tree,
            "stat": self.cmd_stat, "head": lambda a: self.cmd_head_tail_wc("head", a),
            "tail": lambda a: self.cmd_head_tail_wc("tail", a), "wc": lambda a: self.cmd_head_tail_wc("wc", a),
            "run": self.cmd_run, "exec": self.cmd_exec, "wait": self.cmd_wait, "jobs": self.cmd_jobs, "java": self.cmd_java, "javac": self.cmd_javac, "ps": self.cmd_ps,
            "kill": self.cmd_kill, "debug": self.cmd_debug, "gdebug": self.cmd_gdebug, "newapp": self.cmd_newapp,
            "compile": self.cmd_compile, "build": self.cmd_build, "apps": self.cmd_apps,
            "install": self.cmd_install, "uninstall": self.cmd_uninstall,
            "mem": self.cmd_mem, "cpu": self.cmd_cpu, "regs": self.cmd_regs,
            "stack": self.cmd_stack, "heap": self.cmd_heap, "info": self.cmd_info,
            "disk": self.cmd_disk, "path": self.cmd_path, "which": self.cmd_which,
            "env": self.cmd_env, "set": self.cmd_set, "history": self.cmd_history,
            "import": self.cmd_import, "export": self.cmd_export, "download": self.cmd_download,
            "net": self.cmd_net, "ifconfig": self.cmd_ifconfig, "ipconfig": self.cmd_ipconfig,
            "ping": self.cmd_ping, "nslookup": self.cmd_nslookup, "netstat": self.cmd_netstat,
            "route": self.cmd_route, "networktest": self.cmd_networktest, "test": self.cmd_test,
        }
        if cmd in handlers:
            try:
                if cmd == "run":
                    handlers[cmd](rest, stdin_data=stdin_data)
                elif cmd == "minilang":
                    self.cmd_minilang(" ".join(rest), stdin_data=stdin_data, quiet_result=_pipeline_stage)
                else:
                    handlers[cmd](rest)
            except Exception as e:
                print(f"{cmd}: erreur: {e}")
            return
        if self._execute_path_command(args[0], rest, stdin_data=stdin_data):
            return
        print(f"{args[0]}: commande introuvable. Tapez 'help'.")

    def _stop_all_processes(self):
        with self.process_lock:
            procs = list(self.processes.values())
        for proc in procs:
            if proc.state in ("RUNNING", "READY", "SLEEPING", "WAITING_INPUT"):
                proc.request_stop()
        for proc in procs:
            if proc.thread and proc.thread.is_alive():
                proc.thread.join(timeout=0.25)

    def shell(self):
        self.boot()
        try:
            while not self.exit_requested and not self.shutdown_requested:
                try:
                    line = input(f"{VERSION}:{self.cwd}$ ")
                except (EOFError, KeyboardInterrupt):
                    print()
                    break
                self.execute(line)
        finally:
            self._stop_all_processes()
            self.disk.save()
            try:
                self.graphics.request_quit_mainloop()
            except Exception:
                pass
            print("miniOS arrêté.")

    def boot(self):
        print(r"""                                                                                                            
                                                                                                            
MMMMMMMM               MMMMMMMM  iiii                     iiii            OOOOOOOOO        SSSSSSSSSSSSSSS 
M:::::::M             M:::::::M i::::i                   i::::i         OO:::::::::OO    SS:::::::::::::::S
M::::::::M           M::::::::M  iiii                     iiii        OO:::::::::::::OO S:::::SSSSSS::::::S
M:::::::::M         M:::::::::M                                      O:::::::OOO:::::::OS:::::S     SSSSSSS
M::::::::::M       M::::::::::Miiiiiiinnnn  nnnnnnnn    iiiiiii      O::::::O   O::::::OS:::::S            
M:::::::::::M     M:::::::::::Mi:::::in:::nn::::::::nn  i:::::i      O:::::O     O:::::OS:::::S            
M:::::::M::::M   M::::M:::::::M i:::::in::::::::::::::nn  i::::i      O:::::O     O:::::O S::::SSSS         
M::::::M M::::M M::::M M::::::M i:::::inn:::::::::::::::n i::::i      O:::::O     O:::::O  SS::::::SSSSS    
M::::::M  M::::M::::M  M::::::M i:::::i  n:::::nnnn:::::n i::::i      O:::::O     O:::::O    SSS::::::::SS  
M::::::M   M:::::::M   M::::::M i:::::i  n::::n    n::::n i::::i      O:::::O     O:::::O       SSSSSS::::S 
M::::::M    M:::::M    M::::::M i:::::i  n::::n    n::::n i::::i      O:::::O     O:::::O            S:::::S
M::::::M     MMMMM     M::::::M i:::::i  n::::n    n::::n i::::i      O::::::O   O::::::O            S:::::S
M::::::M               M::::::Mi::::::i n::::n    n::::ni::::::i     O:::::::OOO:::::::OSSSSSSS     S:::::S
M::::::M               M::::::Mi::::::i n::::n    n::::ni::::::i      OO:::::::::::::OO S::::::SSSSSS:::::S
M::::::M               M::::::Mi::::::i n::::n    n::::ni::::::i        OO:::::::::OO   S:::::::::::::::SS 
MMMMMMMM               MMMMMMMMiiiiiiii nnnnnn    nnnnnniiiiiiii          OOOOOOOOO      SSSSSSSSSSSSSSS   
                                                                                                            
                                                                                                            
                                                                                                            
                                                                                                            
                                                                                                            
                                                                                                            
""")
        # Diagnostic de démarrage : utile pour voir immédiatement l'état
        # du miniOS sans répéter le contenu de `help`.
        print("  " + "-" * 78)
        print("  DIAGNOSTIC DU SYSTÈME")
        print("  " + "-" * 78)
        print(f"  Version       : {VERSION}")
        print(f"  Hôte          : {HOSTNAME}")
        print(f"  Plateforme    : {sys.platform}")
        print(f"  Python        : {sys.version_info.major}.{sys.version_info.minor}.{sys.version_info.micro}")
        print(f"  VM32 RAM      : {RAM_SIZE / (1024 * 1024):g} MiB / processus")
        print(f"  JVM           : javac intégré + JVM (max {JVM_MAX_STEPS:,} étapes)")
        print(f"  PATH          : {self.env.get('PATH', '/bin:/path:/apps')}")
        print(f"  Répertoire    : {self.cwd}")
        print(f"  Disque virtuel: {self.disk.storage_path}")
        print(f"  FS            : persistant JSON | {len(self.disk.dirs)} répertoires | {len(self.disk.files)} fichiers")
        try:
            disk_size = os.path.getsize(self.disk.storage_path)
            print(f"  Stockage réel : {disk_size:,} octets utilisés")
        except OSError:
            print("  Stockage réel : fichier disque pas encore créé")
        print(f"  Processus     : {len(self.processes)} actif(s)")
        gui_status = self.graphics.platform_backend_name()
        print(f"  Graphique     : {gui_status}")
        print("  Exécution     : run [-debug|-debg] <programme> [&] | run [-debug|-debg] -mini <fichier.mini> [&]")
        print("  Aide          : `help`, `help os`, `help minilang`")
        print("  GUI           : Win32/X11/Cocoa natif; UIKit via hôte iOS; aucun toolkit Python externe")
        print("  " + "-" * 78)


# ================================================================
# CLI entry point
# ================================================================

def print_usage():
    print(f"{VERSION}")
    print("Usage:")
    print("  python miniOS_0.5.py              -> shell")
    print("  python miniOS_0.5.py java X.class -> lance une classe")
    print("  python miniOS_0.5.py java X.jar   -> lance le Main-Class du JAR")


def main(argv: List[str]) -> int:
    os_ref = MiniOS()
    if not argv:
        # Le thread principal est réservé à la pompe d'événements du backend natif.
        # Le shell tourne dans un thread séparé et communique avec le moteur par queue.
        shell_thread = threading.Thread(target=os_ref.shell, name="miniOS-Shell", daemon=True)
        shell_thread.start()
        try:
            os_ref.graphics.run_mainloop()
        except Exception as exc:
            print(f"[GUI] backend natif indisponible ({exc}), shell texte uniquement")
        shell_thread.join()
        return 0
    if argv[0].lower() == "java":
        os_ref.cmd_java(argv[1:])
        return 0
    if argv[0].lower() == "javac":
        os_ref.cmd_javac(argv[1:])
        return 0
    if argv[0] in ("-h", "--help", "help"):
        print_usage(); return 0
    print_usage()
    return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
