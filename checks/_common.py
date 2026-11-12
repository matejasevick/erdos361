"""Shared helpers for the Erdos #361 source checks (no Lean needed)."""
import re


def strip_comments(s: str) -> str:
    """Remove Lean line comments (--) and nested block comments (/- ... -/, incl. docstrings)."""
    out, i, depth, n = [], 0, 0, len(s)
    while i < n:
        if s.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth > 0:
            if s.startswith('-/', i):
                depth -= 1; i += 2; continue
            i += 1; continue
        if s.startswith('--', i):
            j = s.find('\n', i); i = n if j < 0 else j; continue
        out.append(s[i]); i += 1
    if depth != 0:
        raise ValueError('unbalanced block comment')
    return ''.join(out)


def read(path: str) -> str:
    return open(path, encoding='utf-8').read().replace('\r\n', '\n').lstrip('﻿')


def norm(s: str) -> str:
    return re.sub(r'\s+', ' ', s).strip()
