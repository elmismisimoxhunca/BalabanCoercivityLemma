#!/usr/bin/env python3
"""Validate complete Lean #print axioms messages, including wrapped lists.

Only propext, Classical.choice, and Quot.sound are permitted. Output is one
complete, whitespace-normalized record per line, suitable for exact comparison.
Unrelated diagnostics are left to the compiler exit/error checks in REPRODUCE.sh.
"""
import argparse
from pathlib import Path
import re
import sys

ALLOWED = ('propext', 'Classical.choice', 'Quot.sound')
HEADER = re.compile(r"^'(?P<name>[^\n]+)' (?P<kind>depends on axioms:|does not depend on any axioms)(?P<tail>.*)$")
MARKERS = ('depends on axioms', 'does not depend on any axioms')


def normalize_log(text):
    lines = text.splitlines()
    records = []
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        i += 1
        match = HEADER.fullmatch(line)
        if match is None:
            if any(marker in line for marker in MARKERS):
                raise ValueError(f'malformed axiom message at line {i}')
            continue
        name = match['name']
        tail = match['tail'].strip()
        if match['kind'] == 'does not depend on any axioms':
            if tail:
                raise ValueError(f'unexpected trailing content for {name}')
            records.append(f"'{name}' does not depend on any axioms")
            continue
        while ']' not in tail:
            if i >= len(lines) or any(marker in lines[i] for marker in MARKERS):
                raise ValueError(f'truncated axiom list for {name}')
            tail += ' ' + lines[i].strip()
            i += 1
        body = re.fullmatch(r'\[([^\[\]]*)\]', tail.strip())
        if body is None:
            raise ValueError(f'malformed axiom list for {name}')
        contents = body[1].strip()
        axioms = [a.strip() for a in contents.split(',')] if contents else []
        if any(not a for a in axioms) or len(axioms) != len(set(axioms)):
            raise ValueError(f'empty or duplicate axiom entry for {name}')
        unexpected = set(axioms) - set(ALLOWED)
        if unexpected:
            raise ValueError(f'forbidden axioms for {name}: {", ".join(sorted(unexpected))}')
        ordered = [a for a in ALLOWED if a in axioms]
        if ordered:
            records.append(f"'{name}' depends on axioms: [{', '.join(ordered)}]")
        else:
            records.append(f"'{name}' does not depend on any axioms")
    if not records:
        raise ValueError('no complete axiom records found')
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('raw', type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    try:
        records = normalize_log(args.raw.read_text(encoding='utf-8'))
    except (OSError, UnicodeError, ValueError) as error:
        args.output.unlink(missing_ok=True)
        print(f'axiom audit failed: {error}', file=sys.stderr)
        return 1
    args.output.write_text('\n'.join(records) + '\n', encoding='utf-8')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
