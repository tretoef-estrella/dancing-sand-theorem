#!/usr/bin/env python3
"""normcmp.py — Grepy el lector frío del cubo 6, 2026-10-05.

Normalizing comparison of the hunks of a unified diff (mission §2 items 1-2).

For each hunk, OLD = context + '-' lines, NEW = context + '+' lines.
N1 (strict): delete every backtick and every whitespace character (spaces,
    tabs, newlines), then compare OLD and NEW as strings. Equal => the hunk
    changes only line breaks, spaces and backticks («LAYOUT-ONLY»).
For a hunk that is not LAYOUT-ONLY, print a word-level diff (tokens = the
    whitespace-separated words after deleting backticks), with 4 words of
    context, so that a human can judge every changed word.
Usage: normcmp.py DIFF [--mutate] ; --mutate is the control: it changes one
    character inside a '+' display of a hunk that should be LAYOUT-ONLY,
    and that hunk must then be reported as changed.
"""
import sys, re, difflib

def hunks(path):
    out, cur = [], None
    for line in open(path, encoding='utf-8'):
        line = line.rstrip('\n')
        if line.startswith('---') or line.startswith('+++'):
            continue
        if line.startswith('@@'):
            cur = {'head': line, 'old': [], 'new': []}
            out.append(cur)
            continue
        if cur is None:
            continue
        tag, body = line[:1], line[1:]
        if tag == ' ':
            cur['old'].append(body); cur['new'].append(body)
        elif tag == '-':
            cur['old'].append(body)
        elif tag == '+':
            cur['new'].append(body)
        elif line == '':
            cur['old'].append(''); cur['new'].append('')
    return out

def n1(lines):
    return re.sub(r'\s+', '', '\n'.join(lines).replace('`', ''))

def words(lines):
    return '\n'.join(lines).replace('`', '').split()

def main():
    path = sys.argv[1]
    mutate = '--mutate' in sys.argv
    hs = hunks(path)
    if mutate:
        # control: H11 (index 10) must become non-layout if one '+'-side char changes
        h = hs[10]
        for j, l in enumerate(h['new']):
            if '2f+1' in l and l.strip().startswith('`− Σ'):
                h['new'][j] = l.replace('2f+1', '2f+2', 1)
                print('CONTROL: mutated H11 new line:', h['new'][j][:80])
                break
    n_layout = 0
    for i, h in enumerate(hs, 1):
        a, b = n1(h['old']), n1(h['new'])
        if a == b:
            n_layout += 1
            print(f'H{i:02d} {h["head"]}  LAYOUT-ONLY')
            continue
        print(f'H{i:02d} {h["head"]}  CHANGED')
        wa, wb = words(h['old']), words(h['new'])
        sm = difflib.SequenceMatcher(None, wa, wb, autojunk=False)
        for op, a0, a1, b0, b1 in sm.get_opcodes():
            if op == 'equal':
                continue
            ctx_l = ' '.join(wa[max(0, a0 - 4):a0])
            ctx_r = ' '.join(wa[a1:a1 + 4])
            old = ' '.join(wa[a0:a1]); new = ' '.join(wb[b0:b1])
            if len(old) > 300: old = old[:300] + ' …'
            if len(new) > 300: new = new[:300] + ' …'
            # a word diff that is only whitespace-regrouping is shown as such
            same_n1 = re.sub(r'\s+', '', old) == re.sub(r'\s+', '', new)
            tag = ' [same chars, regrouped]' if same_n1 else ''
            print(f'    {op}{tag}: «…{ctx_l} [{old}] → [{new}] {ctx_r}…»')
    print(f'TOTAL hunks {len(hs)}, LAYOUT-ONLY {n_layout}')

main()
