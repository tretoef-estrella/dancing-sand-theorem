#!/usr/bin/env python3
"""normcmp.py — Grepy cold reader 7. Word-level comparison of v4 and v5 md, hunk by hunk.

How it works:
 1. Split both md files into lines; difflib.SequenceMatcher on lines (autojunk off) gives the
    changed blocks (the same blocks as diff -u, checked against the hunk count).
 2. Each side of a block is joined into one string and NORMALIZED (typographic only):
    ℤ→Z, ℚ→Q, 𝔽→F (the number-set change), ’→', ‘→', ⋯→…, no-break / thin spaces → space,
    ** (bold) removed, whitespace collapsed.
 3. If the normalized strings are equal, the block is TYPO-ONLY. Otherwise both sides are
    tokenized (code spans `...` kept as single tokens; words; punctuation) and a token-level
    SequenceMatcher prints each replaced/inserted/deleted token run with 4 tokens of context.
 4. Output: one record per block, with v4/v5 line numbers, class TYPO-ONLY or CONTENT-DIFF.
 Usage: normcmp.py OLD NEW [--all]
"""
import sys, re, difflib
old = open(sys.argv[1], encoding='utf-8').read().split('\n')
new = open(sys.argv[2], encoding='utf-8').read().split('\n')
SHOWALL = '--all' in sys.argv

TR = {'ℤ':'Z','ℚ':'Q','𝔽':'F','’':"'",'‘':"'",'⋯':'…',' ':' ',' ':' ',' ':' ',' ':' ',' ':' ','⁠':''}
def norm(s):
    for a,b in TR.items(): s = s.replace(a,b)
    s = s.replace('**','')
    s = re.sub(r'\s+',' ',s).strip()
    return s
TOK = re.compile(r'`[^`]*`|\w+|[^\w\s]')
def toks(s): return TOK.findall(s)

sm = difflib.SequenceMatcher(None, old, new, autojunk=False)
nblocks = 0; ntypo = 0; ncontent = 0
for tag, i1, i2, j1, j2 in sm.get_opcodes():
    if tag == 'equal': continue
    nblocks += 1
    a = '\n'.join(old[i1:i2]); b = '\n'.join(new[j1:j2])
    na, nb = norm(a), norm(b)
    if na == nb:
        ntypo += 1
        print(f'### block {nblocks}: v4 {i1+1}-{i2} / v5 {j1+1}-{j2}: TYPO-ONLY')
        if not SHOWALL: continue
    else:
        ncontent += 1
        print(f'### block {nblocks}: v4 {i1+1}-{i2} / v5 {j1+1}-{j2}: CONTENT-DIFF')
    ta, tb = toks(na), toks(nb)
    s2 = difflib.SequenceMatcher(None, ta, tb, autojunk=False)
    for t, a1, a2, b1, b2 in s2.get_opcodes():
        if t == 'equal': continue
        ctxl = ' '.join(ta[max(0,a1-4):a1]); ctxr = ' '.join(ta[a2:a2+4])
        print(f'  [{t}] …{ctxl} ‹{" ".join(ta[a1:a2])}› → ‹{" ".join(tb[b1:b2])}› {ctxr}…')
print(f'TOTAL blocks={nblocks} typo_only={ntypo} content_diff={ncontent}')
