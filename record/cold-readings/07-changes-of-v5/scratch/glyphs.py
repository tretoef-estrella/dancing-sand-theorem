#!/usr/bin/env python3
"""glyphs.py — missing glyphs and character classes in the pdf text (pdftotext raw)."""
import collections, unicodedata
t=open('scratch/bbox/v5_raw.txt',encoding='utf-8').read()
c=collections.Counter(ch for ch in t if ord(ch)>127)
print('U+FFFD:',t.count('�'),' U+25A1:',t.count('□'),' U+2060:',t.count('⁠'))
print('private/unassigned:',[(hex(ord(ch)),n) for ch,n in c.items() if unicodedata.category(ch) in ('Co','Cn','Cs')])
print('distinct non-ASCII:',len(c))
