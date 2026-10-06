p = 'REPORT_COLD_6.md'
s = open(p, encoding='utf-8').read()
old = s[s.index('- Do the changes of the text hold as written: (pending)'):s.index('## 1. The changes of the text')]
new = '''- **Do the changes of the text hold as written: HOLDS WITH GAPS.** The mathematics of every change holds: no symbol, number, quantifier or hypothesis of any numbered statement changed (item 1; my own normalizing comparison, §2), and the new sentences on strictness (item 3), on the cleanliness of the moves (item 4) and on «the rounding never acts» (item 6) are right. No gap and no error in the mathematics; the Stop rule was not triggered. What does not hold as written is the record: one row of §12.2 is arithmetically false («the 7 634 cells with `i ≥ 1` … (7 874 less the 240 with `i = 0`)»: in that range 254 cells have `i = 0` and 7 620 have `i ≥ 1`; item 8, ERROR of the record), and Appendix A still calls version 3 «(this text)» (item 7); further sentences of §1.0, §13, Appendix A and §12 are inexact, and «Why dance» drops a sign (items 5, 7, 8).
- **Is the pdf perfect: NO** — **32 global defects** (GD1–GD32, `checks/PDF_DEFECTS.md`) and **64 page-specific ones** (`checks/PAGES.md`). The gravest: barred and hatted letters are unreadable (`X̄(λ, i) ≅ 2X(λ, i)` reads «X ≅ 2X», `N̄ := N ⊗ F_2` reads «N := N ⊗ F_2», `d̂_r` reads «đ_r»); **no page numbers**; stray bold words in statements; the n-ary `⊕` of the new display of Proposition 10.3 set as the binary sign; «=:» split; matrices written as lists `[[X, 0], …]`; breaks inside short bracket groups and one formula split across a page; visibly loose lines (word spaces up to twice the median).
- **Is version 4 ready for publication: AFTER CORRECTIONS** — of the record (two false sentences, several inexact ones) and of the typesetting; no correction of the mathematics is needed.

'''
s = s.replace(old, new)
s = s.replace('9. **Short pages:**', '9. **Count.** 64 page-specific defects: one per lettered item of `checks/PAGES.md` that is not just an instance of a global defect (each loose line counted once).\n10. **Short pages:**')
open(p, 'w', encoding='utf-8').write(s)
print('ok', 'HOLDS WITH GAPS' in s, '64 page-specific defects' in s)
