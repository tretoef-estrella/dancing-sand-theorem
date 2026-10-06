p = 'REPORT_COLD_6.md'
s = open(p, encoding='utf-8').read()
old6 = s[s.index('- **P-R6.**'):s.index('- Checked and exact:')]
new6 = ('- **P-R6 (record of the author, not of the paper).** §13 lists the *statements* changed in version 3 (Lemma 7.9, Lemma 10.6(a), Lemma 10.10). '
        '`CORRECTIONS_v3_to_v4.md` §5 says that the rewording of Lemma 3.5 made in version 3 «is listed in §13 of version 4»; it is not — '
        'and rightly not: that rewording was in the *proof* of Lemma 3.5 («`C(3, r) = 1, 3, 3, 1`» → «`1, 3, 3, 1` (that is, `C(3, r)`)», '
        'REPORT_COLD_5 §3, read in Part 4). §13 is exact; `CORRECTIONS` §5 is wrong. In the same file, line 22: «(items 7, 8 and 11 below)» — §1 of `CORRECTIONS` has items 1–10 only.\n'
        '- **P-R7 (added in Part 4).** Appendix A, version 4 bullet: «… except the ranges of §12 that the fifth reader checked against the code». '
        'The new parenthesis of reader 4\'s Lemma 7.9 row («7 874 less the 240 with `i = 0`») was not checked by the fifth reader, who wrote that the 7 634 cells were «not checkable from the paper» (REPORT_COLD_5 §1.10, point 3): the author composed it, and it is wrong (item 8).\n')
s = s.replace(old6, new6)
s = s.replace('- «all corrected in this version 4» (§1.0) is graded in §6 of this report, against `REPORT_COLD_5.md`.',
              '- **P-R8 (added in Part 4).** §1.0: the fifth reader «found points of presentation and defects of typesetting, all corrected in this version 4». Against `REPORT_COLD_5.md` §4 (§6.1 of this report): of its 8 global and 28 specific defects, 33 are fixed, row 25 only partly, and rows 1 (the blank of p. 7) and 20 (the broken definition of `R_𝒮`) are not; two of its minor notes remain (a sentence opening with a formula; `b_0 ⊗ / b_1 n`). «All corrected» is not exact; «corrected, except …» would be.')
s = s.replace('(Checked against `gate_sections5to7.py` in §6 below.)',
              '(Confirmed in Part 4: `gate_sections5to7.py` lines 154–158 test only `u_0(D) = k + K + R^♯(D) − R^♯(I ∖ D)` for `D ≠ ∅`; the valuation loop runs for `i ≥ 1` only. Sealed S-18, hit.)')
open(p, 'w', encoding='utf-8').write(s)
print('P-R6' in s, 'P-R7' in s, 'P-R8' in s, 'Sealed S-18, hit' in s)
