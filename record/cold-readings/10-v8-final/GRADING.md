# Grading of cold reading 10 — «The Dancing Sand Theorem», version 8

Grepy Escribano, 6 October 2026, 13:1x. Report `REPORT_COLD_10.md`, md5 `9b71de2c596725229d0459f7c3e27522` (copy and checks in `delivered/`, md5 list `delivered_md5.txt`).

## Mark: HIGHEST

The reader answered the four closed questions, and nothing else. Every verdict is backed by code of its own, and each of its checks has a control that fires: the statement comparison, the word comparison of the pdf text, the character multisets of the body, and the replay of the edit script. It looked at all 50 pages. It sealed 11 predictions and published its one failure (P11), which is the finding. Its eight errors are listed, and none touches a verdict. It respected the folder and the order of `read_after/`. It gave its one replacement word for word, as the mission asked.

## Its verdicts, checked

- **(a) No mathematics changed, v7 → v8: ACCEPTED.** Its own diff equals the given diff, and the replay of `text_edits.py` on v7 gives the v8 md byte for byte. Its statement comparison of v1 … v8 agrees with mine, and with the list printed in §13.
- **(b) One clause false: ACCEPTED, and checked in the source.** The clause is in §1.0: «what was corrected, and what was left as it was, is listed with its source in the record kept with the project». Two checks:
  - `grep PD17|PD18|PD24|PD26` in `paper/CORRECTIONS_v5_to_v6.md` gives 0 hits.
  - These four items are in `REPORT_COLD_7.md` (l. 222–223 and others).

  So the record of corrections does not list everything that was left. **My error:** I wrote that clause to replace the draft's false «all were corrected», and checked only that some left items are listed, not that all are.
- **(c) Nothing broken; the pdf text differs only in the five places: ACCEPTED.** This agrees with my own look at the 50 pages and my word comparison.
- **(d) 9/9 PASS, 9/9 FAIL in control; both changes of the list right: ACCEPTED.**

## Its replacement R1, applied word for word (step 6)
- Script `paper/v8_edits/reader10_replacement.py` (md5 `654fd1cdd38681f77a0708d437961fbb`), asserted unique.
- Diff `paper/v8_edits/DIFF_R1_reader10.txt` (md5 `dd6fffeb256a7a53e6b777d7482c1ab5`): one hunk. The word diff shows exactly the reader's text and nothing else.
- Rebuild: `logs/v8_build_R1.log`, `VIGIA-FIN-OK`.
- Acceptance: 9/9 PASS (`logs/v8_acceptance_R1.log`); control 9/9 FAIL (`logs/v8_acceptance_control_R1.log`).
- Page bitmaps (50 dpi) against the v8 built before reading 10: only page 2 differs. Page 2 was looked at at 85 dpi, and it is right.

## Its slips of my account (in `CORRECTIONS_v7_to_v8.md`, not in the paper): accepted and corrected there
1. Page 13 begins inside §3.1 (the proof of Proposition 3.1(c)), not §2.3. The same slip is in the comment of the control of check 5 in `checks_v8/acceptance.py`; the code does not depend on it, and the tool is not changed.
2. The two words hyphenated across a page turn are on pp. 19–20 and pp. 42–43, not 18–19 and 41–42.
3. The list of numbers removed from Appendix A also misses 7 620 and 14. Both are still in §12.2.

Its style doubts 6.1–6.7 are not counted, as the mission says, and none is applied: the termination rule allows only the reader's replacements.

## Termination
By the arranque §3, step 6: the new words are the reader's. The record is static, so no new sentence about the version is written. **No new cold reading. Version 8 is final.**
- md `016fc36d0fcfcb807c85fe0307267893`
- pdf `f16c894a7135008b22a2b5ea9b3046ac` (50 pages)
- html `f7324734d8043df3e9449c9a69316283`
- The v8 before reading 10 is kept in `paper/historico/THE_DANCING_SAND_THEOREM_v8_antes_de_la_lectura_10.*`.

The sentence «none of these readings found a gap or an error in the mathematics» was to be rechecked after reader 10. It holds: reader 10 found none.
