# Grading of cold reader 9 (the changes of version 7)

Grepy Muchas Pilas, chief auditor, 6 October 2026.

- Report: `delivered/REPORT_COLD_9.md`, md5 `859424acff771a6f926f0ed72eaff456` (the last line of its `logs/DIARY.md`, checked).
- Delivery: 155 files copied into `delivered/`; the md5 of every file is in `delivered_md5.txt`. Origin and copy are identical (the md5 of the md5 list is `9bd76c74…` on both sides).

## Mark: HIGHEST

## Verdict of the reader: «HOLDS WITH GAPS»; ready after two corrections
- **Mathematics:** no numbered statement changed. The one proof step touched (Proposition 9.6 (H)) is right, and the reader re-derived both of its cases (§2.6).
- **Pdf:** the changed pages are exactly the author's list. Nothing on them is broken, and md = pdf on every changed passage. The acceptance list passes 9 of 9 and its controls fire 9 of 9.
- **One ERROR, of the record, and it is mine.** Appendix A, the «Version 7» entry, says «No mathematical statement changed, and no number». Version 7 changed printed numbers (the dates of the work; the reader-3 row of §12.2).
  - Checked: the sentence is at md l. 1152.
  - The same sentence is at `paper/CORRECTIONS_v6_to_v7.md` l. 13.
  - The same note says «The other 39 pages are unchanged» (l. 35). It is 38, because 52 − 14 = 38.

## Why the highest mark
1. **Every claim is a derivation, not a stamp.** It gives the arithmetic of the houses with and without `k = 0`, the two runs of reader 3 from the logs, and an inference marked as an inference (682, 1 134).
2. **It re-ran the gate.** It ran `gate_strict_cut.py 6 4` under the watchdog and reproduced every number of the two rows.
3. **It found the one sentence nobody had read:** the newest entry of the record, written by the scribe.
4. **It audited the controls of the acceptance list one by one** and showed where their isolation is imperfect (style doubt 7.3: the damage of check 5 also hits check 2).
5. **It wrote replacement texts word for word.**
6. **It sealed 7 predictions before measuring, and they gave 7 hits.** It published 6 errors of its own, all small.

## What its finding shows (it goes beyond this version)
Since version 4, every cold reading has found at least one false sentence in the paper's record of its own versions:
- reading 6: a false number and a false sentence;
- reading 7: §13;
- reading 8: §13 and the dates;
- reading 9: the entry of version 7.

The cause is structural; it is not in the pdf. See `notes/DIAGNOSTICO_EL_BUCLE_DE_LAS_VERSIONES_v1.md`.

## Its two corrections
Both concern the «Version 7» entry. In the plan for version 8 (`ARRANQUE_GREPY_ESCRIBANO_v1.md`) that entry disappears, together with the whole diary of versions, so the two corrections become moot. If Rafa does not approve the static record, they are applied word for word.
