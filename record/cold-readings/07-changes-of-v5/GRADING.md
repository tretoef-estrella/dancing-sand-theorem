# Grading of cold reader 7 — «The Dancing Sand Theorem», the changes of version 5 and its pdf

Grepy Muchas Pilas, chief auditor, 6 October 2026.

Report: `REPORT_COLD_7.md`, md5 `e20806b86ed82eabdc8a055ac5ed07c6` (the md5 on the last line of its `logs/DIARY.md`; checked). Delivery copied with md5 into `delivered/` (266 files, identical to the originals; list `delivered_md5.txt`).

## Mark: HIGHEST MARK

The report reads every changed passage against the source, says what it did not read, seals 20 predictions before measuring and prints the 6 failures beside the 14 hits, and gives every pdf defect its page and, in §6.3, the builder rule that caused it. Its own six errors are listed (§8), including ten small inspections run outside the watchdog (E4). That breaks a rule, and the report says so itself.

## Its verdicts, checked

### 1. Mathematics: «no statement changed» — ACCEPTED.
- It compares the two versions with a normalizing script and a control that fires.
- It reads all 67 blocks whose content changed.

### 2. The record — ACCEPTED, all four points.
- **R1 is a real error of mine.** §13 says «No statement of a theorem changed in versions 2, 3, 4 or 5», but version 2 added «strict» to the (Cut) of Theorem 7.8. The paper itself says so in Appendix A.
- **R2:** four descriptions of counts changed, not one.
- **R3:** «audited» should be «made by the auditor».
- **The «left as they are» list is incomplete:** seven kinds are missing.

### 3. The pdf — ACCEPTED: not perfect, 28 kinds, 172 instances.

I re-ran three of its checks with its own scripts, under the watchdog (`logs/r7_rerun.log`, VIGIA-FIN-OK, 17 MB, 1 s; outputs in `rerun/`):
- **PD1 confirmed.** The pdf text of p. 26 reads «1. The walk», then «(Λ).» and «(Cut).» with no number, then «4.», «5.», «6.». The md has «2.» and «3.».
- **Fill confirmed.** Pages under 90 %: 1, 5, **13 (89.0 %), 18 (86.1 %), 44 (83.8 %)**, and 51 (the last page).
- **Loose lines confirmed.** 1015 justified lines, median stretched space 3.48 pt, 57 lines at ≥ 1.6× the median.

### 4. Its diagnosis of my checks — ACCEPTED. These are errors of mine.
- **`allchecks.sh` cuts `fill.py` with `| head -12`.** So I never saw pages 13 to 51, and CORRECTIONS §5 says «p1 and p5» only. A check whose output is cut is not a check.
- **`loose2.py` is broken by rule (59).** The absolutely positioned ∎ makes gaps of 230–386 pt, so its counts mean nothing.
- **`lines2.py` skips list lines and formula words.** «2 lines at twice the median» is what that one tool shows, not what the page shows.
- **PD1 was made by my own rule (52)** of version 5. The rule removes the marker of a labelled item, and it also acted in an ordered list.

### 5. «Ready for publication? AFTER CORRECTIONS» — ACCEPTED.

## What this says about the method
- Readings 6 and 7 were asked to read the pdf as a typesetter would, with no fixed standard. With such a mandate a 51-page pdf always yields dozens of findings.
- Each version of my home-made imitation of TeX inside Chrome fixed the named instances and created new kinds.
- The measure moved between readings: loose lines were 2 by one tool and 55 by another.

The strategy to stop this is in `notes/ESTRATEGIA_PDF_A_LA_PRIMERA_v1.md`.

— Grepy Muchas Pilas
