# DIARY — Grepy el lector frío del cubo 6

2026-10-05 21:21:39 — START. Read MISSION.md whole. Created REPORT_COLD_6.md with empty §6 headings (before reading anything else).
2026-10-05 21:21:39 — BEFORE run manifest_md5: estimate <20 MB, <5 s (md5 -r over ~60 files).
2026-10-05 21:21:40 — AFTER run manifest_md5: see logs/manifest_md5.log
2026-10-05 21:21:44 — Manifest: 73 OK, 0 FAIL. PART 1 BEGIN: reading headings of v4 md.
2026-10-05 21:22:02 — Read v4 §1.0–§1.8, §11–§13, Ack, App. A, References. Next: CORRECTIONS_v3_to_v4.md and first pass over diff.
2026-10-05 21:22:10 — Read CORRECTIONS_v3_to_v4.md. Noted: its §5 says rewording of Lemma 3.5 is listed in v4 §13 — §13 line 1112 does not list it (to verify). Now: diff hunk list.
2026-10-05 21:22:18 — BEFORE run regen_diff: estimate <30 MB, <2 s.
2026-10-05 21:22:18 — AFTER run regen_diff.
2026-10-05 21:24:15 — PART 1 first pass over diff done: 29 hunks catalogued in REPORT §1. Statements touched: H5 (Cor 1.6 key), H9 (Lemma 2.1), H17 (Lemma 9.7). Notes for item 7: App. A still says «Version 3 (this text)»; CORRECTIONS §5 says Lemma 3.5 rewording listed in v4 §13 — it is not; CORRECTIONS cites «items 7, 8 and 11» but has items 1–10.
2026-10-05 21:24:49 — PART 2 BEGIN. Sealed S-2. Writing scratch/normcmp.py.
2026-10-05 21:24:53 — BEFORE runs normcmp (main + control): estimate <40 MB, <3 s each.
2026-10-05 21:24:54 — AFTER runs normcmp, normcmp_control.
2026-10-05 21:27:57 — Items 3,4,5 analysed (notes to be written). Now item 6: GMMY source, Proposition 2.5.
2026-10-05 21:30:33 — Wrote verdicts items 3,4,5,6 to scratch/items_3to6.md (to be merged into REPORT §1 now).
2026-10-05 21:31:23 — Item 8: sealed S-3..S-7. Writing scratch/cells.py (own code, exact Fractions).
2026-10-05 21:31:27 — BEFORE run cells: estimate <80 MB, <90 s (≈7.9k + 10.5k cells + 16k houses, PAVA ≤ 128 entries, Fractions).
2026-10-05 21:31:31 — AFTER run cells.
2026-10-05 21:32:23 — S-3..S-7 all HIT. FINDING: §12.2 reader-4 Lemma 7.9 row '7 634 cells with i ≥ 1 (7 874 less the 240 with i = 0)' false: 254 cells have i = 0; 240 = i=0 & I≠∅; i≥1 = 7 620. Now item 9 references.
2026-10-05 21:32:37 — MY ERROR E-1: used echo ===== in zsh (word starting with =), command failed partway; no file written. Redone with quoted separators.
2026-10-05 21:33:01 — BEFORE runs refs (main+control): <30 MB, <2 s.
2026-10-05 21:33:01 — AFTER runs refs.
2026-10-05 21:34:41 — PART 2 DONE: items 1-9 and REPORT §2 written (item 7 false sentence App. A; item 8 ERROR 7 634 row). Next PART 3: pdf.
2026-10-05 21:34:50 — PART 3 BEGIN. BEFORE run render90: pdftoppm -r 90, 49 pages; estimate <400 MB, <120 s.
2026-10-05 21:34:57 — AFTER run render90.
2026-10-05 21:35:19 — BEFORE run crop p1 abstract @200dpi: <150 MB, <5 s.
2026-10-05 21:35:42 — BEFORE run pdftotext full (raw + layout): <80 MB, <10 s.
2026-10-05 21:35:59 — MY ERROR E-2: ran a small python count of apostrophes (scratch/v4_raw.txt) OUTSIDE vigia.sh. Result: 43 ASCII ' , 0 U+2019. Re-run under vigia to have a log:
2026-10-05 21:36:00 — apos re-run under vigia: logs/apos.log.
2026-10-05 21:37:06 — PAGES p1-p2 written; PDF_DEFECTS.md started (GD1-GD6).
2026-10-05 21:41:49 — PAGES p1-p9 done.
2026-10-05 22:02:35 — PAGES p1-p49 ALL LOOKED AT and written (checks/PAGES.md). PDF_DEFECTS GD1-GD30. Next: systematic checks (fill S-8, margins, gaps, structure, widows, fonts, md vs pdf, xrefs, hyphenation).
2026-10-05 22:02:58 — REPORT §3 summary written. Now reading material/tools scripts before using them.
2026-10-05 22:03:41 — Sealed S-9..S-13. BEFORE runs of the 7 tools: each <60 MB, <20 s.
2026-10-05 22:03:43 — AFTER runs of the 7 tools.
2026-10-05 22:05:09 — BEFORE run pdfcheck: <60 MB, <15 s.
2026-10-05 22:05:09 — AFTER run pdfcheck.
2026-10-05 22:05:58 — pdfcheck v2 (next line skips sub/superscript bands; prints fill of all pages). BEFORE run: <60 MB, <15 s.
2026-10-05 22:05:58 — AFTER run pdfcheck2.
2026-10-05 22:06:21 — MY ERROR E-3: in PAGES.md I estimated blank feet on p5 (12%), p11 (18%), p15 (18%) from the downscaled 90-dpi view; measured fill (logs/pdfcheck2.log) is 99%, 97%, 95%. Corrected in PAGES.md. MY ERROR E-4: an empty 'python3 - <<EOF' (no-op) was run outside vigia.sh before the perl edits; no computation, logged for honesty.
2026-10-05 22:06:43 — BEFORE run pdffonts: <50 MB, <10 s.
2026-10-05 22:07:02 — BEFORE run pdffonts per page (49 calls): <50 MB, <30 s.
2026-10-05 22:07:36 — Fonts: 114 embedded (112 Type 3 + 2 Menlo CID TrueType), all subset + ToUnicode; STIXGeneral fallback for ∎ (pages=QED pages) and bold ∇ p11. No folios (GD32). Next: loose-line baseline, consecutive displays across pages, own statement md-vs-pdf, own xrefs, code names.
2026-10-05 22:07:57 — BEFORE run lines2: <60 MB, <15 s.
2026-10-05 22:07:57 — AFTER run lines2.
2026-10-05 22:08:43 — BEFORE runs stmt_cmp (main + control): <60 MB, <20 s each.
2026-10-05 22:08:43 — AFTER runs stmt_cmp.
2026-10-05 22:09:30 — stmt_cmp v2 (monotonic label search; Main Theorem anchored). BEFORE runs: <60 MB, <20 s.
2026-10-05 22:10:49 — BEFORE runs xref2 (main + control): <40 MB, <10 s.
2026-10-05 22:12:38 — PART 3 DONE: REPORT §3, §4, §5 written. Next PART 4: material/read_after (mission §5).
2026-10-05 22:12:53 — PART 4 BEGIN. Sealed S-16..S-20. Opening material/read_after/cold_reading_5/REPORT_COLD_5.md.
2026-10-05 22:13:14 — Read REPORT_COLD_5 §0–§3. Now gate_cold5_full.log.
2026-10-05 22:14:10 — Read REPORT_COLD_5 §4–§6. Reading PAGES.md and gate_cold5.py of reader 5.
2026-10-05 22:14:58 — S-16..S-20 resolved except S-16 (to record). Now builder: md2html_v4.py header.
2026-10-05 22:15:08 — Read md2html_v4.py rules. Reading phtml.py.
2026-10-05 22:15:56 — BEFORE run phtml_probe (author's phtml.py on 4 test strings): <40 MB, <5 s.
2026-10-05 22:16:12 — phtml_probe confirms mechanisms of GD19, GD25, GD28, GD9/GD21. Reading build_v4.sh, chrome_pdf.sh, pdf_meta.py.
2026-10-05 22:16:24 — Read build_v4.sh, chrome_pdf.sh (--no-pdf-header-footer = no folios), pdf_meta.py. Reading author_checks.
2026-10-05 22:16:49 — Sealed S-21. BEFORE run author fill.py: <80 MB, <10 s.
2026-10-05 22:17:12 — S-16, S-21 recorded. Writing REPORT §6.
2026-10-05 22:19:45 — PART 4 DONE: REPORT §6 written; items reordered; item 7 P-R6..P-R8, item 8 heading. Next PART 5: §0, §7, §8, §9, §10, md5.
2026-10-05 22:20:21 — REPORT §7, §8, §9 written. Now §0 first lines.
2026-10-05 22:21:24 — PART 5: report §0–§9 final. BEFORE run manifest_md5_end: <20 MB, <5 s.
2026-10-05 22:21:24 — AFTER run manifest_md5_end.
2026-10-05 22:21:38 — BEFORE run md5_written: md5 of every file I wrote (except REPORT_COLD_6.md, logs/DIARY.md, logs/md5_written.log, the manifest itself) into checks/MD5_COLD6.txt; <30 MB, <10 s.
2026-10-05 22:21:38 — AFTER run md5_written.
2026-10-05 22:21:46 — BEFORE run md5_manifest: <10 MB, <2 s.
2026-10-05 22:21:46 — AFTER run md5_manifest.
2026-10-05 22:22:10 — REPORT §10 written. BEFORE run md5_report: <5 MB, <1 s.
2026-10-05 22:22:10 — AFTER run md5_report.
REPORT_COLD_6.md listo — md5 98fa152e4c2e33d901e171d6b98f1d94
