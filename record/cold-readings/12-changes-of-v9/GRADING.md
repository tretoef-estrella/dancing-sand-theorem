# Grading of cold reading 11 — «Grepy Cotejo», the changes of version 9 and the certificate's corrections

Grepy Escribano, 11 October 2026. Report `REPORT_COLD_11.md`, md5 `fc1066fd1e37886dba1a5bb5fb871357` (the md5 is the last line of its diary). Delivery copied with md5 in `reports/LECTOR_FRIO_11/delivered/` (`MANIFEST_md5_delivered.txt`, 54 files: the report, `ESTADO.md`, `checks/`, `logs/`, and its code and the two files «with replacements» from `scratch/`; page images left out).

## Verdict: HIGHEST MARK

The reading is closed, complete and exact. It answers the five questions of the mission in its first lines, gives every finding with a file and a line, says how it counted, publishes its own errors, and lists what it did not check. Every one of its findings that I checked is correct. None touches mathematics: no numbered statement, proof or number of a result changed from version 8 to version 9.

## The findings, one by one

| Finding | Correct? | How I checked | Applied |
|---|---|---|---|
| E-B2 (§1.0: the Lean name of each row is in §12.3; Theorems O and F have no name there) | **Correct** | §12.3 names no Lean theorem for Theorems 6.2 and 7.8; the §1.0 table has the row «Theorems O and F» (v9 line 25) | word for word |
| E-B3 (§1.3: «each edge is the image of two edges» is false at `n = 1`) | **Correct** | `Q_1` has one edge and the folded cube one vertex with one loop; the paper includes `n = 1` | word for word |
| E-B9 (415 files and 60 940 lines; the project has 416 and 60 964) | **Correct** | my count: 416 `.lean` files in `RequestProject/` (Main.lean included), 60 964 lines (`find … \| xargs cat \| wc -l`) | word for word |
| E-B10 (the «one sentence» was the paper's own §1.3, not only the certificate's) | **Correct** | F-ERR-4 of reading LEAN_1 quotes version 8 §1.3 | word for word |
| E-B14 (§13: «every result above» includes the measured items) | **Correct** | v9 line 1149 is the item «Measured, not proved» just above | word for word |
| E-C1 (certificate §6: the row of `Main.lean` is written into the script, not read from data) | **Correct** | `make_tables.py` line 160 | word for word |
| P-B5 (no piece number occurs in v9) | **Correct** | grep | word for word |
| P-B11 (the pointer should be «§1.3 and §2») | **Correct** | certificate §0, §1.3 | word for word |
| P-B16 (the DOI placeholder is printed) | **Correct** | declared in `CORRECTIONS_v8_to_v9.md`; filled with the Zenodo DOI reserved for the Lean record, and check 12 rewritten to require the DOI | word for word, with the DOI |
| P-C1 (certificate §1.3 row headed «Paper (v8)» now quotes v9) | **Correct** | certificate line 109 | word for word |
| P-D1 (orphaned caption of Table 6b at the foot of p20) | **Correct** | to be seen on the rebuilt pdf | caption kept with its table |
| §2 item 6 «(§3.2)» → «(§3.3)» (seen in passing) | **Correct** | the seven side modules are listed in §3.3 | word for word |
| «14 hunks» in `CORRECTIONS_v8_to_v9.md` (9 hunks; 14 is the number of edits) | **Correct** | internal record; corrected there | yes |

**Style doubts S1–S10:** not counted, as the mission asks. S8 (the header comment of `make_tables.py` still says «so that no number is copied by hand») is corrected, because it is the same kind of sentence as E-C1.

**The nine final check logs missing from its material** (`checkC30`, `C34`, `C35`, `C50`, `C50b`, `C50c`, `C50h`, `C51`, `C52`): **my error in the mission**, not the reader's. They exist in `logs/` (checked by name); the manifest of the material was built from a list that missed them. The count 885 stays as the first reader established it on all 68 logs.

## Decision

No further reading (the termination rule of reading 10 applies: closed list of changed places, replacements printed word for word, applied word for word). The replacements are applied by `paper/v9_edits/reader11_replacements.py` (paper) and `lean/CERTIFICADO/cold_fixes_COTEJO.py` (certificate); the paper is rebuilt with the frozen builder, the acceptance list is run with its controls, and the changed pages are looked at.

The version label stays «version 9»: version 9 was never public (the public version is 8), so a «version 10» would skip a number. The pre-reading text is kept in `paper/historico/` and `lean/CERTIFICADO/historico/`.
