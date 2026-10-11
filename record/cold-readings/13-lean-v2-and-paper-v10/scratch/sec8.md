## 8. Style doubts (not counted)

- Certificate p. 16–17: «the four `_all` statements» prints `_all` in italic (readable).
- Certificate p. 10: in §1.5 «the `𝔽_2`-rank `R`» prints `R` as an italic letter, `L1` as code.
- Certificate Table 6b, total row: «61285», «25559» without the thin space of the other totals' style in §7 («61 261»).
- Certificate §3.3: «Its lines for the sixteen theorems of version 1» — the log has individual cones for ten of them and the union of the sixteen (as the table); true, slightly loose.
- `acceptance.py`: the version-9 paragraph of the docstring still names the DOI `…23296708` for check 12, while its check 11 was edited to `CertCubo2.log`.
- `chkC53.py`: the comment says «n=3..6 sanity», the loop is `range(3,5)` (n = 3, 4); its check «R1» is `0 == aN(1)`, not a rank computation (the zero matrix is checked by «S3»).
- The mission says the author's `CheckC53.lean` ran in 189 s, peak 1.5 GB; `material/c53/CheckC53.log` says 156 s, peak 1.76 GB; my run 180 s, 1.58 GB. Not a document error.
- The paper's «the count of §10.8 … at `n = 1`»: §10.8 itself is written for `n ≥ 2`; the clause is true (it says what the first 68 pieces left out), but a reader may look in §10.8 for `n = 1` and not find it.

## 9. Sealed predictions, hits and failures

Sealed in `checks/SEALED.md` before measuring.
- P1 (tar `RequestProject/` = clone, 420 `.lean`): **hit**.
- P2 (416 unchanged, `SmallCases` the only new folder): **hit**.
- P3 (14 statements faithful; only renaming `L1_one`): **hit**.
- P4 (no forbidden construct): **hit**.
- P5 (`CheckC53` exit 0, ~3 min, standard axioms): **hit** (180 s, 1.58 GB).
- P6 (paper diff only header, §12.3, Appendix A, [LC26]; no number of a result changed): **hit**.
- P7 (at least one slip in the new text, prior 50 %): **hit**, but not where I expected: no count or number was wrong; the slips are scope, description and order of sentences, and two names printed as formulas.
- P8 (my count reproduces 420 / 61 285 / 3 470): **hit**, exactly, with `wc -l` lines and comment-stripped declarations.
- P9 (pages 1 and 48–52 differ): **hit**.
- P10 (12/12 pass, 12/12 controls fail): **hit**.
- P11 (`msgC53.txt` = instruction + piece byte for byte): **hit** (plus a separator line, which the certificate's «preceded by a one-paragraph instruction» covers).

## 10. My errors

- I ran one tiny Python (the `msgC53.txt` comparison) and the report-editing snippets outside `vigia.sh` and without `PYTHONDONTWRITEBYTECODE=1` (stdin scripts write no bytecode). Logged in the diary at the time; the comparison was redone inside the checks of (d).
- I started a word with `=` in zsh (`echo ======`): harmless failure, rerun.
- My first run of `grep420` used an unquoted `--include=*.lean`, which zsh tried to glob: all counts came out 0 with «no matches found». I saw it and reran quoted; the first log was overwritten by the good run.
- My first version of `remate_cert.py` cut the Lean block of §1.5 one line short and reported «not byte-identical»; fixed the slice (the block is identical).
- In §2 of this report I first wrote «Six hunks» for the paper's diff; corrected to five at once.
- A `cd` in one command persisted into the next tool call once; no file was written outside this folder.

## 11. What I did not check

- [GMMY24] is not in the material: that Gao et al. state their Theorem 4.1 for `n ≥ 2`, and whether their Theorem 4.1 alone or 4.1 with 4.2 is what `G1` states, I did not check.
- The concept DOI `10.5281/zenodo.23296707` (not in any other file of the material; I did not query Zenodo).
- Aristotle's register (527 → 541) and the audit log `INFORME_ARISTOTLE_CUBO_v1.md` (not in the material).
- The send time of C53 (13:44 CEST); that `SmallCases` «had never been compiled on this machine»; the order «Before that» of the md5 comparison.
- That each of the 68 earlier folders is identical to the tarball of the piece that created it, and that the 68 piece files in the tarball are the ones sent (I have only tarball (69)).
- That versions 9 and 10 keep the numbering of version 8 (I do not have version 8; 9 and 10 agree).
- I did not run `make_tables_v2.py` (it needs 69 brute-force logs; the material has one); I recomputed its inputs and outputs instead.
- I did not rebuild any module (`lake build` is forbidden here); I re-elaborated the three source files of C53 with `lake env lean`.
- I did not re-read the unchanged parts of the paper or the certificate beyond searching them for sentences the changes could falsify.
- The rendering of my C-9 fix: the certificate's builder is not in the material, so I could not rebuild the pdf to see it.
