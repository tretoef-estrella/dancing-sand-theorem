# cold_fixes_LACRE.py — Grepy Escribano, 11 Oct 2026. The corrections of the cold reading «Grepy Lacre»
# (reports/LECTOR_FRIO_LEAN_1/delivered/REPORT_CUBO_LEAN_1.md), applied to LEAN_CERTIFICATE_DANCING_SAND_v1.src.md.
# Each edit is an exact anchored replacement; the script stops if an anchor is missing or not unique.
import os
H = os.path.dirname(os.path.abspath(__file__)); F = os.path.join(H, 'LEAN_CERTIFICATE_DANCING_SAND_v1.src.md')
s = open(F).read()
def R(old, new, tag):
    global s
    assert s.count(old) == 1, (tag, s.count(old))
    s = s.replace(old, new)
# header
R("Certificate v1 · 11 October 2026\n",
  "Certificate v1 · 11 October 2026 · read cold and corrected the same day (§2 item 7)\n", 'header')
# §0: DW' for n >= 2 (F-PRES-3); Gao et al. Theorem 4.1 for n >= 3 (F-PRES-7)
R("the sandpile group of the folded cube `Q_n/⟨𝟙⟩`, and its equivalent form",
  "the sandpile group of the folded cube `Q_n/⟨𝟙⟩`, and, for `n ≥ 2`, its equivalent form", 'F-PRES-3 §0')
R("including Gao, Marx-Kuo, McDonald and Yuen's Theorems 4.1–4.2,",
  "including Gao, Marx-Kuo, McDonald and Yuen's Theorem 4.1 for `n ≥ 3` and Theorem 4.2,", 'F-PRES-7 §0')
# §0: the cold reading
R("**Not yet read cold.** This certificate has not yet been read by a reader other than its writer. That reading is owed before it is released (§2 item 7).",
  "**Read cold.** A reader other than its writer, with the compiled project at hand, read this certificate before release; verdict «holds as far as I can check», with four errors in the record (one sentence and three counts) and no error in a statement. They are corrected here (§2 item 7).", 'cold §0')
# §1.1: one vocabulary for the statements (F-PRES-2)
R("Printed by Lean with `#check` (log `logs/CertCubo.log`, from `checks/CertCubo.lean`, run on the rebuilt project of §8).",
  "Printed by Lean with `#check` (log `logs/CertCubo.log`, from `checks/CertCubo.lean`, run on the rebuilt project of §8). **Twenty-four statements are printed here.** Sixteen of them are the *headline theorems*, whose dependency cones are counted in §3.3: `M1`, `M2`, `theorem_D_i`, `BaiCounts.B1`, `B2`, `G1`, `G2`, `G3`, `Y2`, `FoldLaw.H`, `DW`, `DW'`, `L1`, `FoldLaw.R`, `OddParts.B1`, `C5`. With `MainTheorem.G2` and the four `M3_*` they are the twenty-one statements restated by hand in `CheckCubo.lean` (§1.4); with the three cases `P1`–`P3` of Corollary 1.6, the twenty-four printed here.", 'F-PRES-2 §1.1')
# §1.3: the folded cube (F-ERR-4)
R("| the folded cube `Q_n/⟨𝟙⟩`: vertices the pairs of antipodal words, two pairs joined once for each pair of words, one from each, that differ in one letter (§1.3) | `aElt`, `Gbar`, `mk`, `lapBar` | Literal: `Gbar n` is `G n` modulo `aElt n = 𝟙`, and `lapBar ℤ n u x = n·u x − Σ_i u (x + mk (e i))`, with the multiplicities of the paper: at `n = 2` the two images of `e_1`, `e_2` coincide and give the double edge of §1.3. |",
  "| the folded cube `Q_n/⟨𝟙⟩`: vertices the `2^{n−1}` pairs `{x, x + 𝟙}` of antipodal words; `{x, x + 𝟙}` is joined to `{x + e_i, x + 𝟙 + e_i}` once for each `i = 1, …, n`; the Cayley graph of `𝔽_2^n/⟨𝟙⟩` with the images of the unit vectors (§1.3) | `aElt`, `Gbar`, `mk`, `lapBar` | `Gbar n` is `G n` modulo `aElt n = 𝟙`, and `lapBar ℤ n u x = n·u x − Σ_i u (x + mk (e i))`: the Laplacian of the Cayley multigraph of `𝔽_2^n/⟨𝟙⟩` with the `n` images of the unit vectors, one edge for each `i`. At `n = 2` the two images of `e_1`, `e_2` coincide and give the double edge of §1.3. Version 8 of the paper describes the edges as «once for each pair of words, one from each, that differ in one letter»; read literally, that sentence counts each edge twice (`(x, x + e_i)` and `(x + 𝟙, x + 𝟙 + e_i)`). The paper's next sentence, its proofs and its numbers use the Cayley graph, as Lean does. |", 'F-ERR-4 row')
# §1.3: DW' at n = 1 (F-PRES-3)
R("The form is stated for `n ≥ 2`, where `a_n` is defined; at `n = 1` the paper's formula for `a_n` has a negative exponent. |",
  "`DW'` is stated for `n ≥ 2`. At `n = 1` the paper's `a_1 = 2^{−1} − 2^{−1} = 0` and both groups are trivial (`B1` at `n = 1` gives `l0 (Syl2 (K 1)) = 1`), but Lean does not state that case. |", 'F-PRES-3 row')
# §1.3: Corollary 1.6 row, Theorem 4.1 at n = 2 (F-PRES-7)
R("`G1`–`G3` the four statements of «In particular», for `n ≥ 3`, `n ≥ 3`, `n ≥ 4`. |",
  "`G1`–`G3` the four statements of «In particular», for `n ≥ 3`, `n ≥ 3`, `n ≥ 4`. Gao et al. state their Theorem 4.1 for `n ≥ 2`; the case `n = 2` (`K(Q_2) = ℤ/4`) is not in Lean. |", 'F-PRES-7 row')
# Generality (F-PRES-3)
R("The paper's results for which Lean asks for more than the paper are `DW'`, `L1` and `R`, which need `n ≥ 2`, where `a_n` is defined.",
  "The paper's results for which Lean asks for more than the paper are `DW'`, `L1` and `FoldLaw.R`, stated in Lean for `n ≥ 2`; at `n = 1` every group involved is trivial and every count is `0`, but Lean does not state that case. In Corollary 1.6, Gao et al.'s Theorem 4.1 at `n = 2` is not in Lean.", 'F-PRES-3 generality')
# §1.4 vocabulary
R("the objects of §1.2 (by `rfl`) and the twenty-one headline statements (closed by the name of the certified theorem).",
  "the objects of §1.2 (by `rfl`) and the twenty-one statements of §1.1 named there (closed by the name of the certified theorem).", 'F-PRES-2 §1.4')
# §2 item 7: the cold reading
R("7. **Not yet read cold.** No reader other than the writer has read this certificate. A cold reading, with the compiled project at hand, is owed before release.",
  "7. **The cold reading.** On 11 October 2026 a reader other than the writer (a separate Claude session, with the paper, the sources, the pieces, the logs and the compiled project, but not the author's notes) read this certificate. It re-read every definition in the statements against the paper; printed the statements and their axioms itself; re-elaborated from source the eight files of `M1`, `DW`, `DW'` and five more of the chain; evaluated the multiplicities and 2 121 raw clocks in Lean against its own Python; and checked the Main Theorem, Theorem DW and Corollaries 1.4–1.7 against Smith forms it computed from the graphs (`n ≤ 11` for the 2-parts, `n ≤ 9` for the odd parts): 161 checks, 0 failures. Verdict: «holds as far as I can check»; no Lean statement says something other than the paper. It found four errors in the record, none in a statement: the folded-cube sentence of §1.3; the number of checks in Table 6a (C13, and C21–C30 left blank; the author then found that C1–C16 report counts too); 885, not 884, lines of `#print axioms`; and 3 449 theorem and lemma declarations, not 3 237 (the latter counts lines). They are corrected here. What it did not check: 408 of the 416 modules were not re-elaborated by it, 59 of the 68 rows of the §3 table were not read statement by statement, and the provenance data of Table 6a. Its report and checks are kept with the record (`reports/LECTOR_FRIO_LEAN_1/delivered/`).", 'cold §2')
# §3 bold names
R("The names in bold are the headline theorems of §1.1.",
  "The names in bold are statements printed in §1.1.", 'F-PRES-2 §3')
# §3.3 identical line for line (F-PRES-5)
R("Its output is identical, line for line, before and after the clean rebuild (§8).",
  "Its output is identical, line for line, before and after the clean rebuild (§8), except the watchdog's final line (time and memory).", 'F-PRES-5 §3.3')
# §4 instances (F-PRES-1)
R("  An instance adds no axiom. The structures on the types in the statements of §1.1 are the product structures of Mathlib (`XFam`, through `inferInstanceAs`).",
  "  Besides, one line `attribute [instance] DPLattice.fintype DPLattice.decEq` (`DPLattice/Basic.lean`) makes two more declarations instances: the finiteness and the decidable equality of the index type of a divided-power lattice. The project also has three tactic macros (`weyl_close`, local, in `DPLattice/Weyl.lean`; `wf_simp` and `wf_close` in `WeylFilt/Comm.lean`) and two local notations (`lV`, `lP` in `Split/ChangeOfBasis.lean`, abbreviations of `DirectSum.lof`). A macro only produces a proof term that the kernel still checks.\n\n  An instance adds no axiom. The structures on the types in the statements of §1.1 are the product structures of Mathlib (`XFam`, through `inferInstanceAs`).", 'F-PRES-1 §4')
# §4 axioms (F-ERR-2)
R("  - Over the 68 final check logs, 884 lines of `#print axioms`: 868 give the three axioms, 12 give `[propext, Quot.sound]` and 4 give `[propext]`. The last sixteen are small lemmas about digits, lists, ranks and units.",
  "  - Over the 68 final check logs, 885 lines of `#print axioms`: 868 give the three axioms, 12 give `[propext, Quot.sound]`, 4 give `[propext]`, and one (`FormalDance.C1`, `checkC40b.log`) depends on no axiom. The last seventeen are small lemmas about digits, lists, ranks and units.", 'F-ERR-2')
R("  - In `CheckCubo_postclean.log` the twenty-one headline theorems give the three axioms.",
  "  - In `CheckCubo_postclean.log` the twenty-one statements of §1.4 give the three axioms.", 'F-PRES-2 §4')
# §6 bullets (F-ERR-1, F-ERR-3)
R("- **Brute force:** the script `lean/chkC<N>.py`, log `logs/chkC<N>.log`, every one with 0 failures. The number of checks is given where the log reports one.",
  "- **Brute force:** the script `lean/chkC<N>.py`, log `logs/chkC<N>.log`, every one with 0 failures. The number of checks is the total the log reports; where the log reports counts by kind only (C1–C16), it is their sum, with the number of kinds.", 'F-ERR-1 bullet')
R("Theorems are lines beginning with `theorem ` or `lemma `;",
  "The column «`theorem`/`lemma` lines» counts lines beginning with the word `theorem` or `lemma` (it leaves out the declarations preceded by an attribute such as `@[simp]`; the declarations are counted in §7);", 'F-ERR-3 bullet')
R("The two tables are generated from data files by `lean/CERTIFICADO/make_tables.py`; no number in them was copied by hand.",
  "The two tables are generated by `lean/CERTIFICADO/make_tables.py`: Table 6b from data files, and the checks column of Table 6a from the brute-force logs themselves. Two columns of Table 6a were transcribed by hand into that script: the Aristotle task identifiers, from the audit log, and the controls (fired/total), from the logs; the cold reader checked the controls against the 68 logs, with no mismatch.", 'F-ERR-1 sentence')
# §7 (F-ERR-3)
R("| | Files | Lines | Theorems and lemmas | Definitions |",
  "| | Files | Lines | `theorem`/`lemma` lines | Definitions |", 'F-ERR-3 §7 header')
R("- **`sorry`: 0.**\n",
  "- **Theorem and lemma declarations in code: 3 449.** The column above counts lines that begin with the word `theorem` or `lemma`; it leaves out the 213 declarations preceded by an attribute (`@[simp]` 210, `@[ext]` 3) and counts one comment line.\n- **`sorry`: 0.**\n", 'F-ERR-3 §7')
# §8 identical line for line (F-PRES-5) and paths (F-PRES-6)
R("**Their output is identical, line for line, to the runs before the rebuild** (`CheckCubo.log`, `DepsCubo.log`).",
  "**Their output is identical, line for line, to the runs before the rebuild** (`CheckCubo.log`, `DepsCubo.log`), except the watchdog's final line (time and memory).", 'F-PRES-5 §8')
R("**Commands**, from the project root (`lean/proyecto_cubo/` here):",
  "**Paths.** Every path in this certificate is relative to the project folder of the author's working tree; the public repository keeps the same relative paths (`lean/…`, `logs/…`, `checks/…`).\n\n**Commands**, from the project root (`lean/proyecto_cubo/` here):", 'F-PRES-6 §8')
open(F, 'w').write(s)
print('applied')

# Note: the two «the word `theorem` or `lemma`» texts above were edited after a first build (a trailing space in a code span printed as « :»); the src was edited the same way.
