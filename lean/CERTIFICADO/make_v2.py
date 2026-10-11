# make_v2.py — Grepy Escribano, 11 Oct 2026.
# Version 2 of the Lean certificate of «The Dancing Sand Theorem»: version 1 (as published, read cold twice) plus
# piece C53, the small cases. Built from LEAN_CERTIFICATE_DANCING_SAND_v1.src.md by anchored edits; every
# replacement is asserted unique. Numbers that come from the Lean runs of version 2 are read from
# data_v2/values.txt («key=value», one per line), written from the logs CheckC53.log, CheckCubo2.log,
# CertCubo2.log and DepsCubo2.log. Output: LEAN_CERTIFICATE_DANCING_SAND_v2.src.md (then fill_v2.py).
import os
H = os.path.dirname(os.path.abspath(__file__))
s = open(os.path.join(H, 'LEAN_CERTIFICATE_DANCING_SAND_v1.src.md'), encoding='utf-8').read()
V = dict(l.split('=', 1) for l in open(os.path.join(H, 'data_v2', 'values.txt')).read().splitlines() if '=' in l)

def rep(old, new, label, n=1):
    global s
    c = s.count(old)
    assert c == n, (label, c)
    s = s.replace(old, new)
    print('ok', label)

# 0. Title, date, companion
rep('# THE DANCING SAND THEOREM — LEAN CERTIFICATE v1', '# THE DANCING SAND THEOREM — LEAN CERTIFICATE v2', 'title')
rep('Certificate v1 · 11 October 2026 · read cold and corrected the same day (§2 item 7)',
    'Certificate v2 · 11 October 2026 · version 1 read cold and corrected the same day (§2 item 7); version 2 adds piece C53, the small cases (§1.5), and was read cold in its turn (§2 item 9)',
    'date line')
rep('Companion to *The Dancing Sand Theorem — The 2-part of the sandpile group of the hypercube, for every n*, version 8 (6 October 2026), Zenodo DOI 10.5281/zenodo.23188299. The numbers of sections and results below are those of version 8.',
    f"Companion to *The Dancing Sand Theorem — The 2-part of the sandpile group of the hypercube, for every n*, version 10 (11 October 2026), Zenodo DOI {V['paper_doi']}. The numbers of sections and results below are those of version 8, which versions 9 and 10 keep (they add §12.3, on this certificate, and change nothing else in the numbering).",
    'companion')

# 1. Verdict
rep("where `K̄(n)` is the sandpile group of the folded cube `Q_n/⟨𝟙⟩`, and, for `n ≥ 2`, its equivalent form `Syl_2 K(Q_n) ≅ (ℤ/2)^{a_n} ⊕ H`",
    "where `K̄(n)` is the sandpile group of the folded cube `Q_n/⟨𝟙⟩`, and its equivalent form `Syl_2 K(Q_n) ≅ (ℤ/2)^{a_n} ⊕ H`",
    'verdict DW prime')
rep("including Gao, Marx-Kuo, McDonald and Yuen's Theorem 4.1 for `n ≥ 3` and Theorem 4.2",
    "including Gao, Marx-Kuo, McDonald and Yuen's Theorem 4.1 for every `n ≥ 2` and Theorem 4.2",
    'verdict Gao 4.1')
rep("and every one of the 68 numbered statements of §2–§10 on which these rest, from Lemma 2.1 to Theorem 10.22, Theorem D among them (§3).",
    "and every one of the 68 numbered statements of §2–§10 on which these rest, from Lemma 2.1 to Theorem 10.22, Theorem D among them (§3).\n\n**Version 2.** Version 1 proved the equivalent form of Theorem DW, the count of cyclic factors of `Syl_2 K̄(n)` and the `𝔽_2`-rank of the folded Laplacian for `n ≥ 2`, and Gao et al.'s Theorem 4.1 for `n ≥ 3`. Piece C53 adds the missing cases, `n = 1` and `n = 2`, and states each of the four for every `n` the paper states it for (§1.5). Every statement of the paper is now proved in Lean for every `n` for which the paper states it.",
    'verdict v2 paragraph')
rep("**All 416 modules of the project were compiled again from their sources on the author's Mac, with exit code 0, in a clean rebuild that skipped none** (§8).",
    f"**All 416 modules of version 1 were compiled again from their sources on the author's Mac, with exit code 0, in a clean rebuild that skipped none; the four modules of piece C53 were then compiled from their sources, with the sources of the other 416 unchanged** (§8).",
    'verdict rebuild')
rep("**Read cold.** A reader other than its writer, with the compiled project at hand, read this certificate before release; verdict «holds as far as I can check», with four errors in the record (one sentence and three counts) and no error in a statement. They are corrected here (§2 item 7).",
    "**Read cold.** A reader other than its writer, with the compiled project at hand, read this certificate before release; verdict «holds as far as I can check», with four errors in the record (one sentence and three counts) and no error in a statement. They are corrected here (§2 item 7). The changes of version 2 were read cold in their turn (§2 item 9).",
    'verdict read cold')

# 2. §1.3 rows and Generality
rep("`DW'` is stated for `n ≥ 2`. At `n = 1` the paper's `a_1 = 2^{−1} − 2^{−1} = 0` and both groups are trivial (`B1` at `n = 1` gives `l0 (Syl2 (K 1)) = 1`), but Lean does not state that case.",
    "`DW'` is stated for `n ≥ 2`. At `n = 1` the paper's `a_1 = 2^{−1} − 2^{−1} = 0` and both groups are trivial; version 2 proves this case (`SmallCases.DW'_one`, with `H` trivial) and states the equivalent form for every `n ≥ 1` (`SmallCases.DW'_all`, §1.5).",
    'row DW')
rep("Gao et al. state their Theorem 4.1 for `n ≥ 2`; the case `n = 2` (`K(Q_2) = ℤ/4`) is not in Lean.",
    "Gao et al. state their Theorem 4.1 for `n ≥ 2`; version 2 proves the case `n = 2` (`K(Q_2) = ℤ/4`, `SmallCases.T0`, `SmallCases.G1_two`) and states the theorem for every `n ≥ 2` (`SmallCases.G1_all`, §1.5).",
    'row Gao')
rep("**Generality.** Every statement holds for every `n` for which the paper states it, and `OddParts.B1` for every `n ≥ 0`. The paper's results for which Lean asks for more than the paper are `DW'`, `L1` and `FoldLaw.R`, stated in Lean for `n ≥ 2`; at `n = 1` every group involved is trivial and every count is `0`, but Lean does not state that case. In Corollary 1.6, Gao et al.'s Theorem 4.1 at `n = 2` is not in Lean.",
    "**Generality.** Every statement holds in Lean for every `n` for which the paper states it, and `OddParts.B1` for every `n ≥ 0`. In version 1, `DW'`, `L1` and `FoldLaw.R` were stated for `n ≥ 2` and Gao et al.'s Theorem 4.1 for `n ≥ 3`; version 2 adds the cases `n = 1` (every group involved is trivial and every count is `0`) and `n = 2` (`K(Q_2) = ℤ/4`), and states the four results for every `n` (§1.5).",
    'generality')

# 3. §1.4 and the new §1.5
rep("The three cases `P1`–`P3` of Corollary 1.6 are printed in `CertCubo.lean`, with the same three axioms each.",
    f"The three cases `P1`–`P3` of Corollary 1.6 are printed in `CertCubo.lean`, with the same three axioms each.\n\n**Version 2.** `checks/CheckCubo2.lean` is `CheckCubo.lean` with one import more and, at its end, the four statements of §1.5 restated by hand: twenty-five restatements, and twenty-five lines of `#print axioms`, every one `[propext, Classical.choice, Quot.sound]` (log `logs/CheckCubo2.log`, exit code 0, {V['check2_s']} s, peak {V['check2_gib']} GiB). Its first twenty-one lines of axioms are identical to those of `CheckCubo_postclean.log`. The piece's own check file `checks/CheckC53.lean` restates all fourteen statements of C53 (log `logs/CheckC53.log`).\n\n### 1.5 Version 2: the small cases (piece C53)\n\nPiece C53 (folder `SmallCases`) proves Theorem DW′, the count `L1` and the `𝔽_2`-rank `R` at `n = 1`, and Gao et al.'s Theorem 4.1 at `n = 2`; each case is proved directly (at `n = 1`: `Q_1` is one edge, the folded cube is one vertex with one loop, `Fold.lapBar A 1 = 0`, and both `2`-parts are trivial; at `n = 2`: `Syl_2 K(Q_2) ≅ ℤ/4`). It then states each of the four results for every `n` the paper states it for, by cases: the new case, or the theorem of version 1. Printed by `#check` (log `logs/CertCubo2.log`, from `checks/CertCubo2.lean`):\n\n<<<SmallCases.DW'_all SmallCases.L1_all SmallCases.R_all SmallCases.G1_all>>>\n\nThe statements are those of `FoldLaw.DW'`, `FoldLaw.L1`, `FoldLaw.R` and `PodiumCor.G1` (§1.1) with the hypothesis `2 ≤ n` replaced by `1 ≤ n` (the first three) and `3 ≤ n` by `2 ≤ n` (the fourth). They use no definition that is not printed in §1.2. The ten statements of the cases themselves are `SmallCases.S0`–`S3`, `DW'_one`, `L1_one` (the item «(L1-1)» of the piece: a Lean name cannot contain `-`), `R1`, `T0`, `T1` and `G1_two`, each restated by hand in `CheckC53.lean`.",
    'section 1.5')

# 4. §2: items 8, 9
rep("8. **Aristotle's per-task times** are shown on its web page and were not exported. The download times in §6 are the save times of the result files. Aristotle's own account of its 68 runs is in `ARISTOTLE_SUMMARY.md` of the returned project, one section per run.",
    "8. **Aristotle's per-task times** are shown on its web page and were not exported. The download times in §6 are the save times of the result files. Aristotle's own account of its 69 runs is in `ARISTOTLE_SUMMARY.md` of the returned project, one section per run.\n9. **The cold reading of version 2.** [[V2READ]]",
    'items 8 9')

# 5. §3
rep("The paper was cut into **68 pieces**, `C1`–`C52` (with letter suffixes where one section needed several pieces).",
    "The paper was cut into **68 pieces**, `C1`–`C52` (with letter suffixes where one section needed several pieces); version 2 adds a 69th, `C53`, for the small cases (§1.5).",
    'sec3 pieces')
rep("- the project's `RequestProject/` folder is identical, file by file, to the one in Aristotle's last returned project (piece C52);\n- every one of the 68 folders is identical to its copy in the returned project of the piece that created it;",
    "- the project's `RequestProject/` folder is identical, file by file, to the one in Aristotle's last returned project (piece C53);\n- every one of the 69 folders is identical to its copy in the returned project of the piece that created it;",
    'sec3 checked')
rep("- the 68 piece files inside the returned project are identical to the ones sent.",
    "- the 68 piece files of C1–C52 inside the returned project are identical to the ones sent. Piece C53 was not attached as a file: its text was pasted into the request (the project page had grown too large for the file input), and that text, `lean/msgC53.txt`, is the piece file `lean/C53_the_small_cases.md` preceded by a one-paragraph instruction.",
    'sec3 piece files')
rep("| C52 | the odd parts, Corollary 1.4 | `OddParts` | **`OddParts.B1`**, **`C5`**, `Q0`–`Q2`, `OddParts.X`, `F1`–`F3`, `B0` |",
    "| C52 | the odd parts, Corollary 1.4 | `OddParts` | **`OddParts.B1`**, **`C5`**, `Q0`–`Q2`, `OddParts.X`, `F1`–`F3`, `B0` |\n| C53 | the small cases: Theorem DW′, the count of §10.8 and the `𝔽_2`-rank at `n = 1`; Gao et al.'s Theorem 4.1 at `n = 2` (version 2) | `SmallCases` | `S0`–`S3`, `DW'_one`, `L1_one`, `R1`, `T0`, `T1`, `G1_two`, **`DW'_all`**, **`L1_all`**, **`R_all`**, **`G1_all`** |",
    'sec3 row C53')
rep("Every one of the 68 numbered statements of §2–§10 of the paper is in a piece of this table.",
    "Every one of the 68 numbered statements of §2–§10 of the paper is in a piece of this table. Piece C53 proves no numbered statement of §2–§10: it completes four results of §1.3 and §1.4 of the paper.",
    'sec3 every')

# 6. §3.3 cone
rep("| `OddParts.C5` (the odd part of `K̄(n)`) | 277 | 13 |\n| **union of the sixteen headline theorems** | **7 988** | **341** |",
    f"| `OddParts.C5` (the odd part of `K̄(n)`) | 277 | 13 |\n| **union of the sixteen headline theorems** | **7 988** | **341** |\n| `SmallCases.DW'_all` (version 2) | {V['cone_dwall_d']} | {V['cone_dwall_m']} |\n| `SmallCases.L1_all` (version 2) | {V['cone_l1all_d']} | {V['cone_l1all_m']} |\n| `SmallCases.R_all` (version 2) | {V['cone_rall_d']} | {V['cone_rall_m']} |\n| `SmallCases.G1_all` (version 2) | {V['cone_g1all_d']} | {V['cone_g1all_m']} |\n| **union of the twenty headline theorems of version 2** | **{V['union20_d']}** | **{V['union20_m']}** |",
    'cone table')
rep("The project has 416 modules, and 75 are outside the union:",
    f"In version 1 the project has 416 modules, and 75 are outside the union of the sixteen. In version 2 it has 420 modules; the union of the twenty (the sixteen and the four `_all` statements of C53) has {V['union20_m']}, and the {420 - int(V['union20_m'])} outside it are the same 75 and `SmallCases.All`. The 75 of version 1 are:",
    'cone outside')
rep("Its output is identical, line for line, before and after the clean rebuild (§8), except the watchdog's final line (time and memory).",
    "Its output is identical, line for line, before and after the clean rebuild (§8), except the watchdog's final line (time and memory). For version 2, `checks/DepsCubo2.lean` (log `logs/DepsCubo2.log`) is `DepsCubo.lean` with one import more and five lines more: the cones of the four `_all` statements and the union of the twenty. Its lines for the sixteen theorems of version 1 are identical to those of `DepsCubo_postclean.log`.",
    'cone v2 file')

# 7. §4 trust base
rep("- **Forbidden constructs**, searched in all 416 files: none.", "- **Forbidden constructs**, searched in all 420 files: none.", 'forbidden')
rep("- **The tactic `decide`** occurs in 16 files.", "- **The tactic `decide`** occurs in 17 files (one of them, `SmallCases/PartT.lean`, for the two counts of the factors of `ℤ/4` and the empty index set of the family of `λ = 1`).", 'decide')
rep("- **Axioms**, printed after each piece (68 final check logs; for C31 the final run is `checkC31b.log`) and again in `CheckCubo_postclean.log` and `CertCubo.log`.",
    "- **Axioms**, printed after each piece (69 final check logs; for C31 the final run is `checkC31b.log`) and again in `CheckCubo_postclean.log`, `CertCubo.log`, `CheckCubo2.log` and `CertCubo2.log`.",
    'axioms 69')
rep("  - Over the 68 final check logs, 885 lines of `#print axioms`: 868 give the three axioms, 12 give `[propext, Quot.sound]`, 4 give `[propext]`, and one (`FormalDance.C1`, `checkC40b.log`) depends on no axiom.",
    f"  - Over the 68 final check logs of version 1, 885 lines of `#print axioms`: 868 give the three axioms, 12 give `[propext, Quot.sound]`, 4 give `[propext]`, and one (`FormalDance.C1`, `checkC40b.log`) depends on no axiom. The check log of C53 has 14 lines: {V['c53_ax3']} give the three axioms{V['c53_axother']}.",
    'axioms lines')
rep("  - In `CheckCubo_postclean.log` the twenty-one statements of §1.4 give the three axioms.",
    "  - In `CheckCubo_postclean.log` the twenty-one statements of §1.4 give the three axioms, and in `CheckCubo2.log` the twenty-five.",
    'axioms check2')
rep("- **Aristotle's own register** for the project: 527 properties PROVED, 0 NEGATED, 0 in progress, after the last piece (audit log `lean/INFORME_ARISTOTLE_CUBO_v1.md`, run C52).",
    "- **Aristotle's own register** for the project: 527 properties PROVED, 0 NEGATED, 0 in progress, after piece C52, and 541 PROVED, 0 NEGATED, 0 in progress after piece C53 (audit log `lean/INFORME_ARISTOTLE_CUBO_v1.md`, runs C52 and C53).",
    'register')

# 8. §5
rep("The cycle, for each of the 68 pieces, in one turn:", "The cycle, for each of the 69 pieces, in one turn:", 'cycle')

# 9. §6
rep("the cold reader checked the controls against the 68 logs, with no mismatch.",
    "the cold reader of version 1 checked the controls against the 68 logs, with no mismatch. Version 2 adds the row of C53: its task, tarball `(69)` and brute-force log `logs/chkC53.log` (14 checks, one line `PASS` each, and four controls that must fail, and fail); its rebuild columns are its own build, one module at a time under the cap of §5 (the modules are new, so the build is from their sources).",
    'sec6 note')

# 10. §7
rep("| The 68 folders | 415 | 60 940 | 3 237 | 876 |", "| The 69 folders | 419 | 61 261 | 3 258 | 877 |", 'totals row')
rep("- **Theorem and lemma declarations in code: 3 449.**", "- **Theorem and lemma declarations in code: 3 470** (3 449 in version 1, and 21 in `SmallCases`).", 'decls')
rep("- **Brute-force checks before sending:** 68 scripts, 0 failures. Every script carried negative controls; all fired except one control in each of C28, C33 and C49b, declared.",
    "- **Brute-force checks before sending:** 69 scripts, 0 failures. Every script carried negative controls; all fired except one control in each of C28, C33 and C49b, declared.",
    'bf')
rep("about four days and five hours for the 68 pieces.",
    "about four days and five hours for the 68 pieces. Piece C53 was sent on 11 October 2026 at 13:44 CEST and its result downloaded at 14:37.",
    'calendar')
rep("- **Aristotle's register:** 527 properties PROVED, 0 NEGATED, 0 in progress.",
    "- **Aristotle's register:** 541 properties PROVED (527 after C52), 0 NEGATED, 0 in progress.",
    'register 2')

# 11. §8
rep("lake build                               # the 416 modules of RequestProject (or one at a time)\nlake env lean checks/CheckCubo.lean      # the hand restatements of §1.4\nlake env lean checks/CertCubo.lean       # the statements and definitions printed in §1\nlake env lean checks/DepsCubo.lean       # the dependency cone of §3.3",
    "lake build                               # the 420 modules of RequestProject (or one at a time)\nlake env lean checks/CheckCubo2.lean     # the hand restatements of §1.4 (version 2)\nlake env lean checks/CertCubo2.lean      # the statements and definitions printed in §1\nlake env lean checks/DepsCubo2.lean      # the dependency cone of §3.3",
    'commands')
rep("Then `CheckCubo.lean` and `DepsCubo.lean` were run again against the rebuilt files:",
    f"**Version 2.** On 11 October 2026 the four modules of `SmallCases` (piece C53), which had never been compiled on this machine, were compiled from their sources, one at a time under the watchdog with the cap of §5: {V['c53_build']}. Before that, the md5 of each of the 416 sources of version 1 was compared with `MANIFEST_md5_416.txt`: all identical, so the clean rebuild of version 1 stands for them. The md5 list of the 420 sources of version 2 is `lean/clean_rebuild/MANIFEST_md5_420.txt` (md5 `{V['man420']}`).\n\nThen `CheckCubo.lean` and `DepsCubo.lean` were run again against the rebuilt files:",
    'v2 build')

# 12. §9 and references
rep("The proofs in Lean were written by the AI system Aristotle (Harmonic) from 68 pieces written from the paper.",
    "The proofs in Lean were written by the AI system Aristotle (Harmonic) from 69 pieces written from the paper.",
    'sec9')
rep("- R. Amichis Luengo, *The Dancing Sand Theorem — The 2-part of the sandpile group of the hypercube, for every n*, version 8, Zenodo, DOI 10.5281/zenodo.23188299; all versions, concept DOI 10.5281/zenodo.23188298.",
    f"- R. Amichis Luengo, *The Dancing Sand Theorem — The 2-part of the sandpile group of the hypercube, for every n*, version 10, Zenodo, DOI {V['paper_doi']}; version 8, DOI 10.5281/zenodo.23188299; all versions, concept DOI 10.5281/zenodo.23188298.",
    'ref paper')

open(os.path.join(H, 'LEAN_CERTIFICATE_DANCING_SAND_v2.src.md'), 'w', encoding='utf-8').write(s)
print('written v2 src')
