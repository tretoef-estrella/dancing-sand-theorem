# The Dancing Sand Theorem in Lean 4

*This folder and [../logs/](../logs/README.md) hold the same files as version 2 of the Zenodo record of the Lean certificate, with the same relative paths. The paper is in [../paper/](../paper/THE_DANCING_SAND_THEOREM_v12.pdf).*

This folder holds a complete Lean 4 proof, with the Mathlib library, of every theorem of the paper **«The Dancing Sand Theorem — the 2-part of the sandpile group of the hypercube, for every n»** ([doi.org/10.5281/zenodo.23188298](https://doi.org/10.5281/zenodo.23188298)), for every `n` for which the paper states it: the Main Theorem (the whole 2-part of the sandpile group `K(Q_n)` of the hypercube graph, for every `n ≥ 1`), Theorem DW (the fold law for the folded cube) and its equivalent form, Corollaries 1.4–1.7, Bai's odd part of `K(Q_n)`, Theorem D, and each of the 68 numbered statements of §2–§10.

It is archived on Zenodo as its own record (software), a supplement to the paper: [doi.org/10.5281/zenodo.23298436](https://doi.org/10.5281/zenodo.23298436) (version 2; all versions: [doi.org/10.5281/zenodo.23296707](https://doi.org/10.5281/zenodo.23296707)). Version 2 adds piece C53, the small cases: the equivalent form of Theorem DW, the count of §10.8 and the `𝔽_2`-rank of the folded Laplacian at `n = 1`, and Gao et al.'s Theorem 4.1 at `n = 2`.

**Read first:** [CERTIFICADO/LEAN_CERTIFICATE_DANCING_SAND_v2.pdf](CERTIFICADO/LEAN_CERTIFICATE_DANCING_SAND_v2.pdf) ([Markdown](CERTIFICADO/LEAN_CERTIFICATE_DANCING_SAND_v2.md)). It gives:
- the certified statements and every definition they use, exactly as Lean prints them, and a line-by-line comparison with the paper;
- what is **not** formalized (the certificate's §2);
- how the proof is organised, the trust base, the procedure, the data of each of the 69 pieces, the clean rebuild from source, and how to reproduce everything.

Version 1 of the certificate is kept next to it, as published ([PDF](CERTIFICADO/LEAN_CERTIFICATE_DANCING_SAND_v1.pdf)); it cites the files by the names of the author's working tree (see «Paths» below).

## In one line

`MainTheorem.M1` in [`proyecto_cubo/RequestProject/MainTheorem/Theorem.lean`](proyecto_cubo/RequestProject/MainTheorem/Theorem.lean) and `FoldLaw.DW` in [`proyecto_cubo/RequestProject/FoldLaw/PartH.lean`](proyecto_cubo/RequestProject/FoldLaw/PartH.lean) compile with no `sorry` and depend only on the axioms `propext`, `Classical.choice`, `Quot.sound`. Nothing is cited: Lean defines the Laplacian of `Q_n`, its cokernel and the torsion of that cokernel, and proves the theorems themselves. The project has 420 Lean files, 61 285 lines and 3 470 theorem and lemma declarations.

## Read cold

Before release, version 1 of the certificate was read by a reader other than its writer, with the compiled project at hand. That reader re-read every definition in the statements against the paper, re-elaborated from source the files of the Main Theorem, of Theorem DW and five more of the chain, and compared the rule with Smith forms it computed from the graphs (`n ≤ 11`). Verdict: «holds as far as I can check». It found four errors in the record (one sentence and three counts) and none in a statement; all were corrected (the certificate's §2 item 7). A second, closed reading checked the corrections.

The changes of version 2 were read cold in their turn, with the Lean of piece C53 (§2 item 9). Verdict: the Lean of C53 is right, faithful and clean; nine points of wording and presentation, all corrected.

## The layout of this folder

| Folder | What it holds |
|---|---|
| [CERTIFICADO/](CERTIFICADO/) | the certificate (versions 1 and 2, Markdown and PDF) and the scripts and data that generate it |
| [proyecto_cubo/](proyecto_cubo/) | the Lean project: `RequestProject/` (69 folders, one per piece, and `Main.lean`), the check files in `checks/`, the lake files |
| [clean_rebuild/](clean_rebuild/) | the clean rebuild from source of the 416 modules of version 1, one log per module, and the md5 lists of the sources |
| [pieces/](pieces/) | the 69 pieces sent to Aristotle (`C<N>_….md`), the instructions sent with them (`instrC<N>.txt`), and `msgC53.txt` |
| [brute_force/](brute_force/) | the brute-force check of each piece, run before sending it, with negative controls (`chkC<N>.py`) |
| [build/](build/) | the scripts of the local builds (`buildC<N>.sh`) |
| [audit/](audit/) | the audit log, piece by piece (`INFORME_ARISTOTLE_CUBO_v1.md`), and the md5 list of every file of version 1 of the Zenodo record and of version 2 |
| [PATHS_WORKING_TREE_TO_PUBLISHED.tsv](PATHS_WORKING_TREE_TO_PUBLISHED.tsv) | for every file that sits in a subfolder here, its name in the author's working tree |

## Where the evidence is

| What you want to see | File |
|---|---|
| The main results restated by hand, with their axioms | [../logs/final_checks/CheckCubo2.log](../logs/final_checks/CheckCubo2.log), produced by [proyecto_cubo/checks/CheckCubo2.lean](proyecto_cubo/checks/CheckCubo2.lean); for version 1, after the clean rebuild, [../logs/final_checks/CheckCubo_postclean.log](../logs/final_checks/CheckCubo_postclean.log) |
| The statements and definitions printed in the certificate's §1 | [../logs/final_checks/CertCubo2.log](../logs/final_checks/CertCubo2.log), by [proyecto_cubo/checks/CertCubo2.lean](proyecto_cubo/checks/CertCubo2.lean) |
| The dependency cone of each main result | [../logs/final_checks/DepsCubo2.log](../logs/final_checks/DepsCubo2.log), by [proyecto_cubo/checks/DepsCubo2.lean](proyecto_cubo/checks/DepsCubo2.lean) |
| The clean rebuild from source: 416 of 416 modules, exit code 0 | [clean_rebuild/clean_rebuild_2026-10-10.log](clean_rebuild/clean_rebuild_2026-10-10.log), by [clean_rebuild/clean_rebuild_cubo.sh](clean_rebuild/clean_rebuild_cubo.sh) over [clean_rebuild/orden_modulos.txt](clean_rebuild/orden_modulos.txt); one log per module in [clean_rebuild/cr_logs/](clean_rebuild/cr_logs/) |
| The four modules of piece C53, compiled from their sources | [../logs/build/](../logs/build/) (`buildC53.log` and `buildC53_<module>.log`), by [build/buildC53.sh](build/buildC53.sh) |
| The md5 of every source file | [clean_rebuild/MANIFEST_md5_420.txt](clean_rebuild/MANIFEST_md5_420.txt) (version 2), [clean_rebuild/MANIFEST_md5_416.txt](clean_rebuild/MANIFEST_md5_416.txt) (version 1) |
| The 69 pieces, as sent to Aristotle | [pieces/](pieces/) (for example [pieces/C33_the_main_theorem.md](pieces/C33_the_main_theorem.md)) |
| For each piece: the brute-force check and its log | [brute_force/](brute_force/) `chkC<N>.py`, [../logs/brute_force/](../logs/brute_force/) `chkC<N>.log` |
| For each piece: the Lean file that restates its main statements by hand, and its log | [proyecto_cubo/checks/](proyecto_cubo/checks/) `CheckC<N>.lean`, [../logs/piece_checks/](../logs/piece_checks/) `checkC<N>.log` or `CheckC<N>.log` |
| For each piece: the local build | [build/](build/) `buildC<N>.sh`, [../logs/build/](../logs/build/) `buildC<N>*.log` |
| The audit log, piece by piece | [audit/INFORME_ARISTOTLE_CUBO_v1.md](audit/INFORME_ARISTOTLE_CUBO_v1.md) |
| Aristotle's own account of its runs | [proyecto_cubo/ARISTOTLE_SUMMARY.md](proyecto_cubo/ARISTOTLE_SUMMARY.md) |

## Paths

Version 2 of the certificate cites every file by its path in this layout (its §8). The author's working tree keeps the files of `pieces/`, `brute_force/`, `build/` and `audit/` directly in `lean/`, and those of the four folders of `../logs/` directly in `logs/`; the scripts and logs use those names, and so does version 1 of the certificate. [PATHS_WORKING_TREE_TO_PUBLISHED.tsv](PATHS_WORKING_TREE_TO_PUBLISHED.tsv) maps every one of them.

## How to check it

You need `elan` (the Lean toolchain manager) and about 7 GB of disk for Mathlib and its dependencies. The toolchain is `leanprover/lean4:v4.28.0` and Mathlib is `v4.28.0`. From `proyecto_cubo/` (in this folder):

```
lake exe cache get
lake build
lake env lean checks/CheckCubo2.lean
```

On a machine with little memory, build the modules one at a time, in the order of `clean_rebuild/orden_modulos.txt`, then the four modules of `SmallCases`, as the author did. A GitHub Actions workflow, [../.github/workflows/lean-build.yml](../.github/workflows/lean-build.yml), runs the first three commands on GitHub's machines, from the files as published, and then checks that no printed axiom list contains `sorryAx` or anything beyond `propext`, `Classical.choice` and `Quot.sound`; it is started by hand from the repository's Actions tab. Its run of 11 October 2026, on commit `f6d95a4`, built the 420 modules from source in 21 minutes and passed the hand restatements and the check «no `sorry`, no axiom beyond the three standard ones», 24 minutes in all ([run 38172080438](https://github.com/tretoef-estrella/dancing-sand-theorem/actions/runs/38172080438); its output is kept in [logs/actions/](../logs/actions/README.md), because GitHub deletes run logs after 90 days). GitHub's machines build many modules at once; the author's clean rebuild took 7 hours because it built one module at a time, on a machine with 8 GB.

For the Main Theorem alone, make a file `Check.lean` next to `lakefile.toml` with

```
import RequestProject.MainTheorem.Theorem
#check @MainTheorem.M1
#print axioms MainTheorem.M1
```

and run `lake env lean Check.lean`.

## Who did what

The Lean proofs were written by **Aristotle** (Harmonic), one piece at a time, from pieces written from the paper. Instances of Claude (Anthropic) wrote the pieces, audited what came back, compiled it on the author's machine, and read the certificate cold. Nothing was accepted on Aristotle's word: the Lean kernel checks every proof. The author, Rafael Amichis Luengo, directed the project and takes responsibility for the content.

Licence: code MIT, texts CC BY 4.0.
