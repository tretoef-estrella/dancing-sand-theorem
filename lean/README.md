# The Dancing Sand Theorem in Lean 4

*This folder and [../logs/](../logs/README.md) hold the same files as the Zenodo record of the Lean certificate, with the same relative paths; the md5 of every file of that record is in [MANIFEST_md5_zenodo_zip.txt](MANIFEST_md5_zenodo_zip.txt). The paper is in [../paper/](../paper/THE_DANCING_SAND_THEOREM_v9.pdf).*

This folder holds a complete Lean 4 proof, with the Mathlib library, of every theorem of the paper **«The Dancing Sand Theorem — the 2-part of the sandpile group of the hypercube, for every n»** ([doi.org/10.5281/zenodo.23188298](https://doi.org/10.5281/zenodo.23188298)): the Main Theorem (the whole 2-part of the sandpile group `K(Q_n)` of the hypercube graph, for every `n ≥ 1`), Theorem DW (the fold law for the folded cube), Corollaries 1.4–1.7, Bai's odd part of `K(Q_n)`, Theorem D, and each of the 68 numbered statements of §2–§10.

It is archived on Zenodo as its own record (software), a supplement to the paper: [doi.org/10.5281/zenodo.23296708](https://doi.org/10.5281/zenodo.23296708) (version 1; all versions: [doi.org/10.5281/zenodo.23296707](https://doi.org/10.5281/zenodo.23296707)).

**Read first:** [lean/CERTIFICADO/LEAN_CERTIFICATE_DANCING_SAND_v1.pdf](CERTIFICADO/LEAN_CERTIFICATE_DANCING_SAND_v1.pdf) ([Markdown](CERTIFICADO/LEAN_CERTIFICATE_DANCING_SAND_v1.md)). It gives:
- the certified statements and every definition they use, exactly as Lean prints them, and a line-by-line comparison with the paper;
- what is **not** formalized (the certificate's §2);
- how the proof is organised, the trust base, the procedure, the data of each of the 68 pieces, a clean rebuild from source, and how to reproduce everything.

## In one line

`MainTheorem.M1` in [`lean/proyecto_cubo/RequestProject/MainTheorem/Theorem.lean`](proyecto_cubo/RequestProject/MainTheorem/Theorem.lean) and `FoldLaw.DW` in [`lean/proyecto_cubo/RequestProject/FoldLaw/PartH.lean`](proyecto_cubo/RequestProject/FoldLaw/PartH.lean) compile with no `sorry` and depend only on the axioms `propext`, `Classical.choice`, `Quot.sound`. Nothing is cited: Lean defines the Laplacian of `Q_n`, its cokernel and the torsion of that cokernel, and proves the theorems themselves.

## Read cold

Before release the certificate was read by a reader other than its writer, with the compiled project at hand. The reader re-read every definition in the statements against the paper, re-elaborated from source the files of the Main Theorem, of Theorem DW and five more of the chain, and compared the rule with Smith forms it computed from the graphs (`n ≤ 11`). Verdict: «holds as far as I can check»; four errors in the record (one sentence and three counts), none in a statement; all corrected in the certificate printed here (its §2 item 7). A second, closed reading checked the corrections.

## Where the evidence is

| What you want to see | File |
|---|---|
| The main results restated by hand, with their axioms, after the clean rebuild | [logs/CheckCubo_postclean.log](../logs/CheckCubo_postclean.log), produced by [lean/proyecto_cubo/checks/CheckCubo.lean](proyecto_cubo/checks/CheckCubo.lean) |
| The statements and definitions printed in the certificate's §1 | [logs/CertCubo.log](../logs/CertCubo.log), by [lean/proyecto_cubo/checks/CertCubo.lean](proyecto_cubo/checks/CertCubo.lean) |
| The dependency cone of each main result | [logs/DepsCubo_postclean.log](../logs/DepsCubo_postclean.log), by [lean/proyecto_cubo/checks/DepsCubo.lean](proyecto_cubo/checks/DepsCubo.lean) |
| The clean rebuild from source: 416 of 416 modules, exit code 0 | [lean/clean_rebuild/clean_rebuild_2026-10-10.log](clean_rebuild/clean_rebuild_2026-10-10.log), by [lean/clean_rebuild/clean_rebuild_cubo.sh](clean_rebuild/clean_rebuild_cubo.sh) over [lean/clean_rebuild/orden_modulos.txt](clean_rebuild/orden_modulos.txt); one log per module in [lean/clean_rebuild/cr_logs/](clean_rebuild/cr_logs/) |
| The md5 of every source file | [lean/clean_rebuild/MANIFEST_md5_416.txt](clean_rebuild/MANIFEST_md5_416.txt) |
| The 68 pieces, exactly as sent to Aristotle | `C*.md` (for example [lean/C33_the_main_theorem.md](C33_the_main_theorem.md)) |
| For each piece: the brute-force check run before sending it, with negative controls, and its log | `chkC<N>.py`, `../logs/chkC<N>.log` |
| For each piece: the Lean file that restates its main statements by hand, and its log | `proyecto_cubo/checks/CheckC<N>.lean`, `../logs/checkC<N>.log` |
| For each piece: the local build | `buildC<N>.sh`, `../logs/buildC<N>*.log` |
| The audit log, piece by piece | [lean/INFORME_ARISTOTLE_CUBO_v1.md](INFORME_ARISTOTLE_CUBO_v1.md) |
| Aristotle's own account of its runs | [lean/proyecto_cubo/ARISTOTLE_SUMMARY.md](proyecto_cubo/ARISTOTLE_SUMMARY.md) |
| The md5 of every file of the Zenodo record (paths relative to its root, which is the root of this repository for `lean/` and `logs/`) | [MANIFEST_md5_zenodo_zip.txt](MANIFEST_md5_zenodo_zip.txt) |

The paths are those of the author's working tree, as the certificate's §8 says; the watchdog under which every run was made (memory and time caps) is [../checks/vigia.sh](../checks/vigia.sh).

## How to check it

You need `elan` (the Lean toolchain manager) and about 7 GB of disk for Mathlib and its dependencies. The toolchain is `leanprover/lean4:v4.28.0` and Mathlib is `v4.28.0`. From `proyecto_cubo/` (in this folder):

```
lake exe cache get
lake build
lake env lean checks/CheckCubo.lean
```

On a machine with little memory, build the modules one at a time, in the order of `clean_rebuild/orden_modulos.txt`, as the author did. A GitHub Actions workflow, [../.github/workflows/lean-build.yml](../.github/workflows/lean-build.yml), runs these three commands on GitHub's machines; it is started by hand from the repository's Actions tab, and a full build takes hours.

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
