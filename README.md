# The Dancing Sand Theorem

### The 2-part of the sandpile group of the hypercube, for every n

[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.23188298-blue.svg)](https://doi.org/10.5281/zenodo.23188298) [![Lean certificate DOI](https://img.shields.io/badge/Lean_certificate_DOI-10.5281%2Fzenodo.23296707-blue.svg)](https://doi.org/10.5281/zenodo.23296707) [![Lean build](https://github.com/tretoef-estrella/dancing-sand-theorem/actions/workflows/lean-build.yml/badge.svg)](https://github.com/tretoef-estrella/dancing-sand-theorem/actions/workflows/lean-build.yml)

**Rafael Amichis Luengo** · Madrid · tretoef@gmail.com · preprint, version 10, 11 October 2026

> **Status.** A complete proof, published as a preprint. Every step has a written proof that can be checked with pencil and paper; no step uses a computer. Before release the proofs were re-derived by auditors who had not written them, and there were thirteen cold readings — two of the chains of proof, nine of the text, one of the Lean certificate, and one of the last changes of the text and of the certificate — by readers who had not watched it being written: AI systems, all of them instances of Claude. One gap was found, in the first version of the text, and repaired; no theorem was affected ([record/](record/README.md)). **The whole proof has also been checked in the proof assistant Lean 4, with nothing cited** ([below](#formal-verification-in-lean-4)), **and GitHub's own machines have built that Lean proof from the published files** ([Lean build](https://github.com/tretoef-estrella/dancing-sand-theorem/actions/workflows/lean-build.yml)). **It has not been refereed by a human expert.**

**Read the paper:** [paper/THE_DANCING_SAND_THEOREM_v10.pdf](paper/THE_DANCING_SAND_THEOREM_v10.pdf) · [Markdown source](paper/THE_DANCING_SAND_THEOREM_v10.md) · permanent archive: [doi.org/10.5281/zenodo.23188298](https://doi.org/10.5281/zenodo.23188298) (this version: [doi.org/10.5281/zenodo.23298437](https://doi.org/10.5281/zenodo.23298437)) · **Lean certificate:** [lean/](lean/README.md), [doi.org/10.5281/zenodo.23296707](https://doi.org/10.5281/zenodo.23296707)

---

## The question

Put grains of sand on the corners of the `n`-dimensional cube `Q_n`. A corner holding as many grains as it has neighbours topples and gives one grain to each neighbour; one corner is a sink that swallows what falls into it. The stable configurations that keep coming back form a finite abelian group: the **sandpile group** `K(Q_n)` of the cube, also called its critical group or Jacobian. Its order is the number of spanning trees of the cube, `2^{2^n − n − 1} ∏_{j=1}^{n} j^{C(n,j)}`.

In 2003 Hua Bai determined every odd part of this group, proving two conjectures of Victor Reiner on the way. About the prime `2` he wrote: «The full structure of the Sylow-2 subgroup of the critical group of the `n`-cube is still unknown» (*Linear Algebra Appl.* 369 (2003), p. 253). The question stayed open:
- Ducey and Jalil (2014): «the full structure of the 2-primary component of both the critical group and the Smith group of the `n`-cube remain unknown»;
- Chandler, Sin and Xiang (2017): «only the 2-Sylow subgroup of the critical group remains to be determined … We do not have any conjecture about its exact structure»;
- Marx-Kuo, Gao and McDonald, poster (2019): «the Sylow-2 subgroup remains a mystery»;
- Gao, Marx-Kuo, McDonald and Yuen (*Comm. Algebra*, 2024) determined the `n − 1` largest cyclic factors, conjectured the next ones, and wrote that «determining the complete structure still seems out of reach at this moment».

## The answer

> **Main Theorem (the Dancing Sand Theorem).** For every `n ≥ 1`, the 2-part of `K(Q_n)` is given by an explicit rule: as `ℤ_2`-modules,
> `Syl_2 K(Q_n) ⊕ ℤ_2 ≅ ⊕_{1 ≤ λ ≤ n, λ ≡ n (mod 2)} X(λ, (n − λ)/2)^{m_λ(n)}`.

Each family `λ` contributes a group `X(λ, i)` made of explicit small cyclic factors and `2^{|I|}` large ones, where `I` is the set of binary digits of `λ + 1` below the leading one. The large ones are explicit integers — sums of 2-adic valuations of binomial coefficients and counts of binary carries — pooled into a non-increasing sequence in the manner of isotonic regression. The multiplicities `m_λ(n)` follow from a three-line recursion. The right-hand side is a finite computation with binomial valuations; no Smith form is needed, and `n = 1024` takes seconds. The rule is stated in full in §1.2 of the paper, with a worked example (`n = 6`, the smallest cube in which the pooling acts).

> **Theorem DW (the fold law, «dry and wet»).** For every `n ≥ 1`, the 2-part of the sandpile group of the folded cube `Q_n/⟨(1,…,1)⟩` is `2·Syl_2 K(Q_n)`: the group of the cube with every exponent lowered by one, and its `a_n = 2^{n−2} − 2^{⌊(n−2)/2⌋}` factors `ℤ/2` gone.

With the known odd part this gives the whole sandpile group of the folded cube (Corollary 1.4), which we found computed nowhere. The fold law also explains a coincidence that Gao et al. had noticed and left open («We are not sure if that is a coincident, or a special case of some deeper connection», Remark 2.13).

**The first values,** computed by the rule and checked against the 2-adic Smith form of the Laplacian computed directly (exponents `e: c` mean `(ℤ/2^e)^c`; log: [checks/logs/gate_direct_11.log](checks/logs/gate_direct_11.log)):

| `n` | `Syl_2 K(Q_n)` | `Syl_2 K(Q_n/⟨𝟙⟩)` |
|---|---|---|
| 2 | `{2: 1}` | `{1: 1}` |
| 3 | `{1: 1, 3: 2}` | `{2: 2}` |
| 4 | `{1: 2, 3: 4, 5: 1}` | `{2: 4, 4: 1}` |
| 5 | `{1: 6, 3: 4, 4: 1, 6: 4}` | `{2: 4, 3: 1, 5: 4}` |
| 6 | `{1: 12, 2: 4, 3: 1, 5: 4, 6: 10}` | `{1: 4, 2: 1, 4: 4, 5: 10}` |
| 7 | `{1: 28, 2: 1, 4: 8, 5: 6, 6: 14, 7: 6}` | `{1: 1, 3: 8, 4: 6, 5: 14, 6: 6}` |
| 8 | `{1: 56, 2: 2, 4: 16, 5: 12, 6: 28, 7: 12, 10: 1}` | `{1: 2, 3: 16, 4: 12, 5: 28, 6: 12, 9: 1}` |
| 9 | `{1: 120, 2: 10, 4: 16, 5: 26, 6: 48, 7: 26, 9: 1, 11: 8}` | `{1: 10, 3: 16, 4: 26, 5: 48, 6: 26, 8: 1, 10: 8}` |
| 10 | `{1: 240, 2: 36, 3: 26, 5: 16, 6: 148, 8: 1, 10: 26, 11: 18}` | `{1: 36, 2: 26, 4: 16, 5: 148, 7: 1, 9: 26, 10: 18}` |
| 11 | `{1: 496, 2: 66, 3: 32, 4: 100, 6: 164, 7: 1, 9: 100, 11: 64}` | `{1: 66, 2: 32, 3: 100, 5: 164, 6: 1, 8: 100, 10: 64}` |

**In plain words.** Write the sandpile group inside the group ring of `(ℤ/2)^n`: there the Laplacian becomes an element of the algebra of `SL_2`, and the cube becomes the `n`-th tensor power of the natural two-dimensional module. At the prime `2` that tensor power breaks into indecomposable pieces — tilting modules — and the group breaks with it, one piece at a time. Each piece is built from the trivial module by reading the binary digits of `λ + 1` from the bottom: at a digit `0` the piece is doubled, at a digit `1` it is doubled and every «dancer» splits into two partners. Eliminating the unit pivots at each step leaves, at the end, a small triangular matrix indexed by the dancers. Its Smith form is the hard part: an upper bound from a unique cheapest matching, a lower bound from a potential built digit by digit, and the two meet exactly at the pooled clocks. The fold law is the same dance performed on the folded cube: the antipodal involution acts on every piece as `±exp(F)`, and after the dance the group of each folded piece is exactly twice the group of the unfolded one.

| | Statement | Status |
|---|---|---|
| **Main Theorem** | the whole 2-part of `K(Q_n)`, every `n`, by an explicit rule | proved; read cold; in Lean |
| **Theorem D** | each family contributes small clocks plus the cokernel of `2^k M`, with `M` an explicit `2^{|I|} × 2^{|I|}` integer matrix | proved; read cold; in Lean |
| **Theorems O and F** | the Smith form of `M` is the pooled sequence of clocks (unique cheapest matching for the ceiling, a potential for the floor) | proved; read cold; in Lean |
| **Theorem DW** | the fold law, `Syl_2 K(Q_n/⟨𝟙⟩) ≅ 2·Syl_2 K(Q_n)` | proved; read cold; in Lean |
| **Corollary 1.4** | the whole sandpile group of the folded cube | proved; in Lean |
| **Corollary 1.5** | Bai's two counts (Reiner's conjectures), re-proved from the rule | re-proof of a known result; in Lean |
| **Corollary 1.6** | the `n + 1` largest cyclic factors: Gao et al.'s Theorems 4.1–4.2 (known), **their Conjecture 4.14, and the `(n+1)`-th factor of the 2019 poster** | the conjectures are new proofs; in Lean |
| **Corollary 1.7** | `Syl_2 K(Q_{2^e}) ≅ Syl_2 K(Q_{2^e−1})^2 ⊕ ℤ/2^{2^e+e−1}`: **Gao et al.'s Conjecture 5.4** | new proof; in Lean |

«In Lean»: checked in Lean 4 with Mathlib, for every `n` for which the paper states the result. A guided tour of these results, with the lemmas a referee should look at first and their Lean names, is in **[THEOREMS.md](THEOREMS.md)**.

---

## For a referee: how to check this

1. **Read, in this order:** §1.0 (the summary table) and §1.2 (the rule) → §2–§3 (the group ring as an `SL_2`-module, and the family decomposition) → §4 (the dance, Theorem D) → §5–§7 (valuations; Theorem O, the ceiling; Theorem F, the floor) → §8 (assembly) → §10 (the fold law) → §13 (exact status).
2. **Press where it is most likely to break:** [WHERE_TO_ATTACK.md](WHERE_TO_ATTACK.md) names the load-bearing joints, in the order we would attack them, and says where the one gap of the first version was.
3. **Run the checks:** [HOW_TO_VERIFY.md](HOW_TO_VERIFY.md). Every check of §12.1 of the paper is in [checks/](checks/README.md), runs on a laptop in seconds or minutes, and has, where the paper says so, a deliberately wrong variant that must fail.
4. **Check the Lean:** [lean/](lean/README.md) — the certificate first, then the hand restatements in `CheckCubo2.lean` and their log.
5. **Read the record of the checking:** [record/](record/README.md) holds the thirteen cold readings (each with its mission, its report, its own code and logs, and the author's grading), the nine flights in which the proofs were found and the audit of each, the list of corrections of every version, and the literature search.
6. **What is NOT done:** no human referee. The texts of the readings are by AI readers; their code is their own.

---

## Formal verification in Lean 4

**Every theorem of the paper has been checked in the proof assistant Lean 4, with the Mathlib library, with nothing cited.** Lean defines the Laplacian of `Q_n`, its cokernel and the torsion of that cokernel, and proves the theorems themselves; Kirchhoff's theorem is not used. The proof has no `sorry`, and every theorem depends only on the three standard axioms `propext`, `Classical.choice` and `Quot.sound`.

- **What Lean proves:** the Main Theorem (`MainTheorem.M1`), Theorem DW (`FoldLaw.DW`) and its equivalent form (`SmallCases.DW'_all`), Corollaries 1.4–1.7, Bai's odd part of `K(Q_n)`, Theorem D, and each of the 68 numbered statements of §2–§10 of the paper: every theorem, for every `n` for which the paper states it.
- **The one point of trust** is that the Lean definitions say what the paper says. The **[Lean certificate](lean/CERTIFICADO/LEAN_CERTIFICATE_DANCING_SAND_v2.pdf)** prints every definition the statements use, exactly as Lean prints it, and compares it with the paper line by line. That comparison is what a reader should check.
- **How it was done:** the text of the paper was cut into 68 pieces, each a short self-contained file; a 69th piece added the small cases (`n = 1`, and `n = 2` for Gao et al.'s Theorem 4.1). Aristotle (Harmonic) wrote the Lean proofs, one piece at a time. Every returned project was compiled again on the author's machine, and the main statements of each piece were restated by hand and audited against the paper. At the end of the 68 pieces all 416 modules were rebuilt from source, all with exit code 0; the four modules of the 69th piece were then compiled from their sources, with the sources of the other 416 unchanged. The project has 420 Lean files, 61 285 lines and 3 470 theorem and lemma declarations.
- **Read cold:** before release, a reader other than the writer of the certificate, with the compiled project at hand, re-read every definition against the paper, re-elaborated the files of the Main Theorem, of Theorem DW and five more, and compared the rule with Smith forms computed from the graphs. Verdict: «holds as far as I can check»; four errors in the record and none in a statement, all corrected ([reading 11](record/cold-readings/11-lean-certificate/REPORT.md)). The changes of version 2 of the certificate were read cold in their turn, with the Lean of the 69th piece: right, faithful and clean; nine points of wording and presentation, all corrected ([reading 13](record/cold-readings/13-lean-v2-and-paper-v10/REPORT.md)).
- **Where:** [lean/](lean/README.md) holds the certificate, the Lean project, the 69 pieces as sent, the brute-force check run before sending each piece, the build scripts, the audit log and the clean rebuild, each in its own folder; [logs/](logs/README.md) holds the log of every piece and of the final checks. The same files are archived on Zenodo: [doi.org/10.5281/zenodo.23296707](https://doi.org/10.5281/zenodo.23296707) (this version: [doi.org/10.5281/zenodo.23298436](https://doi.org/10.5281/zenodo.23298436)).
- **Check it yourself:** from `lean/proyecto_cubo/`, run `lake exe cache get`, `lake build` and `lake env lean checks/CheckCubo2.lean`. The workflow [lean-build.yml](.github/workflows/lean-build.yml) does the same on GitHub's machines, from the files as published; it is started by hand from the Actions tab. Its run of 11 October 2026, on commit `f6d95a4`, built the 420 modules from source in 21 minutes and passed the hand restatements and the check «no `sorry`, no axiom beyond the three standard ones», 24 minutes in all ([run 38172080438](https://github.com/tretoef-estrella/dancing-sand-theorem/actions/runs/38172080438); its output is kept in [logs/actions/](logs/actions/README.md), because GitHub deletes run logs after 90 days). The badge at the top of this page shows the result of its latest run.

The paper's own proof of the family decomposition does not cite the theory of tilting modules either: it proves it from an elementary lifting lemma for `SL_2` over `ℤ_2` (§3.2). Besides that, the written proof uses only classical results (Weyl's theorem on complete reducibility over `ℚ`, Kostant's `ℤ`-form of `U(sl_2)`, Kummer's theorem, Legendre's formula, the von Staudt–Clausen theorem, Strassmann's theorem), and in Lean each of them is either proved or taken from Mathlib, where it is proved too.

---

## Literature and priority

Before release we searched the literature in depth and honestly: arXiv and journal searches, the citation trees of Bai (2003), Chandler–Sin–Xiang (2017) and Gao et al. (2024) in Google Scholar and Semantic Scholar, and every source cited in the paper, read in the original (MathSciNet was not searched). The query log and the verdict per claim are in [record/literature/](record/literature/LITERATURE_SWEEP.md).

**As far as we know, these are new:** the whole 2-part of `K(Q_n)` for every `n`; the decomposition of a sandpile group over tilting modules, with the reduction of each piece to a small explicit matrix; proofs of Gao et al.'s Conjectures 4.14 and 5.4 and of the `(n+1)`-th factor of the 2019 poster; the fold law and the sandpile group of the folded cube; and the proof techniques of §4–§7 and §10 as combinations. **What is not ours** is credited in §1.8 of the paper: Bai's odd part and counts; Gao et al.'s largest factors, change of variables and Table 1; Chandler–Sin–Xiang's monomial basis for the Smith group; the tilting multiplicities (Donkin, Larsen, Tubbenhauer–Wedrich); the classical tools (Kummer, Legendre, von Staudt–Clausen, Strassmann, pool-adjacent-violators).

**If a result here was obtained earlier, we would be grateful to be told, and we will correct the record.**

---

## How it was made

The work began as a search for an open problem within reach, inside another project of the author. It was carried out by separate instances of Claude, Anthropic's AI, in separate roles under the author's direction: constructors who found and wrote proofs, each from a written mission («flights» 1 to 9); auditors who re-derived every step in their own words and ran their own engines; and cold readers who read the chains and then the text with no access to the audits. Several decisive ideas started as everyday images given by the author and translated into mathematics. The story, with the dead ends and the failed predictions, is in **[THE_STORY_AND_THE_NUMBERS.md](THE_STORY_AND_THE_NUMBERS.md)**.

The author asked four AIs, Claude among them, whether this problem could be solved this way. The question, their answers word for word, and the view of the last auditor are in **[A_PERSONAL_NOTE.md](A_PERSONAL_NOTE.md)**.

---

## Repository map

```
paper/                    the paper, version 10 (PDF and Markdown source);
                          earlier-versions/  the Markdown of versions 1 to 9
lean/                     the Lean 4 proof: the certificate (CERTIFICADO/), the project (proyecto_cubo/),
                          the 69 pieces (pieces/), their brute-force checks (brute_force/), the build scripts (build/),
                          the audit log (audit/), the clean rebuild (clean_rebuild/)
logs/                     the logs of every Lean piece and of the final checks, in four folders
.github/workflows/        the Lean build on GitHub's machines (started by hand; 24 minutes, green on 11 Oct 2026)
checks/                   the folder gate/ of §12.1, with the watchdog and the logs of one complete run
record/cold-readings/     the thirteen cold readings: mission, report, the reader's own code and logs, grading
record/flights/           the nine missions in which the proofs were found, their reports and their audits
record/corrections/       what changed from each version to the next, with its source
record/literature/        the literature search, the novelty sweep for Theorem D, Bai (2003) read in the original
THEOREMS.md               a guided tour of the results
HOW_TO_VERIFY.md          how to run the checks, and which number of the paper each one certifies
WHERE_TO_ATTACK.md        the load-bearing joints of the proof
```

**Related work by the author.** [The Chaise Longue Theorem](https://github.com/tretoef-estrella/chaise-longue-theorem) (Conjecture 1.2 of Degtyarev–Shimada for the Fermat varieties of every degree in every even dimension) and [The Watermark Theorem](https://github.com/tretoef-estrella/watermark-theorem). The sandpile group of the cube is the group ring of `(ℤ/2)^n` modulo one element, at the prime `2`: the degree-2 member of the family of group rings studied in the Chaise Longue.

---

[CITATION.md](CITATION.md) · [LICENSE-TEXT.md](LICENSE-TEXT.md) · [ACKNOWLEDGEMENTS.md](ACKNOWLEDGEMENTS.md) · [THE_STORY_AND_THE_NUMBERS.md](THE_STORY_AND_THE_NUMBERS.md) · [A_PERSONAL_NOTE.md](A_PERSONAL_NOTE.md)

*Cite as:* Amichis Luengo, R. (2026). *The Dancing Sand Theorem — the 2-part of the sandpile group of the hypercube, for every n* (preprint, version 10). Zenodo. https://doi.org/10.5281/zenodo.23188298
