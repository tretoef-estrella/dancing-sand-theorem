# Literature sweep for the paper «The Dancing Sand Theorem» — working file (Grepy Bross, started 5 Oct 2026)

Rafa's order (5 Oct): «el barrido A FONDO; le damos a cada César lo que es del César y nosotros nos atribuimos nuestras novedades e innovaciones, y decimos que hasta donde sabemos es así, y que si no es así, que nos lo digan.»
Rule: append-only; every claim read in the original (pdftotext), never from an automatic summary; sources copied to `sources/` with md5; each query logged.
Earlier sweeps this builds on: `notes/BARRIDO_NOVEDAD_TEOREMA_D_v1.md` (4 Oct), the cold reader's §4 (`reports/LECTOR_FRIO_2/delivered_2026-10-05/REPORT_COLD.md`), `notes/BAI_2003_READING_v1.md`.

## 0. The claims of the paper, one per row (what we would call ours)

## 1. Query log

## 2. Sources read in the original (new this turn)

## 3. Verdict per claim (ours / others' / shared)

## 4. The sentence for the paper (priority and invitation to correct us)

## 5. What was not searched and why

---
### §0 (filled 5 Oct, ~09:30) The claims
- **C1 Main Theorem (Dancing Sand):** the whole Syl₂K(Q_n), every n, by an explicit rule (Theorem D + Theorems O, U, F + the integer antitonic fit).
- **C2 Theorem D (the method):** an integral 2-adic tilting decomposition of the sandpile group (SL₂, char 2): Syl₂K(Q_n) ⊕ Z₂ = ⊕ X(λ, i)^{m_λ(n)}, each X(λ, i) read off a 2^|I| × 2^|I| matrix M(λ, i).
- **C3 Corollaries:** Gao et al. Conj. 4.14; the JMM 2019 poster's (n+1)-th factor; Gao et al. Conj. 5.4 for every k.
- **C4 The fold law (dry and wet):** Syl₂K̄(n) ≅ 2·Syl₂K(Q_n), every n; with C1 it gives **the whole 2-part of the folded cube**, and with Gao et al. Prop. 1.9 (odd part) **the whole critical group of the folded cube**.
- **C5 Mod-2 layer of C4:** answers Gao et al. Remark 2.13 (the «coincidence» a_n = F₂-rank count of the folded cube) by a structural law.
- **C6 Proof techniques:** formal dance (doblar/paso Schur complements /2); the class 𝒦 = {a + 2χ(2y)} with the shift-invariant ring map Θ (Theorem C); rigidity (Theorem R: Lemmas IB, PS, H); Lemma B (window bound); continuity at shift 0.
- **C7 Data/negative facts:** the non-antipodal fold Q_n/⟨x₁x₂⟩ does NOT double (reader 2, n = 3..12); flight 7: the half structure breaks; R_gen and PL* false.
- **Not claimed (measured only):** the turned lid / swap symmetry (n ≤ 12).

### §1 Query log (5 Oct)
1. arXiv export API, 7 queries — answered 503 / «Rate exceeded»; abandoned (no result).
2. Web (extended) «critical group of the hypercube Sylow 2-subgroup determined 2025» → Gao et al. (Comm. Algebra 2024), Anzis–Prasad; nothing newer on the whole 2-part.
3. Web (extended) «critical group sandpile group of the folded hypercube folded cube Smith normal form» → Stanley SNF survey, Bai, Sin's pages, Tamimi thesis (Essex 2022), k-partite (2409.02654); no folded cube.
4. Web (extended) «Jacobian of a double cover … Prym … multiplication by 2» → Len–Zakharov (Prym groups: ORDERS only), Len 2210.14060 (survey), Ghosh–Zakharov 2303.03904.
5. Web (extended) «arXiv sandpile group hypercube 2-part 2025 2026» → nothing new on the cube.
6. Web (extended) «"Sandpile groups of Cayley graphs" … conjecture 4.14 5.4 proved» → only Gao et al. themselves (their Thm 1.2, an earlier conjecture, proved in their v3). No proof of 4.14 or 5.4 by others found.
7. Web «Kirchhoff's theorem for Prym varieties …» → Len–Zakharov, Forum Math. Sigma 10 (2022).
8. Yuen's research page (fetched): no newer sandpile paper.
9. Semantic Scholar citation trees (API, today) of 1912.06919 (3), 1511.00272 (13), 1301.2977 (24, incl. 2026 papers), 2301.02517 (1), 2202.02821 (8), 2310.09227 (3), 2012.15235 (15). Candidates downloaded and read (below).
10. Web (extended) «tilting modules Smith normal form … graph Laplacian» → Larsen (have), Selecta 2023 (tilting SL₂ mixed case, not graphs), Lorenzini «Smith normal form and Laplacians»; **no tilting decomposition of a sandpile group.**
11. Web (extended) «Smith normal form Laplacian hypercube Krawtchouk 2-adic …» → CSX, Ducey–Hill–Sin (Kneser), Ducey–Jalil; nothing new.
12. Web «"folded cube" OR "folded hypercube" spanning trees / critical group / Jacobian» → OEIS A193134 (spanning tree counts of folded cubes; no group), interconnection-network papers on «folded hypercubes» (independent spanning trees, automorphisms 1103.4351).
13. Web (extended) «"folded cube" distance-regular Smith normal form / critical group / Smith group» → nothing on the folded cube.
14. OEIS A193134 fetched: «Numbers of spanning trees of the folded cube graphs», no comment on the group.

### §2 Sources read in the original this turn (pdftotext; md5 in `sources/MANIFEST_md5.txt`)
- **Vetluzhskikh–Zakharov, arXiv:2409.04629 (2024), «Critical groups in harmonic abelian quotients».** Abstract l. 10–17, Thm 1.1 (l. 95): the ORDER of ker(p_*: Jac(X̃) → Jac(X)) for abelian Galois covers, via Zaslavsky's bias matroid. Orders, not group structure; no cube. **Cite as context** (the pushforward is surjective; orders of kernels).
- **Akyar–…–Terekhov, arXiv:2609.10625 (9 Sep 2026), «The 2-adic valuation of the order of the all-ones class in the sandpile group of a square».** Grids, not cubes. Its §4 (l. 532–567): «Can one determine the full 2-primary Smith form …?»; and on Reiner–Tseng: «This makes the prime 2 a natural place to look for additional structure under an involution … Can an analogous integral description … explain … the remaining 2-primary factors?» **Contemporary statement of exactly the kind of question the fold law answers (for the cube's antipode). Cite.**
- **Cho–Dochtermann–Inagaki–Oh–Snustad–Zacovic, arXiv:2306.09315 (2024), signed graphs.** Critical groups of signed cycles, wheels, complete graphs, fans. No cube, no fold. Context for K(G±) of Reiner–Tseng.
- **Len–Zakharov, arXiv:2012.15235 (Forum Math. Sigma 10, 2022), Kirchhoff for Prym.** Order of the Prym group of a free double cover. Orders only. Context.
- **Len, arXiv:2210.14060 (survey), Ghosh–Zakharov 2303.03904, Meyer–Zakharov 2307.03348:** tropical/Prym context; no group-structure statement of our kind.
- **Agarwal–Gaetz, arXiv:1710.08253:** critical groups of representations; abelian case = Cayley graphs; restriction = covering. Not our object.
- **Hung–Yuen 2203.11384; Batal 2609.12546 (Kneser, 2026):** other graphs.
- **Iga–Klivans–Kostiuk–Yuen, arXiv:2202.02821 (in sources since 4 Oct), §7 l. 1293–1345:** Cayley graphs of F₂^r = quotients of cubes by codes (Prop. 37); for these «the 2-Sylow subgroup of their critical groups, or even just the 2-rank of the Laplacians, has been rather difficult to understand». Adinkras are SIGNED graphs; their K is of the signed Laplacian. **The folded cube (1 ∈ C) is the «non-generic» case.**
- **Yuen, arXiv:2301.02517, l. 205–216:** non-generic = 1 ∈ C = «precisely the Cayley graphs on F₂^n whose 2-rank drops below 2^{n−1}».
- **Gao et al. v3, l. 516–545:** every non-generic Cayley graph of F₂^r is built from Q_n/⟨1⟩ (= the folded cube) by successive codimension-one quotients; Prop. 2.12 gives only the F₂-rank of the folded cube. **Prop. 1.9 (l. 220):** the odd part of K of every Cayley graph of F₂^r is the diagonal of its eigenvalues.
- **Ducey–Jalil, arXiv:1308.2335 (LAA 445, 2014), l. 307–308:** «In general, the full structure of the 2-primary component of both the critical group and the Smith group of the n-cube remain unknown.» (One more «open» quote.)
- **Ducey–Hill–Sin, arXiv:1707.09115:** Kneser graph KG(n, 2); Specht-module method at p = 2. Different graph; nearest «representation theory at p = 2 computes a critical group» precedent, with CSX.
- **Naming trap, declared:** in the interconnection-network literature «folded hypercube FQ_n» is Q_n plus the antipodal matching (2^n vertices); our folded n-cube K̄(n) is Q_n/⟨1⟩ = FQ_{n−1} (2^{n−1} vertices). The paper must say both names.

### §1 (cont.) Queries 15–17
15. Web (extended) «isotonic regression pool adjacent violators Smith normal form …» → only statistics/PAVA literature; **no use of PAVA to compute a Smith form found.**
16. Web «ring of 2-adic analytic functions a + 2f(2y) shift invariant … Mahler» → T-functions (Anashin), Mahler coefficients of the 2-adic shift, Iwasawa analytic functions; **standard p-adic analysis, nothing resembling Theorem C (a shift-invariant reduction Θ killing Schur complements of divided-power operators).**
17. Web «Iwasawa theory graph Jacobians Z_2 tower …» → Gonet, Vallières and others (2106.11221, 2405.12909, 2410.11704, 2504.09236): p-parts of Jacobians in Z_p^d-towers of voltage covers. The cubes Q_n are not such a tower (their Galois groups are elementary abelian); not applicable, cite at most as context.

### §3 Verdict per claim (5 Oct 2026)
| claim | verdict | to whom the credit goes |
|---|---|---|
| **C1** whole Syl₂K(Q_n), every n | **OURS** to the best of our knowledge. Stated as open by Reiner (2001 conjectures, REU poster «remains a mystery»), Bai 2003 («still unknown», p. 253), Ducey–Jalil 2014 («remain unknown»), Chandler–Sin–Xiang 2017 («we do not have any conjecture»), Iga et al. 2022 («rather difficult»), Yuen 2023 («remains open»), Gao et al. 2024 (state of the art: top n factors). No later solution found through Sep 2026. | Bai (odd part, a_n, number of factors, integrality of L(L+2)/2); Gao et al. (top factors, Prop. 1.9, the change of variables u_i = x_i − 1); CSX (two-row machinery, adjacency case); Anzis–Prasad (bounds). |
| **C2** tilting decomposition of a sandpile group (Theorem D) | **OURS** as a method, to the best of our knowledge: no tilting decomposition of any sandpile group found (now also checked in the 2024–2026 literature). | Tilting theory of SL₂ (Donkin 1993 tensor products; Jantzen; Tubbenhauer–Wedrich characters; Larsen 2024 fusion at p = 2); Bier 1993; Kostant's formula; the «small matrices» spirit of Ducey et al. 2023 (Johnson scheme) and Wilson; representation-theoretic Smith-group computations of Sin's school (CSX, Ducey–Hill–Sin). |
| **C3** Gao et al. Conj. 4.14, 5.4 and the poster's (n+1)-th factor | **OURS**: proved; no other proof found. | The conjectures are Gao–Marx-Kuo–McDonald–Yuen's (and the JMM 2019 poster's). |
| **C4** fold law; whole 2-part and whole critical group of the folded cube | **OURS** to the best of our knowledge (no statement found; the folded cube's critical group was not computed anywhere found; OEIS A193134 has only its spanning-tree counts). | Reiner–Tseng (the surjection / exact sequence for double covers; non-splitting at 2); Gao et al. Prop. 1.9 (odd part), Prop. 2.12 (F₂-rank of the folded cube), Remark 2.13 (the question); Iga et al. / Yuen (Cayley graphs of F₂^r as quotients of cubes; the non-generic case). Contemporary: Akyar et al. (Sep 2026) ask for an integral 2-primary description under an involution for grids. |
| **C5** the mod-2 layer explains Gao Remark 2.13 | **OURS** (the «deeper connection» they asked for, for the antipodal quotient); with the reader's negative data point that a non-antipodal fold does not double. | Gao et al. for the question and the two numbers; Bai for a_n. |
| **C6** techniques: formal dance, class 𝒦 and Θ (Theorem C), rigidity (Theorem R), Lemma B, PAVA in Smith forms | **OURS** as combinations; each ingredient standard and credited. | Strassmann; Mahler/Amice-type 2-adic analytic functions; Legendre (v(m!)); von Staudt–Clausen (the tanh/coth weights); Kummer; PAVA (Ayer–Brunk–Ewing–Reid–Silverman 1955); block-inverse and Schur-complement identities. |
| **C7** negative facts (non-antipodal fold, half structure, R_gen, PL*) | ours, as data | — |

### §4 The sentence for the paper (draft)
«To the best of our knowledge, after a search of the literature up to October 2026 (the sources and queries are listed in the repository), the results of this paper are new: the 2-part of K(Q_n) was stated as open by Bai [2003], Ducey–Jalil [2014], Chandler–Sin–Xiang [2017], Iga–Klivans–Kostiuk–Yuen [2022], Yuen [2023] and Gao–Marx-Kuo–McDonald–Yuen [2024]; Conjectures 4.14 and 5.4 of the last paper had not been proved; and we found no earlier statement of the fold law, nor of the critical group of the folded cube. Every ingredient we did not invent is credited where it is used. If a result here was obtained earlier, we would be grateful to be told, and we will correct the record.»

### §5 What was not searched, and why
- **Google Scholar and MathSciNet:** not reachable from scripts (Scholar blocks them; MathSciNet needs a subscription). A manual Scholar check by Rafa of the three citation trees (Bai 2003, CSX 2017, Gao et al. 2024) would close the gap.
- **Theses and REU reports after 2019** beyond Anzis–Prasad and Tamimi (Essex 2022, seen only as a title): not read.
- **Non-English literature:** not searched.
- The arXiv API was rate-limited today; its search was replaced by web search plus citation trees.

## §6 Google Scholar, done by hand in Rafa's Chrome (2026-10-05 09:23)

Rafa kept a Chrome window open and solved two captchas; the auditor read the pages. Scholar blocked plain URL navigation twice; clicking links and typing in the search box worked.

- **Bai 2003, «On the critical group of the n-cube»:** cited by 48. Since 2024, five:
  - Reiner–Smith, «Sandpile groups for cones over trees» (Res. Math. Sci. 2024);
  - Assem–Derets–Nehaniv, «Observations on Abelian sandpile models for directed graphs» (ERA 2025);
  - Dong–Jiang–Guo, «On the critical group of the k-partite graph» (arXiv:2409.02654);
  - Gao–Marx-Kuo–McDonald–Yuen (2024, already read);
  - Martinian–Vindas-Meléndez, «On the critical group of hinge graphs» (Rocky Mountain J. Math. 2026).

  None is about the 2-part of K(Q_n); the four new ones are other graphs.
- **Gao et al. 2024:** cited by 1 — Yuen arXiv:2301.02517 (already read). Yuen 2023 is cited by 1 — Gao et al. (closed loop).
- **Chandler–Sin–Xiang 2017:** cited by 9, all up to 2024:
  - Wang 2021, 2023 (walk matrices);
  - Iga–Klivans–Kostiuk–Yuen 2023;
  - Ducey et al. 2023;
  - Alfaro–Barrus–Sinkovic 2021;
  - Gao et al. 2024;
  - Anzis–Prasad 2016;
  - Villagrán Olivas (thesis, 2021);
  - Li 2020.

  Nothing new on the cube.
- **Free query** `"critical group" OR "sandpile group" hypercube "Sylow 2"`: 5 results in all years (Bai, the Gao poster, Gao et al., Alfaro–Valencia 2012 and its 2010 preprint on the cone of the hypercube). Nothing after 2024.
- **Broad query** (hypercube + sandpile/critical/Smith group/Smith normal form + Laplacian, top 20 by relevance): nothing on the 2-part of K(Q_n) after 2024.
  - Not in our sources, to be noted: Jalan 2019 «The Structure of the Sandpile Group» (expository notes, akhiljalan.github.io); Alfaro–Valencia (cone of the hypercube, a different graph); Sherwood (honors project, representation theory of S_n on the hypercube).
  - Chhetri et al. 2025 and Rigobert et al. 2026 are other objects.

**Verdict of §6:** the gap of §5 for Scholar is CLOSED. No paper of 2025 or 2026 on the 2-part of the hypercube's critical group was found. The novelty sentence of §4 stands. MathSciNet remains unchecked (subscription).
