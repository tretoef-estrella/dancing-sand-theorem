# Novelty sweep of Theorem D — working file (Grepy Hypercube). STARTED 4 Oct 2026, morning; Rafa's OK: «Sí, empieza el barrido del Teorema D».

**Rule:** append-only; every claim with its source read in the original (`pdftotext`, never an automatic summary); copies of sources in `sources/` with md5.

## 0. What Theorem D says (flight 2, audited)
Syl₂ K(Q_n) = ⊕ over tilting families λ of V^{⊗n} (SL₂, characteristic 2), with multiplicity m_λ(n), of:
- the small clocks; plus
- the 2-adic Smith form of an explicit 2^|I| × 2^|I| matrix M(λ, i), with i = (n − λ)/2.

As a tool: an integral 2-adic tilting decomposition of the sandpile group (of the Laplacian as an element of the integral sl₂-structure of the Boolean lattice).

## 1. Questions to answer
1. Has anyone decomposed a sandpile / critical group (of any graph) through the tilting modules of a reductive group in positive characteristic?
2. Has anyone computed the 2-adic Smith form of an operator of the Boolean lattice (U + 2D, inclusion matrices, Terwilliger algebra of Q_n) over Z_2 through Weyl or tilting filtrations?
3. Is the Smith form of the Laplacian (resp. the Smith group of Q_n) known from such a decomposition?
4. Does the fusion recursion m_λ(n) coincide with the tilting decomposition of V^{⊗n} in char 2 (Doty–Henke math/0205186, Donkin, Erdmann)?

## 2. Search plan (keywords)
- «Terwilliger algebra hypercube» integral / Smith normal form;
- «Krawtchouk» 2-adic, «Krawtchouk matrix Smith normal form»;
- «tilting module» sandpile, «tilting» «critical group»;
- «inclusion matrices Smith normal form» Wilson, Bier;
- «Boolean lattice» sl2 integral / «up and down operators» Smith;
- «Smith group» hypercube (Ducey, Jazaeri, Sin);
- Chandler–Sin–Xiang (critical groups of some graphs via representation theory; its citations);
- the citations of Gao et al. 2024 (Google Scholar / Semantic Scholar);
- Reiner's REU 2016 problem list; Anzis–Prasad.

## 3. Log (append below, newest last)

### Entry 1 — 2026-10-04 09:0x (Grepy Hypercube)
Web searches (extended): «sandpile critical group tilting modules positive characteristic»; «critical group hypercube Sylow 2 Smith normal form representation theory Boolean lattice»; «Krawtchouk matrix Smith normal form 2-adic hypercube»; «Terwilliger algebra hypercube integral Smith normal form».
Downloaded to sources/ and read with pdftotext:
- Grinberg–Huang–Reiner, «Critical groups for Hopf algebra modules», arXiv:1704.03778. Critical groups of MODULES (McKay-type, Brauer characters, modular reps of finite groups/Hopf algebras). Does NOT treat K(Q_n) nor tilting modules of SL_2. Different object: there the group is built from a representation; ours decomposes the Laplacian of a graph along tilting summands. No overlap found.
- Anzis–Prasad, REU 2016 (Reiner): line 34 «the determination of the 2-Sylow subgroup … remains an open problem»; they get the largest cyclic factor and a Conjecture 3.11 (leading terms); odd p via a cell complex. No tilting.
- Bai, LAA 369 (2003): odd p only (to read in full for the counts).
- Abiad et al. arXiv:1910.12502; Iga–Klivans–Kostiuk–Yuen arXiv:2202.02821 (adinkras): spectral/SNF bounds; to check.
Provisional: Q1 — no prior tilting decomposition of a sandpile group found.

### Entry 2 — 2026-10-04 (Grepy Hypercube)
More searches: «sandpile hypercube 2-Sylow 2023–2026»; «tilting SL2 char 2 tensor power Smith Laplacian»; «Wilson inclusion matrices SNF»; «arXiv 2025 2026 sandpile n-cube 2-Sylow Gao proved».
Citations harvested from Semantic Scholar (API, read today): of Gao et al. 1912.06919 → 3 papers (2402.15453 Reiner–Smith cones over trees; 2301.02517 Yuen, Adinkras up to 2-rank; 2202.02821 Iga et al.); of Chandler–Sin–Xiang 1511.00272 → 13 (Ducey et al. 2310.09227; walk matrices; 1-intersection ranks; Anzis–Prasad; …); of 2310.09227 → 3 (2609.12546 Kneser magic maps; Hamming-layer codes; 2505.02505 Maliakas–Stergiopoulou).
Read in the original (sources/, pdftotext):
- Yuen 2301.02517, line 39: «the 2-Sylow subgroup of K(A) remains open». Works up to 2-rank; no tilting.
- Reiner–Smith 2402.15453: cones over trees; cites Bai only. Not our object.
- **Ducey–Engelthaler–Gathje–Jones–Pfaff–Plute 2310.09227 (Algebraic Combinatorics): the CLOSEST METHOD.** Smith group of every Z-combination in the Bose–Mesner algebra of the JOHNSON scheme (fixed-size subsets), incl. Laplacians/critical groups of Kneser and Johnson graphs, via Wilson's triangular forms reducing to matrices M_s whose size depends on k_r, k_c but not on n. Same spirit as our «a 2^|I|×2^|I| matrix M(λ,i) per family, independent of the multiplicity». Different object (Johnson scheme, not the Hamming scheme/hypercube; Wilson–Bier forms, not tilting modules). MUST BE CITED as the nearest precedent of the «small matrices» reduction.
- Maliakas–Stergiopoulou 2505.02505: Specht-module decomposition of images of intersection matrices (char 0 / ranks). Not Smith over Z_2, not hypercube.
- Larsen 2405.16015, Doty–Henke math/0205186: tilting decomposition of V^{⊗n} for SL_2 in char 2 (multiplicities via the fusion graph). Q4: the multiplicities m_λ(n) ARE these tilting multiplicities — known; our use is to index the sandpile group by them. Credit Doty–Henke/Donkin/Larsen for the multiplicities.
- Grinberg–Huang–Reiner 1704.03778: «critical groups» of modules over Hopf algebras (Brauer characters). Different object; no tilting decomposition of a graph's sandpile group.

## 4. Verdict of the sweep (provisional, 4 Oct)
- Q1 tilting decomposition of a sandpile group: **NOT FOUND** in any source read or in the citation trees of Gao et al., Chandler–Sin–Xiang, Ducey et al. 2310.09227.
- Q2 2-adic Smith form of Boolean-lattice operators through tilting/Weyl filtrations: not found; nearest is Ducey et al. (Johnson scheme, Wilson forms, every prime, no tilting) and Chandler–Sin–Xiang (Hamming scheme, Smith group of the ADJACENCY matrix, odd p and the structure for even n, by representation theory of the symmetric group / Jacobi sums? — reread their method before citing).
- Q3 whole 2-part of K(Q_n): open in every source up to 2025 (Gao et al. 2024, Yuen 2023, Anzis–Prasad, Bai). Gao et al. is the state of the art.
- Q4 m_λ(n): known (tilting multiplicities of V^{⊗n}, char 2).
**Grade: «to the best of our knowledge, after a search of the citation trees and the sources listed», Theorem D is new.** Not a proof of novelty: Google Scholar not queried (blocked to scripts); MathSciNet not available.
Owed: reread Chandler–Sin–Xiang's method (§ for even n); Google Scholar by hand (Rafa); Bai 2003 read in full.

### Entry 3 — Chandler–Sin–Xiang reread (arXiv:1511.00272, DCC 84 (2017))
Their object is the ADJACENCY matrix A of Q_n (Smith group), even n: «A is integrally equivalent to diag with C(n,m) zeros and k = 1..m with multiplicity C(n, m−k)·…» (Thm 1.1). Method: Wilson-type inclusion maps η_{t,k} and Frankl's rank-t subsets (standard tableaux of shape [n−t,t], i.e. two-row Specht modules), canonical bases. Their final section (line ~851) states that for the LAPLACIAN nI − A only the 2-Sylow subgroup of the critical group remains to be determined. So: same Boolean-lattice/two-row-shape machinery, different matrix (A, whose 2-part has exponents 1..m, versus the Laplacian with towers), no tilting modules. **Cite it as the nearest precedent on the hypercube itself.**
Q2 updated: the integral two-row (Specht) structure of the Boolean lattice is used by Wilson, Bier, Chandler–Sin–Xiang, Ducey et al.; what is not found is its 2-adic tilting form and its use on the Laplacian.
Quote found in the original (Chandler–Sin–Xiang §5.2, txt lines 850–853): «It would be of interest to find a diagonal form for the Laplacian matrix nI − A of Q_n … only the 2-Sylow subgroup of the critical group remains to be determined … We do not have any conjecture about its exact structure.» This is the source of the «not even a conjecture» line (it is NOT Reiner's poster).

> **NOTE 2026-10-04 20:50 (Grepy Bross).** The cold reader (`reports/LECTOR_FRIO_1/`) read Doty–Henke (math/0205186): it decomposes L ⊗ L′ for two simple modules and factorises tilting modules (Lemma 1.4); it does **not** give the multiplicities of T(λ) in V^{⊗n}. Credit for m_λ(n): Donkin's tensor product theorem (characters) and Larsen, arXiv:2405.16015 (2024) §2 (fusion graph of V^{⊗2} at p = 2; reader's P-LARSEN 32/32, control fires; quoted through a fetch tool, **not yet read in the original**), with Tubbenhauer–Wedrich whom Larsen cites. Also to credit: the basis s_S = ∏(1 − x_i) is the Laplacian analogue of Chandler–Sin–Xiang §5 eq. (5) and is Gao et al.'s change of variables u_i = x_i − 1 (proof of Prop. 2.5).

> **NOTE 2026-10-04 ~20:55 (Grepy Bross).** Larsen arXiv:2405.16015 v1 now READ IN THE ORIGINAL (`sources/Larsen_arXiv2405.16015.pdf`, md5 `51ef9216…`): §2 prints the V^{⊗2} fusion rule exactly as the cold reader quoted it; characters from Tubbenhauer–Wedrich (Represent. Theory 25, 2021, Prop. 2.6, 5.4); tilting ⊗ tilting by Donkin (Math. Z. 212, 1993). Details: `reports/LECTOR_FRIO_1/LARSEN_READ_IN_ORIGINAL_v1.md`.
