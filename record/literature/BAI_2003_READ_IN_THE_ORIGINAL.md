# Bai 2003, read in full — Grepy Hypercube, 2026-10-04 12:59:55

Source: Hua Bai, «On the critical group of the n-cube», Linear Algebra Appl. 369 (2003) 251–261 (`sources/Bai_cube_group_LAA2003.pdf`, read through `sources/Bai_cube_group_LAA2003.txt`, every page).

## What it contains
- **Reiner's two conjectures** (Univ. of Minnesota Combinatorial Problem Session, 2001; Bai's ref. [17]), both PROVED by Bai:
  - Theorem 1.1: K(Q_n) has exactly 2^{n−1} − 1 invariant factors;
  - Theorem 1.3: a_n (the Z/2's) has generating function 1/((1 − 2x)(1 − 2x²)), so a_n = 2^{n−2} − 2^{⌊(n−2)/2⌋}.
- Theorem 1.2: Syl_p K(Q_n) ≅ Syl_p ⊕_{k=1}^{n} (Z/k)^{C(n,k)} for odd p.
- **Bai's own words (p. 253): «The full structure of the Sylow-2 subgroup of the critical group of the n-cube is still unknown.»**
- The tools:
  - **Lemma 2.1:** (1/m!)·Π_{i<m}(L_n + 2(k+i)) is integral. This is the integrality of the divided products, i.e. the ring 𝓢 of flight 6.
  - **Lemma 2.2:** L_{n+1,k} ~ I ⊕ L_{n,k}L_{n,k+1}. This is the «halving identity» that Mandalay re-found on 2 Oct and did not claim as new: **it is Bai's.**
  - **Prop. 3.1:** maps ψ, φ between K(L_{n,k}L_{n,k+1}) and K(L_{n,k}) × K(L_{n,k+1}) with ψφ = 2 and φψ = 2 (an isomorphism away from 2).
  - **Cor. 4.2:** a partial recursion for Syl₂, using the two indices n − 2 and n − 3.
- Table p. 260: Syl₂K(Q_n) for n = 2..11 (Reiner's LinBox data).

## Gate
`engines_gh/gh_bai_table_gate_v2.py`, log `logs/gh_bai_table_gate_v2.log`: **the rule reproduces Bai's printed table, 10/10**. Control (the rule lowered by one): 0/10.
- My first transcription (`gh_bai_table_gate.py`) gave 4/10. That was MY error: the printed superscripts omit the multiplicity 1, and I had misaligned them. The log is kept.
- This is independent 2003 data, computed by another program (LinBox).

## Consequences for our registers
1. **Correction to my answer 2 of `notes/TITLE_AND_SIX_QUESTIONS_v1.md`.** I said there is no «Reiner conjecture» on the hypercube. That is wrong. Reiner proposed two conjectures in 2001, and **Bai proved both in 2003.**
   - What was still open after Bai, in his own words, is the full Sylow-2 subgroup.
   - What the Dancing Sand Theorem gives is that full Sylow-2 subgroup.
   - Correct claim (after a cold reading): «we determine the Sylow-2 subgroup of K(Q_n) for every n, which Bai (2003) left open after proving Reiner's two conjectures, and which Chandler–Sin–Xiang (2017) and Gao et al. (2024) left open».
2. **Credit in the paper:**
   - flight 6's Leg 0 (Bai's counts) re-derives Bai's Theorems 1.1 and 1.3;
   - the halving identity is Bai's Lemma 2.2;
   - the integrality of the divided products is Bai's Lemma 2.1.
3. **Lead for the fold law (READING, not tested):** Bai's Prop. 3.1 is a pair of maps whose composites are multiplication by 2, and the fold law says 2K(Q_n) ≅ K̄(n). It may be worth checking whether K̄(n) is one of Bai's two factors, or their combination: K(L_{n−1,0}) × K(L_{n−1,1}), or coker(L_{n−1} + 2). Not sent to flight 7 while it flies; for the audit of flight 7.

> **Note 2026-10-04 13:00:16:** item 3 above is weaker than written. By Prop. 3.1 the product K(L_{n−1,0}) × K(L_{n−1,1}) has the same order as K(Q_n), while K̄(n) has the order of 2K(Q_n), which is smaller. So K̄(n) is not that product. What is left of the lead is only that both statements are «up to 2» relations; nothing to test now.
