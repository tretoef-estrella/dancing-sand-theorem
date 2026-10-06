# Audit — Flight 6 («Grepy el volador 6»: Conjecture 5.4 and the fold law), Grepy Hypercube, 4 Oct 2026

Delivery read cold: `~/Desktop/GREPY_EL_VOLADOR_6/REPORT.md` (330 lines, md5 `ea663da7428c18118a407ecf2954167f`; 321 files, manifest `ENTREGA_VUELO_6/MANIFEST_md5.txt`, md5 identical before and after the move). The folder is now `VOLADORES/GREPY_EL_VOLADOR_6/`.

## 1. Verdict in one line

**GAO ET AL.'S CONJECTURE 5.4 IS PROVED FOR EVERY k, AND THE FOLD LAW 2K(Q_n) ≅ K̄(n) ON 2-PARTS IS NOW PROVED FOR EVERY n ≤ 60.**
- The flight proved Conjecture 5.4 by pencil. The auditor re-derived it and gated it with own code.
- For the fold law, the flight reached n ≤ 21 and n = 23, 25, 27 with 46 exact certificates. The auditor added a second, independent route (§4), which covers every n ≤ 60.
- **For every n the fold law is still open:** it is conditional on the flight's conjugacies (Q) and (Q_even). The kill criterion never fired.

## 2. Grades

| result | grade |
|---|---|
| Leg 0: Bai's counts (2^{n−1} − 1 factors, a_n Z/2's) from the rule, every n | PROVED (pencil; second reading; gates n ≤ 100, own code). Bai's theorems, re-derived as a calibration. |
| **Leg A: Conj. 5.4, Syl₂K(Q_{2^K}) ≅ Syl₂K(Q_{2^K−1})² × Z/2^{2^K+K−1}, every K** | **PROVED** (pencil, two readings, gates K ≤ 10, own code), resting on the closed rule (flights 1–4). It is stronger than Gao's statement: it holds dancer by dancer. No external cold reading. |
| Leg B: rule for K̄ = rule for K with every exponent lowered by one | PROVED for the Steinberg families (pencil). PROVED for every family present in Q_n, n ≤ 60 (§4). General: conditional. |
| **Leg C: fold law** | **PROVED for every n ≤ 60** by two routes: certificates (flight, n ≤ 21, 23, 25, 27) and cells (auditor, n ≤ 60). Every n: CONDITIONAL on (Q), (Q_even). |

## 3. Pencil reading (my own words)

- **Lemma F, Lemma S, Lemma B, Theorem (Bai) — CORRECT.**
  - X₀² = X₁ + 2 gives the fusion rule.
  - T(0) never recurs; m₁ and m₂ are powers of 2.
  - A family contributes dim T/2 factors and dim T/4 Z/2's.
- **Lemma A — CORRECT, re-derived.**
  - At N = 2^K − 1: x = 2^K − 2J; s₂(x) = K − 1 − s₂(J−1) (complement in K − 1 bits); s₂(J − 1 + x) = K − s₂(J). Hence κ = s₂(J) − 1.
  - At n = 2^K: x′ = (2^K − 1) − 2a, so κ = s₂(a).
- **Theorem A — CORRECT, re-derived.**
  - (i) Uses s₂(J−1) = s₂(J) − 1 + v₂(J).
  - (ii) The difference is t₁ − 1 − v₂(J).
  - (iii) v₂(2i) = v₂(2^k + o_I) = t₁ since k < K. Every digit of D is ≥ t₁, so v₂(J) = t₁ − 1.
- **Pooling doubles — CORRECT.** Each value appears twice, adjacent in o-order. The integer split depends only on the size and the sum of each level set.
- **Corollary 5.4 — CORRECT.** The top factor is the dancer {0} of the family 2^K: J′ = 1, κ = 0, h = K, value 2^K + K − 1.
- **Lemma RT̄ — CORRECT.**
  - Z[G]/(a − 1) is the group ring of Q_n/⟨a⟩, so C̄ = coker[σ | a − 1].
  - a = g^{⊗n} and σ = n − (Lie action of g) both act through GL₂, so they respect the tilting decomposition.
  - g = d·exp(F) with d = (−1)^floor, and on T(λ) ⊗ det^i, a = (−1)^{D+i}·exp F.
  - Confirmed independently: the whole folded groups computed with no families (§4, D) agree with the family-wise rule.
- **Lemma Π(b) — CORRECT.** (1 + 2t)² = 1 + 4(t + t²), and the change of basis is unitriangular.
- **Not re-derived by the auditor:** the Ψ formula of §3.4(Φ) (Bernoulli coefficients), Lemma N, Lemma Z0, and the Hilbert-90 obstruction §3.8.
  - The flight's results for n ≤ 21, 23, 25, 27 at **every** shift depend on them.
  - **The auditor's route (§4) does not:** for a fixed n only the finitely many shifts i = (n − λ)/2 are needed, and those are computed directly.

**No GAP and no ERROR found in what was read.**

## 4. Independent gates — engine `engines_gh/gh_audit_vuelo6.py`

Every run ended VIGIA-FIN-OK. Predictions were sealed in `SEALED_AUDITOR.md` before any run.

The engine uses my own rule (gh_audit_vuelo2 multiplicities, raw clocks, my integer PAVA) and my own Smith forms: pure Python mod 2^128 for lattices, numpy mod 2^30 for Laplacians. **The only flight code used is the lattice builder tilt_dp** (copied as `vuelo6_tilt_dp.py`, md5 identical). Mode L validates it:
- every divided power has only odd denominators;
- F·F^(b) = (b + 1)F^(b+1);
- F^(m) raises the floor by m;
- the weights are Donkin's character;
- coker(F + 2(D + i)) equals my rule cell X(λ, i) in every cell.

| mode | what | result | control |
|---|---|---|---|
| B | Bai counts, Lemma S, Lemma F, n ≤ 100 | 0 failures | factor 1 in the fusion rule differs at 50 n; ⌈·⌉ in a_n differs at 49 n |
| T | Lemma M, digits, twins, pooled doubling, Conj. 5.4, K ≤ 10 (n ≤ 1024; 1 013 families, 14 757 dancers) | 0 failures, 10/10 | without the top factor: 0/10 hold; twins at other odd N fail 14 672 / 24 310 |
| R | lowered rule vs my earlier direct F₂ measurement of the folded operator (aire.py, 1 Oct), n = 14, 15, 16: 3368, 6436, 12872 | match | unlowered rule differs. *Honest note: this is layer 2, already proved in note v2; little new evidence.* |
| D | **whole groups computed directly** (Laplacian Smith, no families, no turnos, no tilt_dp): K̄(n) for n = 3..13; K(Q_n) for n = 3..12 | K̄ = lowered rule 11/11; K = rule 10/10; 2K ≅ K̄ 10/10 | the unlowered rule never matches |
| L | lattices λ ≤ 20 and odd λ ≤ 27, i ≤ 8 (192 cells) | 0 failures | *(the «control» numbers this mode prints are not computed, a printing slip of mine; the real controls are in C and N)* |
| C | X̄(λ, i) ≅ 2X(λ, i) on the lattices, λ ≤ 20 and odd λ ≤ 27, i = 0..40 (984 cells) | 0 failures | unlowered differs 983/984; lowered by 2 differs 982/984 (the cell that does not differ has X = 0) |
| **N** | **every family of every n at the shift the cube needs: lattice validated, then X̄ = 2X and X = rule, n = 3..60 (928 cells)** | **the fold law HOLDS at every n ≤ 60** | Xbar = X unlowered differs in every cell |
| repro | the flight's certificate verifiers, run on a copy | identical output: 26/26 and 20/20 valid | as the flight's |

Example check: X(6, 2) = {1⁴, 3, 6², 10} and X̄ = {2, 5², 9}, as in REPORT §3.2.

**Peaks:** D at n = 13 reached 1.17 GB (4096 × 4096), close to the cap. Every other run was ≤ 980 MB (D at n = 12, 196 s); N up to 60 used 153 MB in 284 s.

**Dependencies of the auditor's route for n ≤ 60:**
- Lemma RT̄ (re-derived above);
- flight 2's construction of T(λ) over Z₂ (A.1, B.1, audited 3 Oct), whose consistency with the rule is re-checked in every cell;
- the closed rule (flights 1–4);
- exact finite Smith computations.

The route needs neither the certificates nor Ψ.

## 5. Sealed predictions of the auditor

S1–S7 held. **S8 (20 %, «some control fails to fire»): did not happen**, except the L-mode printing slip, which is not a control.
- Marks: 7 «safe» predictions held.
- The only prediction with real risk was that N would reach far; I did not seal it, so it does not count as a hit.

## 6. The constructor's conduct

- **Rules kept:** no agents; every computation inside its folder and through vigia; material/ unchanged (251/252, the difference being CLAUDE.md as ordered).
- **Errors published:** E1, E2 (estimates not fully prior), E3–E8 (stray file, killed run, wrong claim corrected, one run outside vigia that crashed at import, float leak caught and its run kept as INVALID, typed times).
- **Failures published in full size:** PB.1, PB.5, PB.7.
- **E4 and E5 of flight 5 (pencil not on disk) not repeated:** the Leg A pencil was in the flight's head for 3 minutes before going to disk, and it says so.
- **Grade of the work: HIGHEST MARK.**
  - It closes Conjecture 5.4, explains it dancer by dancer, and reduces the general fold law to two conjugacies.
  - It found the structural reason for the Steinberg families: the fold keeps the even eigenvalues, and that is the doubled payment.

## 7. State of the art (4 Oct)

- One extended web search turned up nothing newer than Gao et al. (arXiv:1912.06919; Comm. Algebra 2024). There, Conjecture 5.4 is open, and the 2-part is a «poorly understood» component.
- **Credit:** Gao et al. stated Conjecture 5.4. The fold law is ours: measured by Grepy Chats on 2 Oct, from Rafa's image «se van turnando».

## 8. Open after this flight

- **(Q) and (Q_even) for every tilting lattice.** This is the fold law for every n. The flight's descent argument shows that the reason cannot be a formula in F alone.
- The auditor's route reaches n = 60. Above that, families of dimension 1024 appear (λ = 62).
- A cold reader for the whole chain (flights 1–6), then the paper.
