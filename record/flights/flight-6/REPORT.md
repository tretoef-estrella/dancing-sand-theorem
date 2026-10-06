# REPORT — Flight 6 «Grepy el volador 6»

## 0. First line — what this flight closes and what it does not

**THIS FLIGHT CLOSES GAO ET AL.'S CONJECTURE 5.4 FOR EVERY k, BY PENCIL, AND PROVES THE FOLD LAW 2K(Q_n) ≅ K̄(n) (2-parts) FOR EVERY n ≤ 21 AND n = 23, 25, 27. IT DOES NOT PROVE THE FOLD LAW FOR EVERY n.**
- **Leg 0 — CLOSED.** Bai's two counts (2^{n−1} − 1 cyclic factors; a_n = 2^{n−2} − 2^{⌊(n−2)/2⌋} factors Z/2) for every n, by pencil from the rule (fusion rule T(λ) ⊗ V; T(0) never occurs; m₁, m₂ = powers of 2).
- **Leg A — CLOSED.** **Syl₂ K(Q_{2^K}) ≅ Syl₂ K(Q_{2^K−1})² × Z/2^{2^K+K−1} for every K ≥ 1**, by pencil, and more: family by family and dancer by dancer — every dancer D of the odd cube becomes the twins D, D ∪ {0} with the same raw clock (the new digit's gold t₁ pays exactly the carries v₂(J) = t₁ − 1). Gated K ≤ 9.
- **Leg B — NO CONCLUYO for every n; the rule is stated and proved where certified.** The folded cube splits family by family (the fold is the GROUP action of the matrix whose Lie action is the Laplacian); the rule for Syl₂ K̄(n) is **the rule of K with every exponent lowered by one**. PROVED by pencil for every Steinberg family (the fold is the restriction to even eigenvalues, which is the doubled payment); reduced for odd families to one conjugacy (Q) and for even families to (Q_even); **both certified exactly (46 certificates) for every λ ≤ 20 and every odd λ ≤ 27.** Gated: whole groups n = 3..13 (11/11), the note's proved layers n ≤ 40.
- **Leg C — CLOSED for n ≤ 21 and n = 23, 25, 27; NO CONCLUYO for every n** (conditional on (Q), (Q_even) for all tilting lattices). The cells n = 14..21, 23, 25, 27 are new.
- **Kill criterion: did not fire.**
- **Failures published:** PB.1 (the fold law is not a general lemma for lattices with an involution), PB.5 (scope of the perturbation statement), PB.7 (no natural intertwiner), the error E5 (a wrong «parity obstruction»), the invalid run of E7 (a float leak).

## 1. Leg 0 — calibration (Bai's counts from the rule)

**Estimate (written Sun Oct  4 09:04:22 CEST 2026, before the pencil is written down):** 10–15 % of the flight. Pencil: count cyclic factors family by family (2^{|I|} big + Σ_a small), use dim T(λ) = 2^{k+|I|} and Σ_λ m_λ dim T(λ) = 2^n; the Z/2's need the small multiplicities m_0, m_1, m_2, from a fusion rule T(λ)⊗V by Donkin's product formula. Machine: one gate engine over f5lib (n ≤ 200, < 100 MB, < 2 min). **Honesty note:** the two key observations (the fusion rule and m_0(n) = 0) came to me while reading flight 5's §2.4, minutes before this estimate was written; the estimate is therefore not fully prior (see §7, E1).

### 1.1 Setting (from the closed rule; notation of flight 5)
Family λ ≡ n (mod 2), λ + 1 = 2^k + o_I, I ⊆ [0, k), multiplicity m_λ(n) (= multiplicity of the tilting module T(λ) in V^{⊗n}, char 2; characters ch T(λ) = Π_{t<k} X_t · Π_{t∈I} X_t, X_t := e^{2^t} + e^{−2^t}, Donkin's product formula). Each copy of the family gives:
- small clocks (Z/2^a)^{2^{|I|+k−1−a}}, a = 1..k−1;
- big clocks: one per dancer D ⊆ I (2^{|I|} of them), the integer-PAVA pools of the raw clocks u(D) = φ(x) + κ(J−1, x) + h(D); the dancer with J = 0 (λ = n, D = ∅) is the free summand Z₂.

### 1.2 Lemma F (the fusion rule T(λ) ⊗ V) — PROVED, pencil
Since V^{⊗n} is tilting and the ch T(ν) are unitriangular (highest weight ν with coefficient 1), m(n+1) is read off X_0 · ch T(λ):
- **λ odd (0 ∉ I, k ≥ 1), and λ = 0:** X_0·ch T(λ) = ch T(λ + 1).
- **λ even ≥ 2 (0 ∈ I):** let a ≥ 1 be the run of I at 0 ([0, a) ⊆ I, and a ∉ I or a = k). Then
  **X_0·ch T(λ) = ch T(λ + 1) + 2·Σ_{j=0}^{a−1} ch T(λ + 1 − 2^{j+1})**.

*Proof.* X_t² = X_{t+1} + 2. By induction on a, X_0·(X_0X_1⋯X_{a−1}) = X_a + 2Σ_{j=0}^{a−1} X_{j+1}⋯X_{a−1} (step: multiply by X_a and use X_a² = X_{a+1} + 2). Write ch T(λ) = P·X_0⋯X_{a−1}·Q with P = Π_{t<k}X_t, Q = Π_{t∈I, t>a}X_t. The term P X_a Q is ch T(ν) with ν + 1 = λ + 2 (if a < k, the digit a enters I; if a = k, P X_k = Π_{t≤k}X_t and λ + 2 = 2^{k+1}). The term P X_{j+1}⋯X_{a−1} Q is ch T(μ_j) with μ_j + 1 = 2^k + o_{I∖[0,j]} = λ + 1 − (2^{j+1} − 1). For λ odd, X_0 just adds the digit 0 to I. ∎

### 1.3 Lemma S (the three smallest families) — PROVED, pencil
For n ≥ 1: **m_0(n) = 0; m_1(n) = 2^{(n−1)/2} (n odd); m_2(n) = 2^{(n−2)/2} (n even).**
*Proof.* By Lemma F, ν = 0 is never produced (μ_j = 0 would need λ = 2^{j+1} − 1 odd), so m_0(n) = 0 for n ≥ 1. ν = 2 is produced only by λ = 1 (μ_j = 2 would need λ odd): m_2(n+1) = m_1(n). ν = 1 is produced by λ = 0 and by μ_j = 1, i.e. λ = 2^{j+1} with run a > j; λ = 2^{j+1} has I = {0}, and its run is a = 1 if k = j+1 ≥ 2 (then j < 1 fails) and a = k = 1 if λ = 2 (j = 0 works). So m_1(n+1) = m_0(n) + 2m_2(n) = 2m_2(n) = 2m_1(n−1) for n ≥ 2, with m_1(1) = 1, m_2(2) = 1. ∎

### 1.4 Lemma B (every big clock is ≥ 2) — PROVED, pencil
For every family present in Q_n (n ≥ 1) and every dancer with J ≥ 1, the raw clock u(D) ≥ 2; hence every pooled big clock is ≥ 2 (a PAVA mean of numbers ≥ 2 is ≥ 2 and the integer split keeps ⌊mean⌋ ≥ 2).
*Proof.* φ(x) ≥ x, and φ(x) = 1 only for x = 1. x = 1 means μ = 0, λ = 2o_D. Since o_D ≤ o_I ≤ 2^k − 1 and λ + 1 = 2^k + o_I ≥ 2^k + o_D, λ = 2o_D forces o_D = o_I = 2^k − 1, i.e. D = I = [0, k). Then h(D) = k (every gap is 1), so u ≥ 1 + k ≥ 2 unless k = 0, i.e. λ = 0, which never occurs (Lemma S). ∎

### 1.5 Theorem (Bai 2003, from the rule) — PROVED, pencil
For every n ≥ 1: (i) **Syl₂ K(Q_n) has exactly 2^{n−1} − 1 cyclic factors**; (ii) **exactly a_n = 2^{n−2} − 2^{⌊(n−2)/2⌋} of them are Z/2** (n ≥ 2).
*Proof.* (i) A copy of family λ with k ≥ 1 gives 2^{|I|} + Σ_{a=1}^{k−1} 2^{|I|+k−1−a} = 2^{|I|+k−1} = dim T(λ)/2 factors, all nontrivial (small: a ≥ 1; big: Lemma B), one of which is the free Z₂ exactly for λ = n (the only family at i = 0, m_n(n) = 1). λ = 0 (k = 0, where the count would be 1, not 1/2) never occurs (Lemma S). So the count is Σ_λ m_λ(n) dim T(λ)/2 − 1 = 2^n/2 − 1.
(ii) Z/2 comes only from small clocks a = 1 (Lemma B), 2^{|I|+k−2} = dim T(λ)/4 per copy of a family with k ≥ 2. The families with k ≤ 1 are λ = 0, 1, 2 (dims 1, 2, 4). So #Z/2 = (2^n − m_0 − 2m_1 − 4m_2)/4 = 2^{n−2} − m_1/2 − m_2 (Lemma S: m_0 = 0) = 2^{n−2} − 2^{(n−3)/2} (n odd) or 2^{n−2} − 2^{(n−2)/2} (n even), which is 2^{n−2} − 2^{⌊(n−2)/2⌋} in both cases. ∎
**This is the fold law's layer 0 and its a_n.** Uses: the rule (flights 1–4); Donkin's product formula for ch T(λ); nothing measured.

### 1.6 Gate (engines/leg0_gate.py, logs/leg0_gate.log; estimate < 100 MB / 2 min; VIGIA-FIN-OK, 14 MB, 0 s) — MEASURED
| id | statement | result | control (must fire) |
|---|---|---|---|
| P0.1 | Lemma F reproduces the peeled m_λ(n), n ≤ 200 | **held**, 0 failures | factor 1 instead of 2: differs at 198 n |
| P0.2 | m_0 = 0, m_1, m_2 as in Lemma S, n ≤ 200 | **held**, 0 | — |
| P0.3 | raw and pooled big clocks ≥ 2, n ≤ 120 (3 660 family cells) | **held**, 0; min pooled = 2 | — |
| P0.4 | 2^{n−1} − 1 factors and a_n Z/2's, 2 ≤ n ≤ 120 | **held**, 0 | ⌈(n−2)/2⌉: differs at 59 n |

**What the calibration found.** Bai's two counts are pure bookkeeping on the rule: half the dimension of each tilting family is its number of factors, and the Z/2's are a quarter of the dimension minus the three smallest families. The only non-trivial input is that T(0) never occurs and that T(1), T(2) have multiplicities 2^{⌊(n−1)/2⌋}, which is Lemma F at the bottom of the weight line: **V ⊗ V = T(2) is indecomposable in characteristic 2, and T(2) ⊗ V = T(3) ⊕ 2T(1).** The rule gives the counts. **Leg 0 CLOSED.**

## 2. Leg A — Conjecture 5.4

**Estimate (written Sun Oct  4 09:07:29 CEST 2026):** 20–30 % of the flight. Plan: N = 2^K − 1 is odd, so by Lemma F every family λ of N goes to λ + 1 alone (T(λ) ⊗ V = T(λ+1)), with the same multiplicity and the same shift; the new digit 0 doubles the dancers (D and D ∪ {0}) and the small clocks; compare raw clocks. Machine: one gate over f5lib, K ≤ 9 (n ≤ 512), < 300 MB, < 5 min. **Honesty note (E2):** the comparison of raw clocks below was done in my head between 09:04 and 09:07, right after reading Gao's statement and before this estimate was written. It is written down now, before any gate.

### 2.1 Lemma M (the families of an odd cube move up by one) — PROVED, pencil
For every odd N: **m_{λ+1}(N + 1) = m_λ(N) for every λ, and these are all the families of N + 1.** *Proof.* All families of N are odd; by Lemma F, T(λ) ⊗ V = T(λ + 1) for λ odd. ∎
The family λ + 1 has the same k and **I′ = I ∪ {0}** (λ + 2 = 2^k + o_I + 1, and o_I + 1 < 2^k since 0 ∉ I), and the **same shift** i = (N − λ)/2 = (N + 1 − (λ + 1))/2. Its small clocks are exactly twice those of λ (|I′| = |I| + 1). Its dancers are D and D ∪ {0}, D ⊆ I; in o-order they come in adjacent pairs (o_D is even), and the gap of the new digit is h′_0 = t₁ := min(I ∪ {k}); the gaps of the other digits are unchanged.

### 2.2 Lemma A (the raw clocks at N = 2^K − 1 and n = 2^K) — PROVED, pencil
Let N = 2^K − 1, n = 2^K, and J ≥ 1 (so J ≤ N/2 < 2^{K−1} in N, J ≤ 2^{K−1} in n).
- **(a) in the cube N:** x = 2^K − 2J, and κ(J − 1, x) = s₂(J) − 1, so **u_N(D) = 2^K − 2J + v₂(J) + s₂(J) + h(D).**
  *Proof.* φ(x) = 2^K − 2J + 1 + v₂(J) (since 1 ≤ J < 2^{K−1}). With a = J − 1: a + x = 2^K − 2 − a = (2^K − 1) − (a + 1), whose digit sum is K − s₂(J); and x/2 = 2^{K−1} − 1 − a has digit sum K − 1 − s₂(a). So κ = s₂(a) + (K − 1 − s₂(a)) − (K − s₂(J)) = s₂(J) − 1. ∎
- **(b) in the cube n:** x′ = 2^K − 2J′ + 1 is odd and κ(J′ − 1, x′) = s₂(J′ − 1), so **u_n(D′) = 2^K − 2J′ + 1 + s₂(J′ − 1) + h′(D′).**
  *Proof.* With a = J′ − 1 (2a < 2^K): a + x′ = (2^K − 1) − a has digit sum K − s₂(a), and x′ = (2^K − 1) − 2a has digit sum K − s₂(a). So κ = s₂(a) + K − s₂(a) − K + s₂(a) = s₂(a). ∎

### 2.3 Theorem A (the mirror that doubles) — PROVED, pencil
For N = 2^K − 1 and every odd family λ < N, at shift i ≥ 1: **the dancers D and D ∪ {0} of the family λ + 1 in the cube 2^K have exactly the raw clock u_N(D) of the dancer D of the family λ in the cube 2^K − 1.**
*Proof.* (i) D′ = D: J′ = J, h′(D) = h(D), and s₂(J − 1) = s₂(J) − 1 + v₂(J); by Lemma A, u_n(D) = 2^K − 2J + s₂(J) + v₂(J) + h(D) = u_N(D).
(ii) D′ = D ∪ {0}: J′ = J + 1, h′ = h(D) + t₁; by Lemma A(b), u_n(D ∪ 0) = 2^K − 2J − 1 + s₂(J) + h(D) + t₁ = u_N(D) + (t₁ − 1 − v₂(J)).
(iii) **v₂(J) = t₁ − 1.** 2i = N − λ = 2^K − (2^k + o_I) with k < K, so v₂(2i) = v₂(2^k + o_I) = t₁, i.e. v₂(i) = t₁ − 1 (t₁ ≥ 1 because 0 ∉ I). Every digit of D is ≥ t₁, so v₂(o_D) ≥ t₁ and v₂(J) = v₂(i + o_D) = t₁ − 1. ∎
**Pooling.** The raw sequence of λ + 1 in o-order is that of λ with every entry written twice. The antitonic least-squares fit is unique and doubling every point is giving it weight 2, so the fit of the doubled sequence is the doubled fit. The rule's integer split («ceil first») gives, on a level set of size p and sum T, T mod p copies of ⌊T/p⌋ + 1 and the rest ⌊T/p⌋ — a function of the level set's size and mean only (two adjacent PAVA blocks with equal mean give the same multiset as their union). Doubling p and T doubles both counts. **So the pooled clocks of (λ + 1, i) in the cube 2^K are those of (λ, i) in the cube 2^K − 1, each twice.**
**Shift 0.** The family N = 2^K − 1 (I = ∅) has only the free dancer. The family 2^K has I′ = {0}: the free dancer ∅ and the dancer {0}, with J′ = 1, x′ = 2^K − 1, κ = 0, h′_0 = K: **u = 2^K + K − 1** (flight 5's V₀ = φ(n) − 1). The free dancer is first in o-order with value ∞, so nothing pools with it.

### 2.4 Corollary — Gao et al.'s Conjecture 5.4, for every K ≥ 1 — PROVED, pencil
**Syl₂ K(Q_{2^K}) ≅ Syl₂ K(Q_{2^K − 1})² × Z/2^{2^K + K − 1}.**
*Proof.* By the rule, Syl₂ K(Q_N) ⊕ Z₂ is the sum over the families λ of N of m_λ(N) copies of [small clocks ⊕ pooled big clocks], the Z₂ being the free dancer of λ = N. By Lemma M the families of n = N + 1 are the λ + 1 with the same multiplicities and shifts; by §2.1 their small clocks double; by Theorem A and the pooling paragraph their big clocks double for λ < N; for λ = N the family 2^K gives its doubled small clocks, the free Z₂ and Z/2^{2^K+K−1}. So Syl₂ K(Q_n) ⊕ Z₂ ≅ Syl₂ K(Q_N)² ⊕ Z/2^{2^K+K−1} ⊕ Z₂, and the free Z₂ cancels (finitely generated Z₂-modules). ∎
**It is stronger than Gao's statement: it holds family by family and dancer by dancer**, with the explicit pairing D ↔ {D, D ∪ {0}}. The mirror that doubles is the digit 0: adding it to every tilting family of the odd cube splits each dancer into two twins with the same clock.
**Dependencies:** the closed rule (flights 1–4); Lemma F (§1.2); Donkin's product formula; Kummer; uniqueness of the antitonic least-squares fit. Nothing measured.

### 2.5 Gate (engines/legA_gate.py, logs/legA_gate.log; estimate < 200 MB / 5 min; VIGIA-FIN-OK, 20 MB, 1 s) — MEASURED
| id | statement | result | control (must fire) |
|---|---|---|---|
| PA.1 | Lemma M, odd N ≤ 199 | **held**, 0 | — |
| PA.2 | Lemma A closed forms, K ≤ 9 (14 757 dancer cells) | **held**, 0 | — |
| PA.3 | twins u_n(D) = u_n(D∪0) = u_N(D), K ≤ 9 (4 916 dancers) | **held**, 0 | same pairing at odd N ≠ 2^K − 1, N ≤ 199: fails in 14 672 / 24 310 dancers, at all 93 such N |
| PA.4 | pooled doubling family by family, K ≤ 9 | **held**, 0 | — |
| PA.5 | Conj. 5.4 on whole spectra, K = 1..9 (n ≤ 512) | **held** 9/9 | without the top factor: fails 9/9 |
(The number of factors printed, 2^{n−1} − 1, is Bai's count again.) **Leg A CLOSED.**

## 3. Leg B — the folded cube's rule

**Estimate (written Sun Oct  4 09:09:43 CEST 2026, before the leg):** 35–45 % of the flight; probability of a full pencil proof for every n in this flight: ~35 %. Plan: (1) read how flights 1–3 derive the rule (RT: V^{⊗n} as a tilting module, the Laplacian as the Lie action of X = e + f); (2) the fold a = x₁⋯x_n is the GROUP action of the same matrix g = [[0,1],[1,0]] ∈ GL₂, times det^i = (−1)^i on the family at shift i, so the folded cube should split family by family too; (3) find what (1 + εg) does to each family's cokernel; (4) machine: a direct engine for the family cokernels of K̄ (Smith over Z_2 of (n − X, εg − 1) on T(λ)), n ≤ 12, gated against turnos.py's whole groups; estimate per run < 500 MB, < 5 min. *(Note added at the final read-through: the matrix guessed here, g = [[0,1],[1,0]] with the Laplacian as e + f, is my first guess before reading flight 1; in flight 1's basis the right matrix is g: b0 ↦ b0 − b1, b1 ↦ −b1, and the Laplacian is n minus the Lie action of g — §3.1.)*

### 3.1 Lemma RT̄ (the folded cube splits family by family) — PROVED (pencil, modulo the same standard tilting facts as flight 1's Theorem RT)
In flight 1's dictionary (V = Z b0 ⊕ Z b1, s_S ↦ b1 on S, b0 elsewhere), x = 1 − s acts on V by **g: b0 ↦ b0 − b1, b1 ↦ −b1**, a matrix of GL₂(Z) with g² = 1, det g = −1; and σ = n − Σ_i x_i = n + (Lie action of −g) = F + n − H. The fold **a = x₁⋯x_n is the group action of g on V^{⊗n}**. Both σ and a act through the Schur algebra S(2, n) over Z_2, so they respect the tilting decomposition V^{⊗n} ≅ ⊕_λ (T(λ) ⊗ det^{i})^{m_λ(n)}, i = (n − λ)/2. On T(λ) ⊗ det^i, g acts as det(g)^i · g|_{T(λ)} = (−1)^i g|_{T(λ)}, and g = d·exp(F) with d = (−1)^{floor} (floor of b1's), so **a = (−1)^{J} exp(F) with J := floor of the cube = (λ − H)/2 + i**. Hence, with τ_i := F + λ − H + 2i on T_{Z_2}(λ):
  **C̄ ⊗ Z_2 = Z_2 ⊕ Syl₂ K̄(n) ≅ ⊕_λ X̄(λ, i)^{m_λ(n)},  X̄(λ, i) := T_{Z_2}(λ) / (τ_i T + (a − 1) T).**
And X̄(λ, i) ≅ (1 + a)·X(λ, i) inside X(λ, i) = T/τ_iT (the injection of the note's §1.2 respects the decomposition).
Rationally: on the τ-eigenline of eigenvalue 2c inside the Weyl factor Δ(μ_D) (c = J_D + r, r = 0..μ_D), a = (−1)^c: the note's «a = (−1)^{σ/2} on characters», read inside each family. Also, in R, **a = Σ_j (−1)^j e_j(s) = Σ_j (−2)^j·C(σ/2, j)** (e_j = σ(σ−2)⋯(σ−2j+2)/j! on every character).

### 3.2 The family-by-family candidate — MEASURED (exploration engine engines/fold_fam.py)
Shifted folded cubes C̄(m, j) = Z[(Z/2)^m]/(σ + 2j, (−1)^j a − 1) (a lattice of rank 2^{m−1}) are, by §3.1, ⊕_ν X̄(ν, j + (m−ν)/2)^{m_ν(m)}; peeling by induction on m isolates every X̄(λ, i). **PB.0 (sealed 55 %): X̄(λ, i) ≅ 2·X(λ, i) — HELD in all 79 cells λ ≤ 9** (logs/fold_fam_9_6.log; VIGIA-FIN-OK, 25 MB, 0 s; no negative peel). Examples: X(6, 2) = {1⁴, 3, 6², 10} and X̄(6, 2) = {2, 5², 9}.
**Wider (logs/fold_fam_12_6.log; estimate < 400 MB / 4 min; VIGIA-FIN-OK, 159 MB, 69 s): 114/114 cells, every family λ ≤ 12, shifts i ≤ 6 + (12 − λ)/2 — HELD, no negative peel.** (This also reproduces, family by family, the whole groups K̄(n) of turnos.py for n ≤ 12 at j = 0 — see the gate in §3.10.)

### 3.3 Lemma L (the fixed lattice) — PROVED, pencil
(a) **T(λ) ⊗ det^i is a free Z_2[⟨a⟩]-module** for every family present (it is an S(2, n)-summand of V^{⊗n} = Z_2[G], which is free over Z_2[⟨a⟩]; a summand of a free module over the local ring Z_2[C_2] is free). Hence T^a := ker(1 − a) = (1 + a)T and ker(1 + a) = (1 − a)T, each of rank d = dim T/2.
(b) **X̄(λ, i) ≅ (1 + a)X(λ, i) ≅ coker(τ_i restricted to T^a)** for i ≥ 1 (τ injective): if τy ∈ (1 + a)T then (1 − a)τy = 0, so y ∈ T^a.
(c) Exact sequence 0 → X̄ → X → X/(1 + a)X → 0 with X/(1 + a)X ≅ coker(τ|(1−a)T) (via 1 − a); so |X̄|·|coker(τ|(1−a)T)| = |X|.
(d) Warning (pencil): (1 + a)X = 2X as SUBGROUPS is false in general: modulo 2, 1 + a ≡ F^{(2)} + F^{(3)} + … on X/2X = T̄/F T̄, and F^{(2)}v_0 = v_2 ∉ F·St_k ⊗ F_2 for k ≥ 2. The fold law is an isomorphism of abstract groups, not an equality of subgroups (except for λ ≤ 2 type cases where F^{(2)} vanishes mod F).

### 3.4 Pencil tools found while looking for the proof (written 09:30:09; PROVED unless marked)
- **(E) The eigen-frame.** For any Dist-lattice T and τ = F + 2(D + i): exp(F/2)·τ·exp(−F/2) = 2(D + i) =: 2J (because [D, F] = F), and exp(F/2)·a·exp(−F/2) = ε(−1)^D = (−1)^J. So X = Λ/2JΛ and X̄ = Λ_e/2JΛ_e, where **Λ := exp(F/2)T** (a lattice in T ⊗ Q, stable under F^{(m)} and 2J) and Λ_e := π_e(Λ), the projection to the floors with J even (π_e = (1 + a)/2). Both operators are diagonal; only the lattice is twisted. On the floors with J odd, 2J has valuation exactly 1.
- **(Z) The Z_2[C_2]-matrix form.** T is free over Z_2[C_2] (Lemma L), so τ = P + aQ (P, Q ∈ M_d(Z_2)), τ₊ := P + Q (a = 1), τ₋ := P − Q (a = −1), and by unimodular row/column operations **X ≅ coker [[τ₊, 0], [Q, τ₋]]**, X̄ = coker τ₊, X/(1+a)X ≅ coker τ₋. Rationally τ₊ has eigenvalues 2c with c even, τ₋ eigenvalues 2c with c odd (valuation exactly 1), so |coker τ₋| = 2^d and |X̄| = |X|/2^d = |2X| (orders agree). If Q is invertible: **X ≅ coker(τ₊ Q^{−1} τ₋)**. **Sufficient condition for the fold law:** if moreover B := Q^{−1}τ₊ ∈ 2M_d(Z_2) with 1 − B/2 invertible (e.g. τ₋ = 2·unit), then X ≅ coker(2τ₊ · unit) and 2X ≅ X̄.
- **(Φ) The odd step with the fold.** For λ = 2λ₁ + 1, T = Φ(N) = N[u]/(u² − 2F_N) (flight 2's «doblar»; F = multiplication by u), exp(F) = P + uQ with **P = cosh u, Q = sinh u / u** (power series in F_N, integral: P = Σ F^{(s)}/(2s−1)!!, Q = Σ F^{(s)}/(2s+1)!!). T = b0N ⊕ a(b0N) is a Z_2[C_2]-basis (mod 2 the b1-part of a(b0 n) is Qn, Q unipotent). In it: **τ₊ = Ψ := u·tanh(u/2) + 4(D_N + j/2)** (j even) or **u·coth(u/2) − 2 + 4(D_N + (j+1)/2)** (j odd), and the coupling is Q_τ = −εQ^{−1} (invertible). So **X̄(2λ₁+1, j) ≅ coker(Ψ on N)**, while P-R1 gives 2X ≅ X^{(2)}(λ₁, ⌈j/2⌉) = coker(F_N + 4(D_N + ⌈j/2⌉)). And u·tanh(u/2) = Σ_{m≥1} η_m F_N^{(m)} with **η_m = 2(2^{2m} − 1)B_{2m}/(2m−1)!! a 2-adic unit for every m** (von Staudt–Clausen: v₂(B_{2m}) = −1); η₁ = 1, η₂ = −1/3, η₃ = 1/5. So the odd-family fold law is: **coker(Σ_m η_m F^{(m)} + 4(D + c)) ≅ coker(F + 4(D + c)) on N = T(λ₁)** — the fold replaces F by a unit-weighted sum of all divided powers of F.
- **(e) In C = R/σR:** e₁e_k = (k+1)e_{k+1} + 2k·e_k, so (k+1)e_{k+1} ≡ −2k·e_k; in particular e₃ ≡ −(4/3)e₂, and **a − 1 ≡ Σ_{k even ≥ 2} u_k e_k with units u_k = (3k+1)/(k+1)**; with C[2] = e₂C (note §1.1) the fold law reads **C/e₂C ≅ C/(Σ_{k even≥2} u_k e_k)C**. Mod 2 the right side is Π_{t≥1}(1 + e_{2^t}) − 1.
- **(λ ≤ 2) Families λ = 1, 2: PROVED (pencil).** On T(0) and T(1) = V (the families ν of the cube n − 1 that give λ = 1, 2 by Theorem E), g/2 = (1 + τ + a′)/2 is integral (mod 2 it is Σ_{s≥2} F^{(s)} = 0 on V), with odd eigenvalues, hence a unit; so coker(fg/2) = coker(f·(g/2)) ≅ coker(f), i.e. 2X(λ, i) ≅ X̄(λ, i) for λ = 2 (and λ = 1 directly: X̄(1, i) = Z/2^{1+v₂(i(i+1))}, X(1, i) = Z/2^{2+v₂(i(i+1))}).
- **PB.1 FAILED (sealed 35 %; engines/fold_lemma_test.py, logs/fold_lemma_test.log, VIGIA-FIN-OK, 49 MB, 8 s).** The fold law is NOT a general lemma about free Z_2[C_2]-lattices with a = (−1)^{τ/2} rationally: random pairs (τ₊, τ₋) with the right eigenvalue valuations satisfy it always for d = 2 (800/800) but fail for d = 3 (168 of 632) and d = 4 (432 of 768). First failure (d = 3): X = {2, 11}, X̄ = {10} (2X = {1, 10}). **So any proof must use more of the families' structure**: the integrality of every e_j = τ(τ−2)⋯(τ−2j+2)/j! (the symmetric-function ring 𝓢 = Z_2⟨2^j·C(τ/2, j)⟩ acts on every family), not only τ and a.
- **(W) Weyl modules are cyclic 𝓢-modules (PROVED, pencil).** On Δ(μ) at shift J, e_j v₀ = Σ_{r≤j} 2^{j−r}C(J, j−r) v_r (unitriangular), so Δ_{Z_2}(μ) ≅ 𝓢|_{[J, J+μ]} (functions c ↦ Σ d_j 2^j C(c, j) restricted to the eigenvalue set c ∈ [J, J+μ]); by Vandermonde this lattice is translation-invariant: basis c ↦ 2^r C(c − J, r), r = 0..μ. In particular **the Steinberg families are the cyclic 𝓢-modules on intervals of length 2^k.**
- **PB.2 HELD** (sealed 60 % / 40 %; engines/fold_cyclic_test.py v2, logs/fold_cyclic_intervals.log, logs/fold_cyclic_random.log, VIGIA-FIN-OK, 12 MB, 3 s and 1 s): the fold law holds on every Z_2[a]-free cyclic 𝓢-module tested: **136/136 Weyl intervals** [J, J+μ] (μ ≤ 15 odd, J ≤ 17) and **147/147 random free sets** C. (The first run of v1 was killed by the watchdog, sympy HNF, and is kept as logs/fold_cyclic_intervals_KILLED.log; not a result.)

### 3.5 Lemma Π (the fold is the restriction to even eigenvalues) — PROVED, pencil
(a) For an 𝓢-lattice T free over Z_2[a] and i ≥ 1: **X̄ ≅ coker(τ on π_e(T))**, where π_e(T) is the image of T in ⊕_{c even} E_c (E_c the τ = 2c eigenspace of T ⊗ Q). (Lemma L: X̄ ≅ coker(τ|T^a), and T^a = (1 + a)T = 2π_e(T).)
(b) **𝓢 restricted to even c is the doubled-payment ring in c′ = c/2:** span{2^j C(2c′, j)} = span{4^j C(c′, j)} =: 𝓢^{(2)}. *Proof.* (1 + 2t)^{2c′} = (1 + 4(t + t²))^{c′} = Σ_j 4^j C(c′, j)(t + t²)^j, and the coefficient of t^m is Σ_j 4^j C(c′, j) C(j, m − j), unitriangular in (m, j). ∎ So π_e(T) is an 𝓢^{(2)}-lattice and τ = 2c = 4c′ on it: **X̄(T) = X^{(2)}(π_e T)**, the cokernel of the α = 2 payment on the even half.
(c) **Theorem W̄ (the fold law for Weyl modules of odd μ, hence for every Steinberg family) — PROVED.** Let μ = 2μ₁ + 1 and j ≥ 1. Δ(μ) at shift j is the cyclic module 𝓢|_C, C = [j, j + μ] (Lemma W); π_e(𝓢|_C) = 𝓢|_{C_e} = 𝓢^{(2)}|_{C′}, C′ = [⌈j/2⌉, ⌈j/2⌉ + μ₁] (by (b); a cyclic lattice on a given eigenvalue set is unique up to a diagonal scaling, which commutes with the diagonal operator), which is Δ(μ₁) at shift ⌈j/2⌉ with α = 2 (Lemma W for α = 2: e_j^{(2)}v₀ = Σ_r 4^{j−r}C(J, j−r)v_r is unitriangular). So **X̄(Δ(μ), j) ≅ X^{(2)}(Δ(μ₁), ⌈j/2⌉)**. Flight 2's P-R1 with Φ(Δ(μ₁)) = Δ(2μ₁ + 1) (flight 2 A.1(d)) gives X(Δ(μ), j) = (units) ⊕ 2·X^{(2)}(Δ(μ₁), ⌈j/2⌉), hence 2X ≅ X^{(2)}(Δ(μ₁), ⌈j/2⌉) ≅ X̄. ∎ For λ = 2^k − 1 (T = Δ = St_k) this is **the fold law family by family for every Steinberg family and every shift i ≥ 1.**
(d) **Why the general family is harder (pencil, with the T(2) example).** For λ = 2λ₁ + 1, T = Φ(N), the eigen-frame gives π_e(exp(u/2)T) = cosh(u/2)N + u·sinh(u/2)N inside N ⊗ Q, while 2X ≅ X^{(2)}(N) lives on exp(F_N/4)N. Writing y = F_N/4: cosh(u/2) = Σ_s y^s/(s!(2s−1)!!), exp(F_N/4) = Σ_s y^s/s!: **the same divided-power series up to an odd unit in every coefficient.** For N = T(2) the two lattices are L_β = ⟨b00 + (b01+b10)/4 + β b11, b01 + b11/4, b10 + b11/4, b11⟩ with β = 1/48 (fold) and β = 1/16 (doubling): ~~not related by any floor-preserving scaling (a parity obstruction)~~ **[CORRECTED Sun Oct  4 09:49:27 CEST 2026 (time pasted from date; a typed «09:58» written first was wrong and is replaced here), error E5: I had only tried scalar maps on floor 1. With a full GL₂ on floor 1 a graded isomorphism L_{1/16} → L_{1/48} exists: γ₀ = 1, γ₁ = [[3, −2], [0, 9]] (row sums ≡ 1, column sums ≡ 3 mod 4, total 10), γ₂ = 3; the conditions are G(1,1)ᵀ ≡ γ₀(1,1)ᵀ, (1,1)G ≡ γ₂(1,1) (mod 4) and 3γ₂ − γ₀ − 3(ΣG − 2γ₀) ≡ 0 (mod 16).]** So for N = T(2) the two lattices ARE isomorphic as 𝓢^{(2)}-lattices, and the equality of the Smith forms is structural, not a coincidence. This suggests conjecture (Q) of §3.6.

### 3.6 Explicit lattices and the reduction of odd families to one perturbation statement — MEASURED + PROVED reduction
- **Engine engines/tilt_dp.py:** T(l) over Z_(2) with every divided power F^{(m)} and the floor D, by flight 2's moves (T(2l+1) = Φ(T(l)), T(2l+2) = V ⊗ Φ(T(l)); Φ's divided powers as in flight 2 A.1(b)). Gate **PB.3 (logs/fold_odd_gates.log; VIGIA-FIN-OK, 14 MB, 5 s), l ≤ 12, 1 ≤ j ≤ 6:** G1 coker(F + 2(D + j)) = the rule X(l, j): 72/72; **G2 the fold law X̄ = 2X computed directly on T(l) (Smith form of [τ | a − 1], a = (−1)^{D+j}exp F): 72/72** (independent of the peeling of §3.2); **G3 my pencil Ψ of §3.4(Φ) gives X̄ for odd l: 36/36.**
- **Reduction (PROVED, pencil).** For λ = 2λ₁ + 1 and j ≥ 1, X̄(λ, j) ≅ coker(Ψ) on N = T(λ₁), Ψ = Σ_{m≥1} η_m F^{(m)} + 4(D + ⌈j/2⌉) with η₁ a unit (η₁ = 1 for j even, 1/3 for j odd; a floor scaling s_{f+1} = η₁ s_f turns η₁F into F and multiplies the other terms by units). And 2X(λ, j) ≅ coker(F + 4(D + ⌈j/2⌉)) (P-R1). **So the fold law for every odd family is equivalent to the following statement at α = 2 on N = T(λ₁):**
  **(P) coker(F + 2^α(D + c) + Σ_{m≥2} ζ_m F^{(m)}) ≅ coker(F + 2^α(D + c)) for every sequence ζ_m ∈ Z_2.**
- **PB.4 (sealed 30 %): (P) HELD in 300/300 trials** (random integers |ζ_m| ≤ 9, l₁ ≤ 10, c ≤ 5, α = 2; logs/fold_P.log, VIGIA-FIN-OK, 13 MB, 9 s). The higher divided powers of F never change the cokernel.
- **Why (P) should be provable (pencil sketch, not yet a proof).** On Φ(N′) the perturbed operator stays in a «perturbed dance class»: F^{(2s)} = F_{N′}^{(s)}/(2s−1)!! on both slots and F^{(2s+1)} = (unit)·F_{N′}^{(s)} or (2s+2)/(2s+1)!!·F_{N′}^{(s+1)} across the slots, so after eliminating the unit pivots b1 ↦ b0 (as in P-R1, with b1-coefficient U₁ = 1 + Σ_s ζ_{2s+1}F^{(s)}/(2s+1)!!, invertible) one gets 2·[F·(unit) + 2^{2α}(⌈j/2⌉ + D)·(unit) + Σ_{m≥2} ζ′_m F^{(m)}] on N′, the cross terms 2^α ζ₂ F(j + 2D) being 2F times an even number when α ≥ 2. So (P) at α propagates to (P) at 2α one level down, and at the bottom (N = Z, F = 0) there is nothing left. Making this an induction through the even step (V ⊗ Φ, with couplings) is what remains.
- **PB.5 (scope of (P); engines/P_scope.py, logs/Pscope_*.log, all VIGIA-FIN-OK, ≤ 13 MB, ≤ 8 s).** (P) **FAILS at α = 1** (constant ζ: 115 of 225 tilting trials, 175 of 330 Weyl trials) and **fails with floor- or entry-dependent ζ at α = 2** (147/250 tilting, 120/360 Weyl); it **holds at α = 2 with constant ζ** (Weyl modules 330/330, tilting 300/300). So (P) is a delicate statement: the coefficients must be constant (an element of the divided-power algebra Z_2⟨F⟩) and the payment must be at least 4.
- **Conjecture (Q) (stronger than (P), suggested by the corrected T(2) computation):** for N = T(λ₁), the operators Ψ = Σ_m η_m F^{(m)} + 4(D + c) and Σ = F + 4(D + c) are **conjugate over Z_2** (equivalently π_e(Φ(N)) ≅ N as 𝓢^{(2)}-lattices). It holds for Weyl modules (cyclic lattices on the same eigenvalue set are graded-isomorphic) and for N = T(2) (above).
- **PB.6 (sealed 55 %): (Q) HELD** — engines/Q_conj.py computes the Z_2-lattice of integral intertwiners G (GΨ = ΣG; G = e^{−F/4}·γ·e^{κ(F)} with γ floor-graded, κ = Σ_m ζ_m F^{(m)}/(4m)) and searches it mod 2 for an invertible element: **found for every l₁ ≤ 6 and j = 1, 2, 3, 4 (24/24)** (logs/Q_conj_fold.log; VIGIA-FIN-OK, 16 MB, 12 s). A first run said «not found» everywhere, even for Δ(3) where cyclicity proves the opposite; the cause was a float leak (error E7: mat_mul returned the integer 0 for empty sums and mexp divided it). That run is kept as logs/Q_conj_fold_INVALID_float_bug.log and is not a result. The other gates (PB.3) never divide a product and are unaffected. Explicit check (logs/Q_debug.log): for N = Δ(3), γ = diag(1, 1, 3, 15) = diag((2f − 1)!!) and **G = [[1,0,0,0],[0,3,1,0],[0,0,1,0],[0,3,0,15]]** (basis b0b0, b0b1, b1b0, b1b1 of Φ(V)) is integral, invertible and intertwines. The odd double factorials are Φ's own units (F^{(2s)} = F_N^{(s)}/(2s−1)!!).
- **What (Q) would give.** If (Q) holds for N = T(λ₁), then (T^a, τ) ≅ (N, F + 4(D + ⌈j/2⌉)) as Z_2[x]-modules, so X̄(2λ₁+1, j) ≅ X^{(2)}(λ₁, ⌈j/2⌉) ≅ 2X(2λ₁+1, j) for **every** shift j at once: the fold law for every odd family, with a structural reason («the even half of Φ(N) is N»).
- **Why (Q) is special to α = 1 (pencil).** For α ≥ 2 the even restriction of 𝓢^{(α)} is 𝓢^{(α+1)} ((1 + 2^αt)^{2c′} = (1 + 2^{α+1}(t + 2^{α−1}t²))^{c′}), while «doblar» doubles α; only at α = 1 do α + 1 and 2α agree. So the mirror that doubles exists only on the cube itself (α = 1), as it must: there is no fold involution for α ≥ 2 (the units of order 2 of Z_2[s]/(s(s − 2^α)) are ±1 only).
- **The even families reduce to (Q) plus a comparison of two gluings (PROVED reduction, pencil).** For λ = ν + 1, ν = 2λ₁ + 1 odd, Theorem E gives X̄(λ, i) = coker(f on T(ν)), f = 1 + τ − a = 4⌈c/2⌉ on the τ = 2c eigenline. In the eigen-frame Λ ⊂ Λ_e ⊕ Λ_o (index 2^d, the graph of a gluing φ̄: Λ_e/2 ≅ Λ_o/2 — Lemma L). By (Q) at shift i, (Λ_e, f) ≅ (N, σ_A := F + 4(D + ⌈i/2⌉)); by (Q) at shift i + 1 (the J-odd floors at shift i are the J-even floors at shift i + 1), (Λ_o, f) ≅ (N, σ_C := F + 4(D + ⌈(i+1)/2⌉)). So **X̄(λ, i) = coker(σ_A ⊕ σ_C on N ⊕ N glued by the fold**, i.e. on the graph of an F̄-equivariant automorphism ω̄ of N/2N). Flight 2 C.7.4 gives **2X(λ, i) = coker(Ξ) = coker(σ_A ⊕ σ_C on L(N ⊕ N))**, L = [[1, 0], [1/2, 1]], which after scaling the first copy is the graph of **the identity** of N/2N. So the even-family fold law is: the two gluings (ω̄ and id) give the same cokernel — true if ω̄ lifts to automorphisms of (N, σ_A) and (N, σ_C).
- **PB.7 FAILED (sealed 35 %; engines/Q_nat.py, logs/Q_nat.log, VIGIA-FIN-OK, 13 MB, 13 s).** On a long Weyl module the intertwiner's diagonal is forced: **γ_f = (2f − 1)!! for j even and (2f + 1)!! for j odd** (Δ(15), printed in the log). But the «natural» G = e^{−F/4}·diag(γ(D))·e^{κ} is integral only on the Steinberg lattices (l₁ = 1, 3, 7: 3 of 12 for each j); on every other T(l₁) it intertwines but is not integral. So (Q), which holds by PB.6, needs an intertwiner that depends on the Weyl-filtration structure of N, not a universal formula.

### 3.7 Lemma Z0 (shift 0 follows from large even shifts) — PROVED, pencil
For the family λ = n at shift 0 (the only one with a free summand): write τ_t = τ₀ + t·1. For r ≤ rank τ₀ = dim − 1 the r-th determinantal divisor of τ_t equals that of τ₀ as soon as v₂(t) exceeds it (some r×r minor has a non-zero constant term of minimal valuation), and the last one tends to ∞. So for N large, X(λ, 2^N) = X_fin(λ, 0) ⊕ Z/2^{e_N} with e_N → ∞, and likewise X̄(λ, 2^N) = X̄_fin(λ, 0) ⊕ Z/2^{ē_N} (the matrix [τ_t | a − 1]; the sign (−1)^{2^N} = (−1)^0, so the same a). Hence **if the fold law holds for the family λ at all large even shifts, it holds at shift 0** (compare the bounded parts). With Theorem W̄ this settles shift 0 for every Steinberg family.

### 3.8 More measurements of (Q), and why no natural isomorphism exists
- **(Q) HELD for every l₁ ≤ 13, both shift parities** (logs/Q_conj_7_9.log, 6/6, 14 MB, 5 s; logs/Q_conj_10_13.log, 8/8, 39 MB, 324 s): with PB.6, **38/38 cells**. So for every odd family λ = 2l₁ + 1 ≤ 27, (T^a, τ) ≅ (T(l₁), F + 4(D + ⌈j/2⌉)) as Z_2[x]-modules.
- **The obstruction to a natural isomorphism (pencil).** Write Φ(N) = B ⊗_A N, A = Z_2⟨F_N⟩, B = A[u]/(u² − 2F_N), ι: u ↦ −u. The fold is a = ε·exp(−u)·ι (a Galois-twisted involution). A natural isomorphism T^a ≅ N would be a Hilbert-90 splitting β ∈ B^× with β/ι(β) = ε·exp(u); over B ⊗ Q the solutions are β = λ(F)·exp(u/2), and cosh(u/2) = Σ_s F^{(s)}/(4^s(2s−1)!!) has denominators 4^s that no even λ(F) ∈ A ⊗ Q removes. So the class of exp(u) in H¹(Z/2, B^×) is not trivial: the even half of Φ(N) is isomorphic to N only module by module (PB.6, §3.8), never by a formula in F (PB.7).

### 3.9 Status of Leg B — the folded cube's rule
**The rule (stated).** For every n ≥ 1:
  **Syl₂ K̄(n) ⊕ Z₂ ≅ ⊕_λ [ ⊕_{a=1}^{k−2} (Z/2^a)^{2^{|I|+k−2−a}} ⊕ (PAVA of the raw clocks u(D) − 1) ]^{m_λ(n)}**
— the rule of K with every big clock lowered by one (all big clocks are ≥ 2, Lemma B, so none disappears) and the small layers shifted down (the layer a = 1 disappears: those are the a_n Z/2's). Equivalently X̄(λ, i) ≅ 2·X(λ, i) for every family.
**Grade:**
- **PROVED** (pencil): the reduction to families (Lemma RT̄), the fixed lattice (Lemma L), the fold as the even restriction (Lemma Π), shift 0 from large shifts (Lemma Z0); the rule **for every Steinberg family λ = 2^k − 1 at every shift** (Theorem W̄) and for λ = 2 (§3.4).
- **PROVED reductions:** odd families ⟺ (Q) (conjugacy, §3.6); even families ⟸ (Q) at shifts i, i + 1 plus the comparison of two gluings of N ⊕ N (§3.6).
- **MEASURED:** the family-by-family rule for λ ≤ 12, all shifts tested (114 + 72 cells), (Q) for l₁ ≤ 13 (38 cells), and the whole groups (§3.10 gate below).
- **NOT PROVED:** (Q) for a general tilting lattice, and the gluing comparison. **Leg B: NO CONCLUYO** (for a pencil proof for every n); the rule itself is stated, gated, and proved on the Steinberg families.
- **[Added after Leg C, written Sun Oct  4 10:31:32 CEST 2026 (pasted)] With the exact certificates of §4.3 the rule is PROVED for every family λ ≤ 20 and every odd family λ ≤ 27, at every shift**, hence the whole rule for K̄(n) for every n ≤ 21 and n = 23, 25, 27 (Corollary C₂). Direct check on explicit lattices (PC.4, logs/fold_odd_gates_20.log; VIGIA-FIN-OK, 15 MB, 40 s): X̄ = 2X in 80/80 cells λ ≤ 20, j ≤ 4; Ψ formula 40/40.

### 3.10 Gate of the stated rule for K̄ (engines/legB_gate.py, logs/legB_gate.log; estimate < 150 MB / 2 min; VIGIA-FIN-OK, 4 MB, 0 s) — MEASURED
- **PB.8 (sealed 99 %) HELD.** (1) **Whole groups: the K̄-rule equals turnos.py's folded groups for n = 3..13 (11/11)**, e.g. n = 13: {1:364, 2:64, 3:364, 4:1, 6:560, 7:12, 8:364, 9:1, 10:336, 11:1, 13:12}. (2) **The note's two PROVED layers of the folded cube** (r₀ = 2^{m−1} + 2^{m−ρ−1}, §1.4; r₁ = Σ_s C(ρ,s)2^{m−ρ−s}κ(s−1) + 2^{m−ρ} − [m ≡ 1 mod 4]2^ρ, §6.3 with M = f; m = n − 1): **0 failures for 3 ≤ n ≤ 40.** Controls: the unlowered rule and the rule lowered by two match turnos in 0 of 11 cells and the layers in 0 of 38.



## 4. Leg C — the fold law for every n

**Estimate (written Sun Oct  4 10:08:16 CEST 2026, pasted from `date`; a typed «10:12» first written here was wrong — error E8; before the leg):** 15–20 % of the flight. Plan: (1) the fold law from the family-by-family law (Krull–Schmidt), with every dependency named; (2) what is PROVED unconditionally (small n by pencil); (3) turn (Q) into **exact certificates** (an explicit integral intertwiner G with odd determinant and GΨ = ΣG, independent of the shift) for every l₁ ≤ 13 and both shift parities, verified by a separate script from scratch — this proves the fold law for every odd n ≤ 27; (4) gate against the measured n = 3..13; kill criterion. Machine: certificate search and verification < 600 MB, < 10 min.

### 4.1 Lemma N (exact shift-uniform normal forms of the even step) — PROVED, pencil (from flight 2 B.1)
Let λ = 2l₁ + 2, N = T(l₁), Σ_c := F + 4(D + c) on N. Flight 2 B.1 gives 2X(λ, i) ≅ coker Ξ_i on N_A ⊕ N_C, Ξ_i = [[F + π_A(D), 0], [κ(D), F + π_C(D)]], π_A(f) = −2(i+2f)(i+2f+1), π_C(f) = −2(i+2f+1)(i+2f+2), κ(f) = −2(i+2f+1).
- **i = 2c even:** π_A = −4(c + D)u, π_C = −4(c + 1 + D)u, κ = −2u with the SAME odd unit u(f) = 2(c + f) + 1. Right-multiplying by diag((−u)^{−1}, (−u)^{−1}) and conjugating both blocks by the floor scalars s(f+1) = s(f)(−u(f))^{−1} gives exactly **2X(λ, 2c) ≅ coker [[Σ_c, 0], [2, Σ_{c+1}]]** (= L^{−1}diag(Σ_c, Σ_{c+1})L, L = [[1,0],[1/2,1]]).
- **i = 2c − 1 odd:** π_A = −4(c + D)u_A, π_C = −4(c + D)u_C, κ = −4(c + D), u_A(f) = 2(c+f) − 1, u_C(f) = 2(c+f) + 1. After the two normalisations the coupling is 4(c + f)·Π_{g<f}(u_C(g)/u_A(g))/u_A(f), and the product **telescopes** to u_A(f)/(2c − 1): the coupling is 4(c + D)/(2c − 1); rescaling the C copy by the constant 2c − 1 and subtracting the first block row from the second (4(c + D) = Σ_c − F) gives exactly **2X(λ, 2c − 1) ≅ coker [[Σ_c, 0], [−F, Σ_c]]** (= Q·diag(Σ_c, Σ_c)·Q^{−1}, Q = [[1,0],[F/4,1]], since [Σ_c, F/4] = F).
Both normal forms Ξ′_c, Ξ″_c satisfy Ξ_{c+1} = Ξ_c + 4: **shift-uniform**, like X̄ (τ_{i+2} = τ_i + 4 on T^a, a depending only on the parity of i). So the even-family fold law at every shift of a parity follows from ONE conjugacy (T(λ)^a, τ_i) ≅ (N ⊕ N, Ξ′ or Ξ″) — call it **(Q_even)** — which can again be certified exactly.

### 4.2 The fold law from the family law — PROVED, pencil
By Lemma RT̄, C ⊗ Z_2 = ⊕_λ X(λ, i)^{m_λ(n)} and C̄ ⊗ Z_2 = ⊕_λ X̄(λ, i)^{m_λ(n)} (i = (n − λ)/2), with exactly one free Z_2 on each side (λ = n, i = 0). If X̄(λ, i) ≅ 2X(λ, i) for every family present, then C̄ ⊗ Z_2 ≅ 2(C ⊗ Z_2), and cancelling the free Z_2 (finitely generated Z_2-modules) gives **Syl₂ K̄(n) ≅ 2·Syl₂ K(Q_n)**, i.e. Syl₂ K ≅ (Z/2)^{a_n} ⊕ [Syl₂ K̄ with every exponent raised by one], a_n being Bai's count (Leg 0).

### 4.3 Certificates — the family law for every family with λ ≤ 20 and every odd family with λ ≤ 27, at every shift
- **Odd families (engines/cert_Q.py, cert_Q_verify.py, cert_Q_control.py; logs/cert_Q_1_10.log, cert_Q_11_13.log, cert_Q.txt, cert_Q_verify.log, cert_Q_control.log; all VIGIA-FIN-OK, ≤ 39 MB, ≤ 194 s).** For every l₁ ≤ 13 and both shift parities, an explicit matrix G (entries in Z_(2), odd determinant) with **G·Ψ_j = (F + 4(D + ⌈j/2⌉))·G**, written to logs/cert_Q.txt. **PC.1 HELD: 26/26 certificates valid**, re-checked from scratch at three shifts not used in the search. Control that can fail: each certificate at the wrong parity — **rejected 52/52**. Since Ψ_{j+2} = Ψ_j + 4 and Σ_{j+2} = Σ_j + 4, one G serves every shift of its parity.
- **Even families (engines/cert_Qeven.py, cert_Qeven_verify.py; logs/lemmaN_gate.log, cert_Qeven_0_5.log, cert_Qeven_6_7.log, cert_Qeven_8.log, cert_Qeven_9.log, cert_Qeven.txt, cert_Qeven_verify.log, cert_Qeven_ctrl_which.log; all VIGIA-FIN-OK, ≤ 60 MB, ≤ 282 s).** **PC.2 HELD:** Lemma N's normal forms equal 2X(λ, i) from the rule in 60/60 cells (λ = 2..20, i = 1..6); control (the other parity's form) differs in 36. **PC.3 HELD:** for every l₁ ≤ 9 (λ = 2l₁ + 2 ≤ 20) and both parities, an explicit G with **G·(τ_i on (1+a)T(λ)) = Ξ′_c G or Ξ″_c G**: **20/20 valid** at three fresh shifts each. Wrong-parity control: rejected 38 of 40; the 2 accepted are both λ = 2 (N = Z, G = [[1,0],[1,3]]), a 2×2 coincidence, identified in logs/cert_Qeven_ctrl_which.log.
- **Theorem C₁ (PROVED: pencil reductions + exact certificates).** For every family λ ≤ 20 and every odd family λ ≤ 27, and every shift i ≥ 0: **X̄(λ, i) ≅ 2·X(λ, i)**.
  *Proof.* i ≥ 1: Lemma L(b) gives X̄ = coker(τ_i on T^a). Odd λ = 2l₁ + 1: T^a ≅ N = T(l₁) carries τ_i to Ψ_j (§3.4(Φ), gate G3), the certificate conjugates Ψ_j to Σ_{⌈j/2⌉}, and P-R1 (flight 2) gives coker Σ = X^{(2)}(l₁, ⌈j/2⌉) ≅ 2X(λ, j). Even λ = 2l₁ + 2: the certificate conjugates τ_i on T^a to Lemma N's normal form, whose cokernel is 2X(λ, i). Steinberg families also by Theorem W̄ (pencil only). i = 0: Lemma Z0 from the large even shifts. ∎
- **Corollary C₂ — the fold law 2K(Q_n) ≅ K̄(n) on 2-parts, and the rule for K̄ (§3.9), hold for every n ≤ 21 and for n = 23, 25, 27** (every family of Q_n is then covered: for odd n all families are odd with λ ≤ n; for even n ≤ 20 all families are even with λ ≤ 20; n = 21 is odd). **The cells n = 14..21, 23, 25, 27 are new: never computed directly** (turnos.py reached n = 13), now proved. For instance the rule gives Syl₂ K̄(15) and Syl₂ K̄(27) explicitly (f5lib spectrum lowered by one).
- **Dependencies, named:** the closed rule (flights 1–4: RT, Theorem D, RT′, Theorems O, U, F); flight 2's Φ (A.1), P-R1 (A.2) and B.1 (the even step); Lemma F, B (Leg 0); Lemmas RT̄, L, Π, Z0, N and the derivation of Ψ (§3.4) (this flight, pencil); the standard tilting facts cited for RT (Jantzen II.4.13, II.B, II.E; idempotent lifting); Donkin's tensor product theorem; 46 exact certificates (machine-found, machine-verified as exact rational identities; they are finite objects in logs/cert_Q.txt and logs/cert_Qeven.txt and can be re-checked by anyone).

### 4.4 For every n — conditional, and the gate
- **Theorem C₃ (conditional, PROVED reduction).** If (Q) holds for every tilting lattice T(l₁) (both parities) and (Q_even) for every T(2l₁ + 2) (both parities), then the fold law holds for every n. Both statements are measured/certified for l₁ ≤ 13 and l₁ ≤ 9 respectively, and fail for no tested case.
- **Gate against the measured n = 3..13 (whole groups):** §3.10 (PB.8): 11/11. Also the family-by-family measurement λ ≤ 12 (114 cells) and the direct lattice computation (72 cells).
- **Kill criterion: did not fire.** No n with 2K ≇ K̄ on 2-parts was found; the law is now proved for n ≤ 21 and n = 23, 25, 27.
- **Leg C: NO CONCLUYO for every n** (the general (Q) and (Q_even) are not proved by pencil); **CLOSED for n ≤ 21 and n = 23, 25, 27.**


## 5. Images — which served

- **The mirror that doubles — SERVED, twice, literally.**
  - In Leg A the mirror is the binary digit 0: adding it to every tilting family of the odd cube 2^K − 1 splits each dancer D into twins D and D ∪ {0} with the same raw clock. «The cube 2^k is the cube 2^k − 1 seen twice in a mirror, plus one tower on top»: the tower is the dancer {0} of the top family, at 2^K + K − 1.
  - In Leg B the mirror is the fold a = (−1)^c on the eigenline of eigenvalue 2c. Folding keeps the even half of the eigenvalues, and **the symmetric functions restricted to even c are exactly the doubled-payment ring** (𝓢|_{even} = 𝓢^{(2)}): folding the cube is literally doubling the payment. That proves the law for Steinberg families, and it is why the mirror exists only on the cube itself (α + 1 = 2α only for α = 1).
- **«Binario, o está o no está… en el doble de horas» — SERVED.** The doubling of hours is flight 2's P-R1 (X = units ⊕ 2·X^{(2)}); the fold law says that the fold reaches the same doubled problem without the factor 2.
- **«Se van turnando» — SERVED as the sign (−1)^c:** consecutive floors alternate between the folded and the anti-folded halves; on the anti-folded half the Laplacian has valuation exactly 1 (the floors that «owe» one factor 2).
- **The wound — SERVED lightly:** the shift 0 (the sink, the free Z) is healed by large even shifts (Lemma Z0): the free summand is the limit of a factor whose exponent runs to infinity.
- **The gold — SERVED in Leg A:** the gold of the new digit 0 (gap t₁) pays exactly the missing carries v₂(J) = t₁ − 1, so the twin D ∪ {0} keeps the clock of D.
- **The rent, the plumber — not used.**

## 6. Sealed predictions, hits and failures

All in checks/SEALED.md, each sealed (time pasted from `date`) before its run.
| id | prediction (odds) | ended |
|---|---|---|
| P0.1 | Lemma F = peeled multiplicities, n ≤ 200 (99.5 %) | **held**; control fired (198 n) |
| P0.2 | m₀ = 0, m₁, m₂ powers of 2 (99.5 %) | **held** |
| P0.3 | every big clock ≥ 2 (99 %) | **held** (3 660 cells) |
| P0.4 | Bai's counts from the rule, n ≤ 120 (99.5 %) | **held**; control fired (59 n) |
| PA.1–PA.5 | Lemma M, Lemma A, twins, pooled doubling, Conj. 5.4 K ≤ 9 (98–99.5 %) | **held**; twins control fired at all 93 other odd N; no-top-factor control fired 9/9 |
| PB.0 | fold law family by family, λ ≤ 9 (55 %) | **held** 79/79 (then 114/114, λ ≤ 12) |
| **PB.1** | **the fold law is a general lemma for Z₂[C₂]-lattices (35 %)** | **FAILED**: 168/632 (d = 3), 432/768 (d = 4) |
| PB.2 | cyclic 𝓢-modules: Weyl intervals (60 %), random free sets (40 %) | **held** 136/136 and 147/147 |
| PB.3 | explicit lattices: G1 (98 %), G2 (97 %), G3 Ψ formula (85 %) | **held** 72/72, 72/72, 36/36 |
| PB.4 | perturbation (P) at α = 2, constant ζ (30 %) | **held** 300/300 |
| **PB.5** | scope of (P): α = 1 (50 %), entry-wise ζ (60 %), unit factors (60 %), Weyl α = 2 (70 %) | **mixed: α = 1 FAILED, entry-wise FAILED, units FAILED; Weyl α = 2 held 330/330** |
| PB.6 | conjecture (Q) (55 %) | **held** 24/24 (after the invalid run of E7), then 38/38 |
| **PB.7** | a natural intertwiner e^{−F/4}diag(γ)e^{κ} (35 %) | **FAILED**: integral only on Steinberg lattices (3/12 per j) |
| PB.8 | K̄-rule vs turnos n = 3..13 and the note's layers n ≤ 40 (99 %) | **held** 11/11 and 38/38; controls 0 |
| PC.1 | 26 odd certificates (90 %) | **held** 26/26; wrong-parity control rejected 52/52 |
| PC.2 | Lemma N normal forms, 60 cells (97 %) | **held**; control differs 36 |
| PC.3 | 20 even certificates (80 %) | **held** 20/20; control rejected 38/40 (the 2 accepted: λ = 2, identified) |
| PC.4 | direct lattices λ ≤ 20 (98 %) | **held** 80/80, 40/40 |
**Failures, in the same type: PB.1 FAILED; PB.5 FAILED in three of its four parts; PB.7 FAILED.**

## 7. My errors

- **E1 (Leg 0 estimate not fully prior).** The fusion rule and m₀ = 0 came to me while reading flight 5's §2.4, a few minutes before the Leg 0 estimate was written (said in the estimate itself).
- **E2 (Leg A estimate not fully prior).** The comparison of raw clocks of Leg A was done in my head between 09:04 and 09:07, right after reading Gao's statement and before the Leg A estimate was written (said in the estimate). It was written down at once, before any gate.
- **E3 (stray file).** A heredoc slip created an empty REPORT.md.tmp; I cannot use rm, so it was renamed scratch_empty.tmp (empty, inside the folder).
- **E4 (killed run, meaningless run).** fold_cyclic_test v1 (sympy HNF) was killed by the watchdog at 1.46 GB, 15 s (kept as logs/fold_cyclic_intervals_KILLED.log, not a result); its random-set run included sets that are not Z₂[a]-free, so it was not meaningful and was redone (v2, with a freeness filter) under the same sealed prediction PB.2.
- **E5 (a wrong claim, corrected).** In §3.5(d) I wrote that the two lattices of N = T(2) are «not related by any floor-preserving scaling (a parity obstruction)». I had only tried scalar maps on floor 1; a full GL₂ map exists. Corrected in place (struck through) with the explicit isomorphism.
- **E6 (one run outside the watchdog).** A debug command ran `python3 engines/Q_debug.py` directly; it crashed at import in 0 s and produced nothing. All results come from vigia runs.
- **E7 (a float leak; an invalid run).** mat_mul returned the integer 0 for empty sums and mexp divided it, producing floats. The first run of Q_conj said «no invertible intertwiner» everywhere, even for Δ(3) where cyclicity proves the opposite; I did not accept it, found the bug, and kept the run as logs/Q_conj_fold_INVALID_float_bug.log. The gates that never divide a product (PB.3) were unaffected.
- **E8 (typed times).** Twice I typed a time instead of pasting it («09:58» in the correction of E5; «10:12» in the Leg C estimate); both were replaced by the pasted `date`, and the replacement says so. A third time-stamp («10:30:00») was pasted but from the previous command; replaced by the right one (10:31:32).
- **Crashes at first launch (not results):** fold_cyclic_test v1 (wrong sympy import path) and Q_conj / Q_debug (fold_odd_gate, Q_conj and P_scope ran their main code at import) crashed in 0 s; fixed (import path; `__name__` guards, no change of logic); each is in the diary.

## 8. The story of this flight, in plain words

- **The calibration was bookkeeping.** Reading flight 5's peeling of multiplicities, I asked what V ⊗ T(λ) is, and Donkin's product formula answers it in one line: X₀ · X₀ = X₁ + 2. From that, T(0) never comes back after the first step, and T(1), T(2) double every two steps. With «every family gives half its dimension in factors, a quarter of it in Z/2's», Bai's two counts fell out. That was the test the mission asked for: the rule can count.
- **The mirror of Leg A was the digit 0.** For an odd cube every family moves up by one (T(λ) ⊗ V = T(λ + 1)), keeping its shift, and gains the digit 0. So each dancer D has two children, D and D ∪ {0}. I wrote the raw clock at n = 2^K − 1 and at 2^K with the carries computed from the complement of the bits (2^K − 1 is all ones), and the two children came out with exactly the parent's clock: one because nothing changes, the other because the gold of the new digit (its gap t₁) pays exactly the carries that disappear (v₂(J) = t₁ − 1). Doubling every clock doubles every pool. Gao's top factor is the child {0} of the free dancer. This took minutes and was in my head before its estimate was on disk (E2).
- **The fold is the group, the cube is the Lie algebra.** In flight 1's dictionary the cube's Laplacian is the Lie action of one 2×2 matrix and the fold a = x₁⋯x_n is the group action of the same matrix. So the folded cube splits along the same tilting families. That turned the mission's §3 hint («look at how a acts on each family») into an exact statement.
- **The family-by-family law held at once (79 cells, then 114), and then it resisted.** My first hope, a general lemma about lattices with an involution, failed on random examples (PB.1). Going back to the families, I noticed that every family carries all the elementary symmetric functions e_j, not only σ and a; Weyl modules are cyclic for them; and the fold keeps only the even eigenvalues. The symmetric functions on even c are exactly the payments doubled. So folding a Steinberg family IS the doubling of flight 2: the law for every Steinberg family, by pencil.
- **The odd families became one question.** Writing the odd step with the fold, I found the folded operator is the doubled operator with F replaced by a series Σ η_m F^{(m)} whose coefficients are odd (Bernoulli numbers: von Staudt–Clausen). The higher divided powers never changed anything in 300 random trials, but floor-dependent ones did, and α = 1 did: a delicate fact. A computation by hand for N = T(2) first looked like an obstruction (E5), and when I corrected it, it became an isomorphism; that suggested the stronger conjugacy (Q). Its first test said «false» even where I had proved it true — a float leak (E7); after the fix (Q) held everywhere.
- **No formula, but certificates.** The intertwiner on Weyl modules has the odd double factorials (2f − 1)!! on its diagonal, and I hoped it was universal: it is not (PB.7), and I found why — a natural isomorphism would be a Hilbert-90 splitting of exp(u) for the quadratic extension A[√(2F)], and the 4^s denominators forbid it. So I made each conjugacy a finite object: an explicit integral matrix with odd determinant, valid for every shift of a parity because both sides move by +4. Twenty-six for the odd families, and, after the even step of flight 2 turned out to normalise exactly (its units telescope), twenty for the even families. Checked from scratch at fresh shifts, with controls that reject them at the wrong parity.
- **Where it leaves the law.** The fold law is proved for every n ≤ 21 and n = 23, 25, 27 — eight cells beyond any direct computation — and for every n it is reduced to two conjugacies, (Q) and (Q_even), that never failed. The general proof needs a reason why the even half of Φ(N) is isomorphic to N for every tilting N; the descent obstruction says that reason cannot be a formula in F alone.

## 9. Files with md5

(Sun Oct  4 10:32:59 CEST 2026. REPORT.md and logs/DIARY.md are still being written and are not listed. material/ and MISSION.md verified unchanged against MANIFEST_md5.txt: 251 of 252 entries match; only CLAUDE.md differs, by its STATE line, as the mission orders. The list is also in logs/_md5_f6.txt.)
```
bcefbe58a7934ce3d566161523d6737d CLAUDE.md
3467d96547869afee7f6e0e8d86dcb6a MISSION.md
5127e664eefe77a5280dd2be5e6f09c4 checks/SEALED.md
bcfceb12dcbf34065ece8461478c514e engines/P_scope.py
70e00d6627b85df503c07809f12ead40 engines/Q_conj.py
be65d964625467d9c4277555f07c187b engines/Q_conj_range.py
e3763a63c18388d6c5c9d1798faa7a44 engines/Q_debug.py
b3bf262299ac6c0823bc991e21dcd01d engines/Q_nat.py
e9c5700cc28a5e7a5b31e5bdd7e83c83 engines/capas.py
29e89334d6a234e8e6b11e9df6b42a2d engines/cert_Q.py
00798810fc6acc719928e66b8b4ec057 engines/cert_Q_control.py
ecf429a9b52e0bfad8b8c48689646627 engines/cert_Q_verify.py
fa218fb04fa2c4febc27cfede8e0b92a engines/cert_Qeven.py
d78e6ac5d98ccc5ebc0913566c02caf5 engines/cert_Qeven_ctrl_which.py
0b036a4d84affcb42f61160915cb6806 engines/cert_Qeven_verify.py
9b1a59cd79ab654041a65aca4db88dc3 engines/f5lib.py
1c693a7aa3be3b02c5f89ac572f41238 engines/fold_cyclic_test.py
87656007ba91a5bd434b7c0bc8c4a455 engines/fold_fam.py
c33eef6297ec20dfddce629e775e7443 engines/fold_lemma_test.py
58f4e81e5c67c75cd2f7a9447113c651 engines/fold_odd_gate.py
63431602ceb8ad4b499c4c5c6dd09424 engines/leg0_gate.py
923278248b3b8af691ddf85ee117afd5 engines/legA_gate.py
1dbc82b4ec4dd97986b82ca9edfdfbd8 engines/legB_gate.py
fb5c804bd68d88d14026d0d255600632 engines/rulew.py
e3d9f8ea9a187a1d74144a07d39366de engines/tilt_dp.py
fc5adc9b8c6a42430f1bcaca8f01c9a8 engines/turnos.py
2171d0db55ee854ab33ee2bf53c6c358 logs/AUDITOR_smoke_test_of_material.log
4890a8bfd4653d41b05a3db63099efa1 logs/AUDITOR_smoke_turnos.log
39d6f1c49e1484c54c5b75ca0ca1c41f logs/Pscope_const_tilt_1_10_5.log
a3ec595f96d389df7e664fdf0aa3649b logs/Pscope_const_weyl_1_12_6.log
f4d04fd2b7c1a472625d727a11ca8745 logs/Pscope_const_weyl_2_12_6.log
c30ac261290643157a10c8691479d16e logs/Pscope_floor_tilt_1_10_5.log
6fe02853a20d1689cc46312e24b61593 logs/Pscope_floor_tilt_2_10_5.log
c3c3cabff337641f266cd123c49b06e3 logs/Pscope_floor_weyl_2_12_6.log
98281d6ce316db188e6507422e03dab4 logs/Pscope_units_tilt_2_10_5.log
27b4cafb06ca9608c6e01cd9e33a5d58 logs/Pscope_units_weyl_2_12_6.log
e3c0f39a472859b892cdd42e0d3e3cc7 logs/Q_conj_10_13.log
feff92ccf102ca14c0ca077201deb89b logs/Q_conj_7_9.log
bbfe28326386e1bb785eb5782f1d2552 logs/Q_conj_fold.log
e24c3ae4e32bae2ffa5242503c817944 logs/Q_conj_fold_INVALID_float_bug.log
2282f8f4ad185cb220daac42a817aede logs/Q_debug.log
6a562497506200c0b96c36ecd1d9d190 logs/Q_nat.log
ba49de73036a495c39d3aba05e0899d2 logs/cert_Q.txt
fd0684717c9d88d437c3c11500c79185 logs/cert_Q_11_13.log
6b18ff526fecf5f023492659a788dda9 logs/cert_Q_1_10.log
588cb8a7b8b03c1253c9605b56c0ac5a logs/cert_Q_control.log
1c6ac84f85b9a4b6b8871fc12fb47263 logs/cert_Q_verify.log
f401440fc09567bedc6bd87c6d2fa441 logs/cert_Qeven.txt
aa2642cb9203d822810545784c50c3e3 logs/cert_Qeven_0_5.log
4dec01a74cde606113b5d5f7004d20f1 logs/cert_Qeven_6_7.log
9372b29a009b9aa0189a1c7fc45ee09e logs/cert_Qeven_8.log
a4270e9940244ff9722ab555d5850ce9 logs/cert_Qeven_9.log
dd67b8f1a84d7c92b913734a0152e675 logs/cert_Qeven_ctrl_which.log
397a3b6891ba01dafa71209ed7cd94e8 logs/cert_Qeven_verify.log
a8d55245add216b767186845f068c0e4 logs/fold_P.log
cc9cceceef43f9ec2afbc5a325174738 logs/fold_cyclic_intervals.log
5453cd493c5d0e92266cd0a4dc6f3af6 logs/fold_cyclic_intervals_KILLED.log
c357c184c46a8665836e31c2fd013b0d logs/fold_cyclic_random.log
95cd26577921a825b893057eb9481253 logs/fold_fam_12_6.log
7eb8c5c6594e29747aff89cbb8039852 logs/fold_fam_9_6.log
2f443b57015e3ec32e62c5ae09282c7b logs/fold_lemma_test.log
42e5b6e3891fc2b63212d43a9d5168ed logs/fold_odd_gates.log
2555270660e11f64f690f9c351f02745 logs/fold_odd_gates_20.log
f1c8cf735ea95a331136461675abb245 logs/leg0_gate.log
40016ebd2a60c042c97287a355e41b02 logs/legA_gate.log
2a776a19f3e736899b6e88eb61e5dd48 logs/legB_gate.log
d21165898f8047c70183b24019e8a068 logs/lemmaN_gate.log
d41d8cd98f00b204e9800998ecf8427e scratch_empty.tmp
e5f8cf13253222f0388fe7dab9edfe88 vigia.sh
```
Notes.
- engines/rulew.py, engines/capas.py, engines/turnos.py are copied unchanged from material/ (same md5 as the originals); engines/f5lib.py is flight 5's file with one changed line (the import path of rulew); engines/smoke/ is the auditor's and is not listed.
- engines/fold_odd_gate.py was edited twice after its first gate (PB.3, logs/fold_odd_gates.log): a `__name__` guard, and the Fraction(0) start of the sums in mat_mul (E7). The final version re-ran the same gates up to λ = 20 (PC.4, logs/fold_odd_gates_20.log) with the same outcome. engines/P_scope.py and engines/Q_conj.py were edited after their runs only by `__name__` guards.
- logs/Q_conj_fold_INVALID_float_bug.log and logs/fold_cyclic_intervals_KILLED.log are not results (E7, E4). scratch_empty.tmp is the empty stray file of E3.
- **The 46 certificates** are logs/cert_Q.txt (26, odd families) and logs/cert_Qeven.txt (20, even families): integer matrices with an odd common denominator; engines/cert_Q_verify.py and engines/cert_Qeven_verify.py re-check them from scratch.
