# REPORT — Mission 4, «Grepy el volador 4»: THE RENT AND THE GOLD

## 0. First line — what this flight closes and what it does not

**KILL CRITERION FIRED: (G½) is false.** In the family **λ = 66** (I = {0,1}, k = 6), α = 1, shift i = 6, the arrow {0,1} → {1} costs 2 and carries gold γ = 5; discounted by ⌈5/2⌉ = 3 it costs −1, below the floor Y(1) = 0 (checked by hand and by exact min-cost flow; 219 such cells with λ ≤ 255; λ = 66 is the very next family with |I| ≥ 2 after the auditor's range λ ≤ 62 — 63, 64, 65 have |I| ≤ 1). The carries of m running through the skipped gap eat the gold. **(G1) — one coin per dancing couple — holds:** PROVED by pencil in the two classes below for every family, and cell by cell (certificates) in all 454 872 cells with λ ≤ 255.

**This flight closes Leg 0** (Theorem A2's case table written out in full: CORRECT, with one GAP — flight 3's sentence «T = U in pattern (1,1,1)» is false when γ > α(2^c − 2^b), first at λ = 10; the floor survives through the chord (U(1)+U(3))/2, gated 7008/7008; St1 and St2 CORRECT). **In Leg A it proves the floor by pencil, for every family, every α and every shift, in two infinite classes of cells:** (a) **every all-short cell** (no carry run of m = i − 1 reaches the next digit of I) — there the pooled clocks are an explicit **reflected walk** (Theorem RW), the ruler's growth bounds it (Lemma Λ), and every arrow pays its half of the pooled drop **with gold to spare** (Theorem H: slack ≥ γ + ν); (b) **every unpooled cell**, jumps and i = 0 included (Lemma P: a negative clock step can only occur where row and column pieces are equal; Lemma M: monotone rulers need no gold at all). A one-line certificate (Theorem U: two monotone «corrected rulers» whose mirror differences are the pooled clocks) unifies both and **exists in every one of the 454 872 checked cells (λ ≤ 255)**. **It does NOT close the floor for every family:** the pooled cells with a full carry window or a jump (9.3 % of the cells with λ ≤ 255; with |I| ≥ 3 the first is λ = 22) are not proved by pencil; there half the gold is not enough (λ = 66). Hence **the whole 2-part of K(Q_n) for every n, Gao et al.'s Conj. 4.14 and 5.4 and the poster's (n+1)-th factor for general n remain open**; Theorem C states exactly which cubes the proved classes close, and the missing step is written in its sharpest form (A.8). No new family or cube was evaluated.

**Addendum (19:12, after the flight): Rafa's image 3, «el fontanero», SERVES as a measured law.** A shared flat and its mirror flat negotiating one deposit together (the cheapest natural deposit, clipped into the window their doors and frontier couples allow) yields corrected rulers in **every** hard cell with λ ≤ 255 (40 523/40 523; control without gold fails 3 849/8 369). With Theorem H and Lemmas M, P, **every cell with λ ≤ 255 now has an explicit rule-built certificate**; the pencil step left is «the joint window is never empty» (§10). Not a theorem yet.


**Mission 4b (20:33, after compaction, Rafa's order — two missions in this flight, both for the auditor): THE FLOOR IS PROVED FOR EVERY FAMILY (Theorem F, §11).** The missing step of C.3 is closed by an induction on the digits: one new self-mirror shared flat per digit, priced between the dearest tenant of its lower half and the cheapest of its upper half. With Theorems D and O: Conjecture W in every cell and the whole 2-part of K(Q_n) for every n (§11.4). The trophies for general n are not derived here.

## 1. Leg 0 — second reading (A2 table, St2)

BUDGET (written Sat Oct  3 17:09:03 CEST 2026, before starting): 15 % of the flight (about 40 min). Pencil first (the whole A2 table, St1/St2 cold), then one gate on the |I| = 2 families with λ ≤ 255 (already checked families: allowed).

### 0.1 Theorem A2 — the case table written out in full (pencil; written into this file 17:10)

**Setting (flight 3 A.1, re-derived).** I = {b, c}, b < c < k, γ = k − c ≥ 1, i ≥ 1, m = i − 1. Dancers 0 = ∅, 1 = {b}, 2 = {c}, 3 = {b,c} (o-order). `A(D) = α o_D + κ(m, o_D)`, `κ(m, 2^t) = r_t` (run of ones of m from bit t). Kummer is additive over disjoint digits: `κ(m, 2^b + 2^c) = r_b + r_c(m + 2^b)`, so **`ι := A3 − A1 − A2 = r_c(m+2^b) − r_c`**. Entries `c_{DD'} = θ(D∖D') + A(D') − A(D) + E_{D'}` (θ(Δ) = k − min Δ; E = the normalised jump `e*·J(o)`):
`c00 = 0, c11 = E1, c22 = E2, c33 = E3, c10 = k − b − A1 = u + γ, c20 = γ − A2 = v, c30 = k − b − A3 = u + v − ι = P, c31 = v − ι + E1, c32 = u + γ − ι + E2`, with `u = (c − b) − α2^b − r_b`, `v = γ − α2^c − r_c`, `s = u − v`.
Clocks `x̂_D = R(D) + C(I∖D)`: `x0 = −P + E3, x1 = s + E2, x2 = −s + E1, x3 = P`; U(r) = sum of the last r clocks.
**Chord criterion** (used throughout): Y ≤ the real convex minorant of U ≤ every chord, so «matching ≥ one chord value at r» ⟹ «matching ≥ Y(r)».

**Carry cases (adding 2^b to m), re-derived bit by bit.**
| case | condition | ι | u |
|---|---|---|---|
| (a) | r_b < c − b (the carry stops below c) | 0 | > −α2^b |
| (b) | r_b = c − b (bits b..c−1 are 1, bit c is 0, so r_c = 0) | 1 + r_{c+1} ≥ 1 | = −α2^b |
| (c) | r_b > c − b (bit c is 1, r_c = r_b − (c−b) ≥ 1) | −r_c < 0, and ι = u + α2^b | = −α2^b − r_c |
**Jump patterns** (J monotone in o; m_low = m mod K): (0,0,1) ⟺ m_low ∈ [K − 2^c − 2^b, K − 2^c): bits b..c−1 = 1, bit c = 0, bits c+1..k−1 = 1 ⟹ case (b), `ι = γ + r_k`. (0,1,1) ⟺ m_low ∈ [K − 2^c, K − 2^b): bits c..k−1 = 1 and bits b..c−1 not all 1 ⟹ case (a), `r_c = γ + r_k`. (1,1,1) ⟺ m_low ≥ K − 2^b ⟹ case (c), `r_b = k − b + r_k`. `e* = −r_k` if r_k ≥ 1, `e* = v_2(⌊m/K⌋ + 2) ≥ 1` if r_k = 0; in all cases **e ≥ −r_k**.

**Pattern (0,0,0), E = 0.** U = (0, P, 2v − ι, P, 0); chords at 1 (and, by the antisymmetry x_{3−j} = −x_j, at 3): {P, v − ι/2, P/3, 0}; at 2: {2v − ι, P, 0}. Five identities:
(i) `c10 − P = γ − v + ι = A2 + ι = α2^c + r_c(m+2^b) > 0`; (ii) `c32 − P = γ − v = A2 > 0`; (iii) `c20 = v`: if ι ≥ 0, v ≥ v − ι/2 (chord); if ι < 0 (case c), `P = v − α2^b < v`; (iv) `c31 = v − ι`: if ι ≤ 0, v − ι ≥ v ≥ a chord by (iii); if ι > 0 (case b), `P = v − ι − α2^b < v − ι`; (v) `c10 + c32 − P = (k − b) + A2 − A1 = (k − b) + α(2^c − 2^b) + r_c − r_b > 0` (case c: r_b − r_c = c − b; cases a, b: r_b ≤ c − b).
| r | matchings | bound used |
|---|---|---|
| 1 | loops 0; c30 = P; c10, c32 > P (i, ii); c20, c31 ≥ a chord (iii, iv) | ≥ chord at 1 |
| 2 | two loops: 0 (chord 0); loop + off: off ≥ P or (iii)/(iv) [if v < 0 and ι ≥ 0: v ≥ 2v − ι; if v − ι < 0 and ι ≤ 0: v − ι ≥ 2v − ι]; two offs: (2,0)+(3,1) = 2v − ι = U(2); (1,0)+(3,1) = (2,0)+(3,2) = P + γ; (1,0)+(3,2) > P by (v) | ≥ U(2), P or 0 |
| 3 | three loops 0; two loops + off: off ≥ chord at 1 = chord at 3; loop + two offs: only (1,0)+(3,1)+loop 2 and (2,0)+(3,2)+loop 1, both P + γ; three offs: impossible (rows 1 and 2 both need column 0) | ≥ chord at 3 |
| 4 | the diagonal only | = U(4) = 0 |

**Pattern (0,0,1)** (E3 = e): case (b), u = −α2^b, v = γ − α2^c, ι = γ + r_k, `P = −α(2^b + 2^c) − r_k`. Entries: c10 = γ − α2^b, c20 = γ − α2^c, c30 = P, c31 = −α2^c − r_k, c32 = −α2^b − r_k, c33 = e. Every entry ≥ P: differences γ + α2^c + r_k, γ + α2^b + r_k, 0, α2^b, α2^c, and `e − P ≥ α(2^b + 2^c) > 0` (e ≥ −r_k).
r = 1: T(1) = P = U(1). r = 2: two loops ≥ min(0, e) ≥ P; loop + off ≥ P (loop 3 forces off ∈ {c10, c20}: `c10 + e − P ≥ γ + α2^c`, `c20 + e − P ≥ γ + α2^b`); offs: (2,0)+(3,1) = U(2), (1,0)+(3,2) − P = γ + α(2^c − 2^b) > 0, the other two = P + γ. All ≥ chord P or U(2). r = 3: all ≥ P = U(3) by the same entries (three loops ≥ min(0,e) ≥ P; loop 3 + off forces off ∈ {c10, c20}; loop + two offs = P + γ). r = 4: e = U(4).

**Pattern (0,1,1)** (E2 = E3 = e): case (a), ι = 0, `v = −α2^c − r_k < 0`, u ≥ −α2^b + 1, so `s = u − v ≥ α(2^c − 2^b) + 1 + r_k > r_k ≥ −e`. Entries: c10 = u + γ, c20 = v, c30 = P = u + v, c31 = v, c32 = u + γ + e, c22 = c33 = e. U = (0, P, 2v, P + e, 2e).
r = 1 (chords P, v, e/2): 0 ≥ v; e ≥ v (e ≥ −r_k > v) or e ≥ e/2; c10 − P = γ − v > 0; c20 = c31 = v; c32 − P = γ + e − v > 0.
r = 2 (chords 2v, P + e/2): two loops 0, e, 2e ≥ 2v; (1,0) + loop e and (3,2) + loop 0 = u + γ + e ≥ P + e/2 (difference γ − v + e/2 > 0); (2,0), (3,1) + loop: v or v + e ≥ 2v; (3,0) + loop: P ≥ 2v (u ≥ v) and `P + e − 2v = s + e > 0`; offs: 2v = U(2); `2u + 2γ + e − (P + e/2) = s + 2γ + e/2 > 0`; P + γ − 2v = s + γ > 0; P + γ + e − 2v = s + γ + e > 0.
r = 3 (chords P + e = U(3), v + e): three loops e or 2e ≥ v + e; (1,0) + loops {2,3}: `u + γ + 2e − (v + e) = s + γ + e > 0`; (2,0) + {1,3} and (3,1) + {0,2}: v + e; (3,0) + {1,2}: P + e; (3,2) + {0,1}: `u + γ + e − (v + e) = s + γ > 0`; loop + two offs: P + γ + e. r = 4: 2e = U(4).

**Pattern (1,1,1)** (E1 = E2 = E3 = e): case (c), `u = −γ − α2^b − r_k`, `v = −α2^c − r_k`, `ι = −γ − r_k`, `P = −α(2^b + 2^c) − r_k`, `s = α(2^c − 2^b) − γ`. Entries: c10 = −α2^b − r_k, c20 = −α2^c − r_k, c30 = P, c31 = γ − α2^c + e, c32 = γ − α2^b + e, loops 0, e, e, e. U = (0, P, P − s + e, P + 2e, 3e).
r = 1: every entry ≥ P (differences α2^c, α2^b, 0, γ + α2^b + r_k + e > 0, γ + α2^c + r_k + e > 0, −P, e − P). T(1) = U(1).
r = 2: **every 2-matching is ≥ min(U(2), P + e)**, the second being the chord (U(1) + U(3))/2: two loops e or 2e (> P + e); (1,0)/(2,0) + loop e: P + e + α2^c, P + e + α2^b; (3,0) + loop: P + e; (3,1)/(3,2) + loop ≥ P + e + γ + α2^b; offs: (2,0)+(3,1) = U(2); (1,0)+(3,2) = P + e + γ + α(2^c − 2^b); the other two P + γ + e.
r = 3: every 3-matching ≥ P + 2e = U(3) (same differences). r = 4: 3e = U(4).
**GAP found (Leg 0):** flight 3 wrote for (1,1,1) «the natural matchings are the tropical minima (T = U)». **That is false when γ > α(2^c − 2^b)** (s < 0): then (3,0) + a loop costs P + e < U(2) = P + e − s, so T(2) = P + e < U(2) (smallest example on paper: b = 0, c = 1, k = 4, α = 1: U(2) = e − 1, T(2) = e − 3). The clocks pool there (x1 < x2). **The conclusion of A2 survives**: T(2) ≥ min(U(2), (U(1) + U(3))/2) ≥ Y(2), the chord criterion. Repaired above.

**i = 0** (row ∅ absent; `A(D) = α o_D − min D`, min ∅ = k; no jump): c10 = −α2^b, c20 = −α2^c, c30 = −α(2^b + 2^c) = U(1), c31 = γ − α2^c, c32 = γ − α2^b, loops 0; clocks (ω − γ, γ − ω, U(1)), ω = α(2^c − 2^b), so U(3) = U(1) and U(2) = γ − 2α2^c. r = 1: min entry = U(1). r = 2: loops/loop+off ≥ U(1) = (U(1) + U(3))/2; offs: (c,∅)+(bc,b) = U(2), (b,∅)+(bc,c) = U(1) + γ + α(2^c − 2^b), the others U(1) + γ. r = 3: the five 3-matchings cost 0, U(1), −α2^b, −α2^c, U(1) + γ (twice) ≥ U(3).

**Verdict on A2: CORRECT** (every inequality now written), **with one GAP** (the (1,1,1) sentence «T = U», false when γ > α(2^c − 2^b); the floor holds there by the chord (U(1)+U(3))/2). Gate: P0a–P0c below.

### 0.2 Lemmas St1 and St2 re-read cold

**St1 — CORRECT.** Cost of an r-matching `= α a_m + b_m + P c_m`, with `a_m = Σ o(cols) − Σ o(rows)`, b_m = Σθ + carries (independent of α and P), `c_m` = −#J-rows (case R) or +#J-columns (case f). (1) a_m is minimised exactly by the row set L_r and column set F_r (o-values distinct). (2) J is an upper set in o-order, so L_r has the most J-rows and F_r the fewest J-columns: c is minimised by the same sets. (3) On (L_r, F_r) the carries part is fixed by the sets, and Σθ = Σ H(Δ) + Σγ with Σ H(Δ) fixed; γ = 0 only on the natural matching (Theorem O). If the natural matching n is optimal at (α0, P = 0), then for α ≥ α0, P ≥ 0: `cost_n = [α0 a_n + b_n] + (α − α0) a_n + P c_n ≤ cost_m`. The clock difference `x̂_{D_j} − x̂_{D_{j+1}}` has α-coefficient `2(o_{D_{j+1}} − o_{D_j}) > 0` and P-coefficient `J(D_{j+1}) − J(D_j) ≥ 0` (case R) or `J(I∖D_j) − J(I∖D_{j+1}) ≥ 0` (case f). So sorted clocks stay sorted, Y = U, T = U.
**St2 — CORRECT.** (T-side) Let `c_min` be the natural slope. A matching with slope `c_m ≥ c_min + 1` has, at P ≥ 0, value `≥ T(r)(0) + P c_m ≥ T(r)(0) + P c_min + P`, which is ≥ the natural value `U(r)(0) + P c_min` once `P ≥ P_T := max_r (U(r)(0) − T(r)(0))`. So beyond P_T, T(r)(P) = B* + P c_min (min over the extreme-slope matchings). (Y-side) The P-dependent clocks are a block of consecutive positions in o-order (case R: the last #J, lowered by P; case f: the first #J, raised by P). If min(first block) ≥ max(second block), PAVA of the whole = PAVA of each block side by side (no block mean of one side can exceed one of the other), and PAVA commutes with adding a constant to a block (integer splitting included). This happens for `P ≥ P_Y` (the explicit spread). Beyond it the r smallest pooled values come from the lower block first, so Y(r)(P) is affine with slope −min(r, #J) (R) or max(0, r − #nonJ) (f) = c_min. Hence T − Y is constant for P ≥ max(P_T, P_Y), and famcheck's range `1 ≤ P ≤ max(P_T, P_Y, 1) + 2` covers it. (The famcheck slope test is a redundant sanity check.)

### 0.3 Gate of the written table (engines/leg0_a2.py, logs/leg0_a2.log; estimate 60 MB / 60 s; VIGIA-FIN-OK, 23 MB, 6 s) — MEASURED
56 families (|I| = 2, λ ≤ 255), α = 1..4, every m_low, cases none / R / f with jump 1..4, and i = 0: 51 732 cells + 224 cells at i = 0.
- **P0a held:** my closed-form entries and clocks = flight 3's reduced costs, 51 956/51 956.
- **P0b held:** T(r) ≥ min(my named chords), and each named chord is a genuine chord ≥ Y(r): 207 600/207 600 (r = 1..4).
- **P0c held:** in the 7 008 cells of pattern (1,1,1), T(2) = min(U(2), P + e) in 7 008/7 008, and T(2) < U(2) exactly when γ > α(2^c − 2^b) (7 008/7 008). **Control fires:** flight 3's sentence «T = U in (1,1,1)» fails in 192 cells; first: λ = 10 (I = {0,1}, k = 3), α = 1, m_low = 7, jump R = 1: T = (0, −4, −5, −6, −3), U = (0, −4, −4, −6, −3) = Y except Y(2) = −5.
- **P0d (control) fires:** the chord set {U(2)} alone fails in 1 028 of 11 316 cells of pattern (0,0,0).
- Floor T ≥ Y: 0 failures (as flight 3).

**STATUS Leg 0: CLOSED (Sat Oct  3 17:11:38 CEST 2026).** A2: CORRECT with one GAP (the (1,1,1) sentence), repaired by the chord (U(1)+U(3))/2 and gated. St1: CORRECT. St2: CORRECT.

## 2. Leg A — the rent

BUDGET (written Sat Oct  3 17:13:38 CEST 2026, before starting): 35 % of the flight. Pencil first: the rent form as an assignment LP; look for closed-form receipts (potentials).

### A.1 The rent as an assignment LP; receipts paired by the mirror (PROVED, pencil; written 17:14)
Notation of flight 3 F4: arrow `a → b` (b ⊊ a) costs `ĉ(a,b) = R(a) + C(b) + γ(a∖b)`; loop `a → a` costs `R(a) + C(a) = E_a` (the normalised jump; **E ≡ 0 when there is no jump**). Clocks `x_D = R(D) + C(I∖D)`.
**Lemma R0 (no jump, i ≥ 1).** If E ≡ 0: loops are free, `x_{I∖D} = −x_D`, so `U(r) = U(N − r)`, and the pooled clocks y (PAVA with integer splitting, «ceil values first») are antisymmetric too: a block with sum S = qn + ρ and values (q+1)^ρ q^{n−ρ} in o-order is mirrored by a block with values (−q)^{n−ρ} (−q−1)^ρ, and the mirror reverses the o-order.
**Lemma R1 (Legendre, integer slopes).** For integer s, `min_r (Y(r) − sr) = min_r (U(r) − sr)`: inside a pooled block the slopes of Y are q and q + 1 and no integer lies strictly between q and S/n < q + 1, so the minimum is reached at a block end, where Y = U. (The auditor's 4.1, re-derived.)
**Lemma R2 (the receipt criterion; no jump, i ≥ 1).** Let y be the pooled clocks. **If every arrow satisfies `2ĉ(a,b) ≥ y_a − y_b`, the rent form (hence the floor) holds for every integer s.**
*Proof.* Receipts `p_D = min(0, (y_D − s)/2)` on rows and `q_{D'} = min(0, (−y_{D'} − s)/2)` on columns (both ≤ 0). Loops: `p_a + q_a ≤ (y_a − s)/2 + (−y_a − s)/2 = −s = ĉ(a,a) − s`. Arrows: `p_a + q_b ≤ (y_a − y_b)/2 − s ≤ ĉ(a,b) − s`. Value: pairing column D' with row I∖D' (y antisymmetric), `Σp + Σq = Σ_D min(0, y_D − s) = Σ_{y_D < s}(y_D − s) = min_r Σ_{L_r}(y − s)` (y non-increasing in o-order, so the negative terms form a suffix) `= min_r (Y(r) − sr) = min_r (U(r) − sr)` by R1. Weak duality: any matching m pays `Σ_m(ĉ − s) ≥ Σ_m (p_a + q_b) ≥ Σp + Σq` (unmatched vertices have p, q ≤ 0). ∎
*Remarks.* (1) Without pooling (y = x) the criterion reads `2ĉ(a,b) ≥ x_a − x_b`, i.e. (with C = −R when there is no jump) `[R(a) + R(I∖a)] − [R(b) + R(I∖b)] ≥ −2γ(a∖b)`; in the additive case (no carries) R(D) + R(I∖D) = τ(I) is constant and the criterion is `γ ≥ 0`: **without pooling and without carries the floor is one line.** [Corrected 18:33 — error E3: at 17:14 I wrote a garbled formula here and the overstatement «without pooling the floor is one line»; with carries R(D) + R(I∖D) varies and P-H1 shows the criterion failing in 780 unpooled cells. Unpooled cells are closed instead by Lemma M + Lemma P, A.4 and A.6.] (2) With the REAL (unrounded) pooled clocks the criterion cannot hold in every cell: it would give T ≥ Ỹ (real minorant) > Y in cells with fractional blocks, contradicting T ≤ d_r ≤ Y (Theorem O). That is the control below. (3) The criterion is local (one arrow at a time): it is Rafa's rent read as «every couple pays at least half the drop of the pooled clock between its two ends».

**P-H1 FAILED (17:20; sealed before the run):** the half-drop law fails in 846 of 2 700 no-jump cells (λ ≤ 62, α ≤ 6), 780 of them unpooled; first λ = 10, I = {0,1}, α = 2, m_low = 1, arrow {0,1} → {0}: 2ĉ = −6 < y_a − y_b = −5. The receipts of R2 are correct wherever the law holds (P-H1r 1854/1854). Reading: with carries `R(D) + R(I∖D) = H(I) − A(D) − A(I∖D)` is not constant, and the mirror receipts are not tight on the natural arrows.

### A.2 Windows: when every carry run is short the model is additive (PROVED, pencil)
For t ∈ I the **window** of t is the bit range `[t, next(t))` (length h_t); the windows of I and the bits below min I partition [0, k).
**Lemma W1 (all-short cells).** If `r_t(m) < h_t` for every t ∈ I, then for every E ⊆ I: `κ(m, o_E) = Σ_{t∈E} r_t(m)`; hence **R(D) = Σ_{t∈D} τ_t with τ_t = h_t − α2^t − r_t(m) ∈ [1 − α2^t, h_t − α2^t]**, and `m_low + o_I < K` (no jump).
*Proof.* Adding 2^t to m changes only the window of t: the run of ones from t (length r_t < h_t) becomes zeros and bit t + r_t < next(t) becomes 1. Windows are disjoint, so the additions for different t ∈ E do not interact and their carries add up; the top window [c, k) absorbs the top carry, so m_low + o_I < K. ∎
**Consequence (the additive model).** In an all-short cell: arrow `a → b` costs `φ(a∖b) = τ(Δ) + γ(Δ)`, loops cost 0, clocks `x_D = τ(D) − τ(I∖D) = 2τ(D) − τ(I)`, and `R(D) + R(I∖D) = τ(I)` is constant: the mirror receipts are tight on every natural arrow. The mission's range `τ_t ∈ [1 − α2^t, h_t − α2^t]` is exactly this model. **Every jump and every non-additive carry lives in the long-run cells** (some run reaching the next digit, or the top run reaching k).

**P-H2 held (17:29):** in all 29 892 all-short no-jump cells (λ ≤ 255, α ≤ 6; 3 570 pooled) R is additive and the half-drop law holds, also with half the gold; all 25 838 failures are long-run cells. logs/legA_half2_255.log.

### A.3 Theorem RW (the pooled clocks are a reflected walk) and Theorem H (the floor in every all-short cell) — PROVED, pencil (pencil 17:20–17:29, written 17:30)
Additive model: digits `t_1 < … < t_n` of I, `τ_j := τ_{t_j} ∈ [1 − α2^{t_j}, h_j − α2^{t_j}]`, clocks `x_D = τ(D) − τ(I∖D)` in o-order (binary order of the index sets).
**Theorem RW.** The pooled clocks (PAVA, non-increasing, integer splitting) are `ŷ_D = z_n(D)`, where `z_0 = 0` and, digit by digit from the bottom,
  **`z_j = max(z_{j−1} − τ_j, 0)` if j ∉ D,  `z_j = min(z_{j−1} + τ_j, 0)` if j ∈ D.**
They are integers: no fractional block ever occurs in an additive cell.
*Proof.* Let `F_j(D) = 2τ(D ∩ [j])` on the 2^j subsets of [j] in binary order; `F_j = [F_{j−1}, F_{j−1} + 2τ_j]` and `F_j(D) + F_j([j]∖D) = 2S_j` (S_j = τ_1 + … + τ_j), the complement reversing the order. (1) PAVA can be run on the blocks of PAVA(first half) and PAVA(second half). (2) The fit of an antisymmetric sequence is antisymmetric (uniqueness). (3) Hence the only possible merge is one block C, symmetric about the centre, of value S_j; inside a block of a non-increasing fit every prefix has mean ≤ the block value, so the left blocks absorbed into C are exactly those of value ≤ S_j. So `Y_j = [max(Y_{j−1}, S_j), min(Y_{j−1} + 2τ_j, S_j)]` (also when nothing merges: then min Y_{j−1} ≥ S_j). Put `z_j = Y_j − S_j`; the clocks are `F_n − S_n`. Integers are preserved, so the integer splitting never acts. ∎
(It is a **Skorokhod reflection**: after a digit outside D the walk is ≥ 0, after a digit inside D it is ≤ 0. Without reflection it is `Σ_{j∈D} τ_j − Σ_{j∉D} τ_j = x_D`.)
**Lemma Λ (the growth of the ruler).** `|z_j(D)| ≤ Λ_j := max_l Σ_{l < i ≤ j}(−τ_i) ≤ α(2^{t_{j+1}} − 1)` for every D. *Proof.* `Λ_j = max(Λ_{j−1} − τ_j, 0)` bounds both max_D z_j and −min_D z_j; and `−τ_i ≤ α2^{t_i} − 1`, `Σ_{i ≤ j} 2^{t_i} ≤ 2^{t_{j+1}} − 1`. ∎ **This is the only place where the sizes α·2^t enter** (and only through the lower bound τ ≥ 1 − α2^t).
**Theorem H (the half-drop law with gold to spare).** For every arrow `a → b`, Δ = a∖b, d = min Δ, ν(Δ) = #{j ∈ I∖Δ : j > d}:
  **`ŷ_a − ŷ_b ≤ 2τ(Δ) + Σ_{j∈I∖Δ, j>d} (h_j − α)⁺`, hence `2ĉ(a,b) − (ŷ_a − ŷ_b) ≥ Σ_{j skipped}(h_j + min(h_j, α)) ≥ γ(Δ) + ν(Δ)`.**
*Proof.* Run the walk for a (A_j) and for b (B_j); they agree below d. Put `W_j = A_j − B_j − 2τ(Δ ∩ [j])`. At j = d: `A_d − B_d = min(ζ + τ_d, 0) − max(ζ − τ_d, 0) ≤ 2τ_d`, so W_d ≤ 0. For j ∈ Δ, j > d: `A_j ≤ A_{j−1} + τ_j`, `B_j ≥ B_{j−1} − τ_j`, so W does not grow. For j ∈ b: `ΔW = max(B_{j−1} + τ_j, 0) − max(A_{j−1} + τ_j, 0) ≤ max(Λ_{j−1} + τ_j, 0) ≤ (h_j − α)⁺`; for j ∉ a: `ΔW = max(τ_j − A_{j−1}, 0) − max(τ_j − B_{j−1}, 0) ≤ (h_j − α)⁺` (Lemma Λ and τ_j ≤ h_j − α2^{t_j}). Sum. ∎
**Corollary H (the floor, every family, every α, every all-short shift).** In every cell (any family I, any α ≥ 1, any i ≥ 1) in which every carry run of m = i − 1 is short, the floor holds: with Lemma R2 the receipts `p_D = min(0, (ŷ_D − s)/2)`, `q_D = min(0, (−ŷ_D − s)/2)` pay every rent s. **And it holds with half of the gold removed** (each arrow keeps slack γ + ν − 2⌈γ/2⌉ ≥ ν − 1 ≥ 0 when it dances), **and with one coin removed per dancing couple** (slack γ + ν − 2 ≥ 0). This is Leg B's (G½) and (G1) in the additive cells. In particular **i = 1 (m = 0) is closed for every family**, and so is every shift whose m has no window of I full of ones.

**Gate P-RW (17:30; engines/legA_rw.py, logs/legA_rw_255.log, estimate 60 MB / 2 min, VIGIA-FIN-OK 20 MB 5 s) — MEASURED:** every all-short no-jump cell with λ ≤ 255, |I| ≥ 1, α ≤ 6: reflected walk = PAVA 37 638/37 638 (5 014 pooled); Theorem H bound, slack ≥ γ + ν and ĉ = τ(Δ) + γ(Δ): 37 638/37 638. Controls fire: the unreflected walk differs in 5 014/5 014 pooled cells; the bound without the (h − α)⁺ terms fails in 400 cells.

### A.4 The general cell: rows read the ruler at m, columns at m + K (PROVED, pencil, 17:30–17:39)
With σ(z) = s_2(m + z) and `R_μ(D) := G(D) − α o_D + s_2(μ + o_D) − s_2(μ)` (G = Σ gaps, g_t = h_t − 1), flight 3's A.1 becomes, after removing global constants,
  **`ĉ(a,b) = R_m(a) − R_{m+K}(b) + γ(a∖b)`**, loops `ĉ(a,a) = R_m(a) − R_{m+K}(a)` (the jump), clocks `x_D = R_m(D) − R_{m+K}(I∖D)`.
(Check: `s_2(K − o_Δ) = θ(Δ) − |Δ| + 1`, so `ĉ(a,b) = κ(m + o_a, K − o_Δ) − α o_Δ` + const: the entry is the 2-adic valuation of `2^{α(K + o_b − o_a)} C(m + K + o_b, K + o_b − o_a)`. Case R: `r_k(m) = R`, `r_k(m+K) = 0`; case f: `r_k(m) = 0`, `r_k(m+K) = f`; this reproduces famcheck's two jump conventions exactly.) **The jump is not a separate phenomenon: it is the carry of m + o_D into bit k, read once at m and once at m + K.** No jump ⟺ R_m = R_{m+K}.
**Windows (carry automaton).** In the window W_t = [t, next(t)) m is F (all ones), A (ones except bit t) or O. An O window never passes a carry; A passes only if t ∈ D and a carry comes in; F passes if t ∈ D or a carry comes in. All-short ⟺ no F window (A.2). A jump ⟺ the top window passes.
**Lemma M (monotone ruler: no gold needed; PROVED).** If R_m and R_{m+K} are both non-increasing in o-order, the floor holds in the cell, even with all the gold removed. *Proof.* Receipts `p_a = min(0, R_m(a) + c − s/2)`, `q_b = min(0, −R_{m+K}(b) − c − s/2)` are feasible for every constant c (γ ≥ 0, loops included). They are the dual of the relaxation in which ANY row may be matched to ANY column at cost R_m(a) − R_{m+K}(b); its optimum at rent s is `min_j [Σ_{j smallest} R_m − Σ_{j largest} R_{m+K} − js]` (rows and columns chosen independently, loops allowed), which for monotone R's is `min_j [Σ_{L_j} R_m − Σ_{F_j} R_{m+K} − js] = min_j (U(j) − js)`; any optimal dual of that relaxation (LP duality, the bipartite matching polytope being integral) is feasible for the true problem, whose costs are larger on a smaller support. ∎ (Simplest route, found later: Lemma M is Theorem U, A.5, with φ = φ' = 0.) (In the additive model, R monotone ⟺ every π_t = τ_t − τ(I_{<t}) ≤ 0 ⟺ no pooling.)
**Obstruction (PROVED on one cell).** In long-run cells receipts with s-independent row levels ρ and column levels κ (`p = ½min(0, ρ − s)`, `q = ½min(0, κ − s)`, `ρ_a + κ_b ≤ 2ĉ(a,b)`) need not exist. In λ = 10, I = {0,1}, α = 2, m_low = 1 (R = (0, −2, −2, −5), clocks (5, 0, 0, −5), unpooled): the constraints force ρ_∅ = κ_I = 5, ρ_I = κ_∅ = −5, ρ_D + κ_D = 0 and κ_{0} ≤ −1, so the middle levels are spread by ≥ ±1 where the clocks are 0, 0, and ½(Φ_ρ + Φ_κ)(0) ≤ −6 < V(0) = −5. **So outside the additive model the receipts must depend on the rent** (Lemma M's do: one constant c per rent).

**Census P-M (18:01; engines/legA_census.py, logs/legA_census_A.log + logs/legA_census_B.log; the first run was killed by the watchdog, error E1, kept as logs/legA_census_KILLED_E1.log) — MEASURED:** over 436 752 cells (λ ≤ 255, |I| ≥ 2, α ≤ 6, every m_low, no jump / R / f with jump 1..3) the general form A.4 reproduces flight 3's costs and clocks in every cell; Lemma M's receipts reach V(s) in 20 760/20 760 monotone cells tested (λ ≤ 62). Coverage: 29 892 cells all-short (Corollary H), 366 452 with monotone rulers (Lemma M), **hard core 40 408 cells (9.3 %), every one of them pooled**, 36 444 of them with a jump. **So every unpooled cell is already PROVED** (all-short or Lemma M — this is a measurement on λ ≤ 255, not yet a theorem: «unpooled ⟹ monotone rulers» is not proved). [Superseded at 18:10: Lemma P (A.6) proves «unpooled ⟹ monotone rulers» for every cell.]

### A.5 Theorem U (corrected rulers) — PROVED, pencil (written 18:00): the floor reduces to three inequalities on two functions
Let ε = ŷ − x (the pooling residual). **Theorem U.** Suppose there are functions φ (rows) and φ' (columns) on the dancers with
 (i′) **gold-compatible:** `φ(a) − φ'(b) ≤ γ(a∖b)` for every b ⊆ a (loops included: φ(a) ≤ φ'(a));
 (ii′) **monotone:** `w_r := R_m + φ` and `w_c := R_{m+K} + φ'` are non-increasing in o-order;
 (iii′) **dominating:** `φ(D) − φ'(I∖D) ≥ ε_D` for every D.
Then T(r) ≥ Y(r) for every r in the cell.
*Proof (one line).* For an r-matching with row set A and column set B, by (i′) `cost = Σ_pairs (R_m(a) − R_{m+K}(b) + γ(a∖b)) ≥ Σ_A w_r − Σ_B w_c ≥ (r smallest w_r) − (r largest w_c)`, by (ii′) this is `Σ_{L_r} w_r − Σ_{F_r} w_c = Σ_{D∈L_r} (w_r(D) − w_c(I∖D)) = Σ_{L_r} (x_D + φ(D) − φ'(I∖D))`, and by (iii′) ≥ `Σ_{L_r} ŷ_D = Y(r)`. ∎
No rent and no matching theory is needed once φ, φ' exist; the rent receipts of A.1 and Lemma M are the LP shadows of this. **Special cases:** Lemma M is φ = φ' = 0 (unpooled, monotone R's); Corollary H is φ = φ' = ε/2 in the additive model ((i′) by Theorem H: ε_a − ε_b ≤ γ − ν; (ii′) because R + ε/2 = (ŷ + τ(I))/2; (iii′) with equality since ε is antisymmetric).
**Canonical choice for every cell:** `φ = ε/2`, `φ'(E) = −ε_{I∖E}/2`, so (iii′) holds with equality and the remaining conditions are
 (i′) `ε_a + ε_{I∖b} ≤ 2γ(a∖b)` for b ⊆ a (loops: `ε_a + ε_{I∖a} ≤ 0`), (ii′) `R_m + ε/2` and `R_{m+K} − (ε∘mirror)/2` non-increasing in o-order.

**P-U (18:03, logs/legA_U_A.log, λ ≤ 191) — MEASURED:** with the canonical split φ = ε/2: (i′) holds in every cell (224 670); (ii′) fails in 666 pooled cells (first λ = 34, I = {0,1}, k = 5, α = 1, m_low = 1). On paper that cell has another split (β = (½,0,0,½)), so the split must be free.
**P-U2 (18:08, logs/legA_U2_A.log + logs/legA_U2_B.log) — MEASURED:** with a FREE split the system (i′)(ii′)(iii′) — integer difference constraints, tested by Bellman–Ford — **is feasible in every one of the 454 872 cells** (λ ≤ 255, |I| ≥ 1, α ≤ 6, every m_low, no jump and jumps 1..3, and i = 0). Removing the gold (γ := 0) makes it infeasible in 19 179 pooled cells: the gold is needed, half of it is not (Leg B).

**Theorem U′ (the same theorem in two potentials; PROVED).** Write `v := w_r` (row potential) and `w := w_c` (column potential). Theorem U says: **if v, w are non-increasing in o-order, `v(D) − w(I∖D) = ŷ_D` for every row D, and `v(a) − w(b) ≤ ĉ(a,b)` for every b ⊆ a, then T = Y.** Since w is fixed by v (`w(E) = v(I∖E) − ŷ_{I∖E}`), the conditions on v alone are:
 (M1) v non-increasing; (M2) v − ŷ non-decreasing (so **v is constant on every pooled block** and drops by at most the drop of ŷ between blocks); (G) `v(a) − v(I∖b) + ŷ_{I∖b} ≤ ĉ(a,b)` for b ⊆ a.
Known solutions: v = R_m (unpooled, Lemma M); v = (ŷ + τ(I))/2 (additive model, Theorem H). The measured statement P-U2 is: **such a v exists in every cell with λ ≤ 255.**
**Negative cycles = generalized matchings (PROVED, Farkas).** The system is infeasible iff there are p arrows `a_{i+1} → b_i` (a p-matching) and p pivots u_i with `u_{i+1} ⪰ a_{i+1}` and `u_i ⪰ I∖b_i` in o-order (disjoint chains) such that `Σ_i ĉ(a_{i+1}, b_i) < Σ_i ŷ_{u_i}`. So P-U2 is a strengthening of the floor (the floor is the case of pivots allowed anywhere: Σ ŷ_u ≥ Y(p)), and it is what an induction on digits should carry (Gold 2: strengthen to close the induction).

### A.6 Lemma P (no pooling ⟹ monotone rulers) — PROVED, pencil (18:08–18:10). Hence the floor in EVERY unpooled cell (i ≥ 1)
Consecutive dancers in o-order are `D = E ∪ L → D⁺ = E ∪ {t}` (t ∈ I, L = I ∩ [0,t) all present in D, E ⊆ I_{>t}); their mirrors are `I∖D⁺ = E' ∪ L → I∖D = E' ∪ {t}` with E' = I_{>t}∖E. So the clock drop splits into a **row piece and a column piece of the same shape**:
  `x_D − x_{D⁺} = P_t(m + o_E) + P_t(m + K + o_{E'})`, `P_t(ν) := G(L) − g_t + α(2^t − o_L) + s_2(ν + o_L) − s_2(ν + 2^t)` (= the drop of R_ν at that step).
Let `c = [m_{<t} + o_L ≥ 2^t]` (the lower chain carries into bit t; the same for both pieces since E, E' only touch bits > t).
- c = 1: `P_t(ν) = const + s_2(m_{<t} + o_L − 2^t) − s_2(m_{<t})` does not depend on ν: **the two pieces are equal.**
- c = 0 and W_t not full: `P_t(ν) = H(L) − h_t + α(2^t − o_L) − κ(m_{<t}, o_L) + r_t(ν)` with `r_t(ν) = r_t(m)` for both ν: **equal.**
- c = 0 and W_t full: `r_t(ν) ≥ h_t` and `κ(m_{<t}, o_L) ≤ t − t_1 = H(L)` (one carry at most per bit of [t_1, t)), so **both pieces are ≥ α(2^t − o_L) ≥ α > 0.**
Hence a non-negative clock drop forces both pieces non-negative: **unpooled ⟺ R_m and R_{m+K} non-increasing**, and with Lemma M: **the floor holds in every unpooled cell, for every family, every α ≥ 1, every i ≥ 1, with or without jump.** (Measured consistency: in λ ≤ 191 the raw rulers fail to be monotone in exactly the 21 689 pooled cells, logs/legA_U_A.log.) Corollary: **a clock drop can be negative only at a step where the row and column pieces are equal** — pooling is always «symmetric», as in the additive model.
**Gate P-P (18:39–18:42; engines/legA_P.py, logs/legA_P.log, VIGIA-FIN-OK 147 s) — MEASURED:** the trichotomy (equal pieces when c = 1 or W_t not full; both pieces ≥ α(2^t − o_L) when c = 0 and W_t full) holds at every step of every cell with i ≥ 1, λ ≤ 255, α ≤ 6, jumps 0..3: 453 390/453 390; control («pieces always equal») fails in 415 752 cells.

### A.7 The block-average candidate (sealed as P-BA before measuring)
Let the PAVA blocks of x be B_1, B_2, … (o-order). Put `v := average of R_m over the block`, `w(E) := average of R_{m+K}(I∖·) over the block of I∖E`. Then `v(D) − w(I∖D) = average of x over the block = ŷ_D` (real values). In the additive model this is exactly `(ŷ + τ(I))/2` (Theorem H's choice); in an unpooled cell it is v = R_m (Lemma M's choice). Theorem U′ then needs only (M1) the block averages of R_m and of R_{m+K}∘mirror to be non-increasing / non-decreasing across blocks and (G) `v(a) − w(b) ≤ ĉ(a,b)`.

**P-BA (18:10–18:13) — FAILED, both versions:** the plain block average of R_m is not a valid v (logs/legA_BA_A.log, logs/legA_BA2_A.log; (M1) fails in 128 and (G) in 26 of 9 656 pooled cells λ ≤ 127 with maximal level sets). By hand (logs/legA_show_34_5.log, logs/legA_show_22_1.log) a valid v is «R_m on singleton blocks and a constant on each pooled block», the constant being forced into an interval by the neighbours (λ = 34, m_low = 5: v = (0,0,0,−1); λ = 22, α = 1, m_low = 1: v = (0,−1,−1,c,c,−3,−3,−6), any c ∈ [−3, −2]); I did not find the general rule for that constant.
**Lemma P at i = 0 (PROVED, pencil, written 18:14).** At i = 0, R(D) = τ(D) + min D (τ_t = h_t − α2^t, min ∅ = k, row ∅ absent). For a step with L ≠ ∅ the row and column pieces are both `τ(L) − τ_t + t_1 − t` (equal); for L = ∅ (t = t_1) they are `−τ_{t_1} + (min E − t_1)` and `−τ_{t_1} + (min E' − t_1)`, both ≥ `−τ_{t_1} + h_{t_1} = α2^{t_1} > 0`; the column step ∅ → {t_1} drops by `k − t_1 − h_{t_1} + α2^{t_1} > 0`. So **unpooled ⟹ monotone rulers at i = 0 as well**, and Lemma M closes every unpooled i = 0 cell.
**Where the hard core first shows (MEASURED, logs/legA_hard22.log):** with |I| ≥ 3 the smallest family having pooled cells that are not all-short is **λ = 22** (I = {0,1,2}, k = 4): exactly 28 cells, all at α = 1 with m odd (the window of digit 0, of length h_0 = 1, is full), 4 without jump and 24 with a jump.

**P-GW (18:28–18:33) — MEASURED, not proved:** in every no-jump cell λ ≤ 255 (64 770 cells, including the 3 964 hard ones) the pooled clocks are the **generalized reflected walk** with the LOCAL increments: `z ← min(z + [R_m(D_{≤t}) − R_m(D_{<t})], 0)` for t ∈ D, `z ← max(z − [R_m(E_{≤t}) − R_m(E_{<t})], 0)` for t ∉ D (E = I∖D). Pencil status: the top-level clip at 0 holds in every no-jump cell (A.3's argument needs only antisymmetry); the lower levels need «PAVA commutes with the piecewise shift τ_t(complement)», whose switch point is where the carry from below reaches the window of t — not proved. With a jump the reflection level moves and the formula fails (6 658 cells).

### A.8 The missing step in its sharpest form (no-jump case; pencil, 18:36–18:38) — the target for the next flight
In a no-jump cell write v = ŷ/2 + β in Theorem U′; then w = ŷ/2 + β∘mirror and the conditions become: **β is (ŷ/2)-Lipschitz along o-order** (|β_j − β_{j+1}| ≤ (ŷ_j − ŷ_{j+1})/2, so β is constant on pooled blocks) and, for every arrow, `|β_{I∖b} − β_a − (Ω(b) − Ω(a))/2| ≤ γ(a∖b) − (ε_a − ε_b)/2`, where **Ω(D) = R(D) + R(I∖D)** (the symmetric part of the ruler; constant in the additive model) and ε = ŷ − x. The loop conditions force η := β − Ω/2 to be **mirror-symmetric**, so the problem is:
  **find a symmetric η with |η_a − η_b| ≤ γ(a∖b) − (ε_a − ε_b)/2 for every b ⊊ a, such that Ω/2 + η is (ŷ/2)-Lipschitz along o-order.**
η = 0 satisfies the first condition in every measured cell (P-Ui: the residual law ε_a − ε_b ≤ 2γ); it fails the second only because Ω is not constant on pooled blocks (666 cells).
**Example of the mechanism (pencil).** One full window at digit 0 with h_0 = 1 followed by an O window at digit 1 gives `R(D) = τ(D) − ι·[0,1 ∈ D]`, with ι = 1 + r_2(m) if bit 1 of m is 0 and ι = −r_1(m) if it is 1 (the two carry cases of Theorem A2). Then `Ω/2 = const − (ι/2)·[D ∩ {0,1} ∈ {∅, {0,1}}]`, a period-4 pattern in o-order. In λ = 34, m_low = 1 the only pooled block is the whole cell, and η = (ι/2)·[D ∩ {0,1} ∈ {∅, {0,1}}] (this is the β = (½, 0, 0, ½) found by hand) cancels the carry interaction exactly and satisfies both conditions.
**The general rule — «η cancels the carry interactions inside each pooled block and nowhere else» — is what I could not state and prove in this flight.** [Addendum 19:12: Rafa's image 3 gave a rule that works in every measured cell — one deposit per shared flat, negotiated together with its mirror flat (§10, P-F4); still to be proved.] After it, the jump cells remain (there the reflection level is not 0: P-GW fails in 6 658 jump cells).

**STATUS Leg A (18:33): NO CONCLUYO for every cell; CLOSED for two infinite classes, for every family.** PROVED by pencil: the floor (rent form) in **every all-short cell** (Theorem RW + Lemma Λ + Theorem H + Lemma R2, with gold to spare) and in **every unpooled cell**, jumps and i = 0 included (Lemma M + Lemma P); a one-line sufficient certificate (Theorem U / U′) unifying both. MEASURED: a Theorem U certificate exists in **every** cell with λ ≤ 255 (454 872 cells). **Missing:** the floor in the pooled cells that have a full window (a long carry run) or a jump, and in the pooled cells at i = 0 — 9.3 % of the cells with λ ≤ 255, none with |I| ≤ 2 outside Theorem A2's reach; the smallest family where this gap is visible with |I| ≥ 3 is **λ = 22** (28 cells, α = 1, m odd), already closed per family by flight 3's machine check. Rafa's image 1, followed literally (a minimal cheaper matching must make a wrinkle), became Farkas' lemma: a cheaper matching is a negative cycle of the certificate system, i.e. p arrows with p pivots `u ⪰ row, u ⪰ mirror(next column)` and Σĉ < Σŷ_u; I did not find the structural reason why the hard core forbids it.

## 3. Leg B — the gold

BUDGET (written 18:27, with this section): 15 % of the flight. Most of the work was already done inside Leg A (Theorem H) and by three gates (P-G½, P-G½x, P-G1).

### B.0 KILL CRITERION FIRED — (G½) is FALSE (MEASURED, exact min-cost flow; checked by hand)
**First cell: λ = 66** (λ + 1 = 64 + 2 + 1, I = {0,1}, k = 6), α = 1, i = 6 (m_low = 5 = 101₂, no jump). R_m = (0, −1, 3, 0) on (∅, {0}, {1}, {0,1}); clocks (0, −4, 4, 0) pool to ŷ = 0, so Y ≡ 0. The arrow {0,1} → {1} drops digit 0 and skips the gap after digit 1 (h_1 = 5): γ = 5, cost ĉ = 2. Discounted by ⌈5/2⌉ = 3 it costs −1 < Y(1) = 0. In all, (G½) fails in **219 cells with λ ≤ 255** (27 with λ ≤ 127, first λ = 66; 192 with 128 ≤ λ ≤ 255, first λ = 130) — exactly the cells where the half-gold Theorem U certificate is infeasible (logs/legB_half.log, logs/legB_exact_half.log). The auditor's 0 failures for λ ≤ 62 were right; λ = 66 is the first family with |I| ≥ 2 beyond that range (63, 64, 65 have |I| ≤ 1).
**Reading.** All 219 cells are pooled cells with a full window (here the window of digit 0 is full, so adding o_b = 2 to m = 5 gives 7 = 111₂ and the arrow gets κ(7, 1) = 3 carries instead of the additive r_0(m) = 1). **The carries running through the skipped gap eat the gold.** In the additive model this cannot happen (Theorem H: slack ≥ γ + ν), and in unpooled cells no gold is needed at all (Lemma M).

### B.1 (G1) — one coin per dancing couple
- **PROVED, pencil, every family:** in every all-short cell (Theorem H: slack γ + ν − 2 ≥ 0 when dancing) and in every unpooled cell (Lemma M + Lemma P: all the gold can be removed).
- **PROVED cell by cell for every λ ≤ 255** (computer-assisted): the Theorem U system with γ − [γ > 0] is feasible in all 454 872 cells (λ ≤ 255, |I| ≥ 1, α ≤ 6, every m_low, jumps 0..3, i = 0) — logs/legB_exact_one.log. **Control:** with two coins per couple the system is infeasible in 20 010 of 27 684 cells (λ ≤ 62, logs/legB_exact_two_ctrl.log), as the auditor's 13 192 floor failures predict. «The uniform margin is exactly one» stands.
- Open: (G1) for the pooled cells with a full window or a jump, |I| ≥ 3, λ ≥ 256 (the same hard core as Leg A).

### B.2 Why half, where half is right; the gold is monotone (PROVED in the additive model)
- **Why half:** each couple's cost is split between its two ends by the receipts (p_a + q_b), so the pooled drop is paid twice by halves; Theorem H shows `2ĉ − (ŷ_a − ŷ_b) ≥ Σ_{skipped j}(h_j + min(h_j, α)) ≥ γ + ν`: each skipped gap pays its own length once in full plus min(h, α) — **the gold is worth at least half itself plus one coin per skipped digit**. The König doubling of F3 is the same halving seen from the matching side.
- **«The more they dance, the more they are worth» (PROVED, additive model; PROVED by certificates λ ≤ 255):** for any matching m, `cost(m) − Y(|m|) ≥ ½ Σ_{dancing e∈m}(γ_e + ν_e) ≥ #dancers(m)` in the additive model (sum the slacks of Theorem H through the receipts), `≥ Σ_e γ_e` in unpooled cells (Lemma M's relaxation ignores γ), and `≥ #dancers(m)` in every cell λ ≤ 255 (the (G1) certificate). The excess is additive over couples: removing a dancing couple removes exactly its own guaranteed share.
- **Water evaporates, breath oxidizes (PROVED, additive model):** the pooled clock is a Skorokhod reflection (Theorem RW) — after a digit outside D it can only be ≥ 0, after a digit inside D only ≤ 0, and its size never exceeds `α(2^{t_{j+1}} − 1)` (Lemma Λ). No step of the walk can undo the growth α·2^t: the walk does not «rejuvenate».
**STATUS Leg B: CLOSED as a verdict** — (G½) FALSE (λ = 66), (G1) PROVED in the additive and unpooled classes for every family and for every cell λ ≤ 255; (G½) is the right induction hypothesis only inside the additive model (where it is a theorem), not in general.

## 4. Leg C — assembly and trophies

BUDGET (written 18:34, with this section): 10 % of the flight. No new family or cube is evaluated here (Rafa's order).

### C.1 What is now proved for every family at once
For every family λ (λ + 1 = 2^k + Σ_{t∈I} 2^t), every α ≥ 1 and every shift i ≥ 0, the cell (λ, i, α) satisfies **Conjecture W (Smith(M) = pooled rule)** whenever it is
 (a) **all-short** (no window of I full of ones in m = i − 1; i ≥ 1) — Theorem O (d_r ≤ Y) + Corollary H (T ≥ Y), or
 (b) **unpooled** (the naive clocks already non-increasing; any i ≥ 0, jumps included) — Theorem O + Lemma M + Lemma P (then T = U = Y), or
 (c) |I| ≤ 2 — Theorem A2 (re-read in Leg 0, one GAP repaired) and flight 2's C.1 / Theorem S, or
 (d) λ ≤ 255 (and odd λ ≤ 511 through P-R1) — flight 3's per-family check.
Dependencies, all named: Theorem RT′ (flight 3, Leg 0: no tilting citation) and flight 2's A.1, A.2 (P-R1), B.1, C.0, C.4 ⟹ Theorem D; Theorem O (flight 3 B.4) for d_r ≤ U ≤ … ⟹ d_r ≤ Y; the tropical inequality d_r ≥ T(r); this flight's A.1–A.6 for T ≥ Y in classes (a), (b).

### C.2 Theorem C (conditional assembly) — PROVED
For every n: **Syl_2 K(Q_n) ⊕ Z_2 ≅ ⊕_λ [⊕_{a=1}^{k−1}(Z/2^a)^{2^{|I|+k−1−a}} ⊕ H(λ, (n−λ)/2)]^{m_λ(n)}** (flight 1's closed rule, D.5) **as soon as every family λ of V^{⊗n} with m_λ(n) > 0, after the P-R1 reductions (λ odd = 2λ1 + 1 → (λ1, ⌈i/2⌉, 2α), repeated), lands in a cell of class (a), (b), (c) or (d).** The trophies (Gao et al. Conj. 4.14, the poster's (n+1)-th factor, Conj. 5.4 for n = 2^k) follow for every such n by flight 3's evaluation of the closed rule (P-C2/C4/C5). I do NOT evaluate this criterion for any n ≥ 262 (that would be measuring new houses).

### C.3 What is missing — exactly one step
**The floor T(r) ≥ Y(r) in the pooled cells that contain a full window (a carry run of m reaching the next digit) or a jump (the top window full), for |I| ≥ 3 and λ ≥ 256.** Equivalently (Theorem U′): a row potential v, constant on every pooled block, with drops between 0 and the drops of the pooled clocks, satisfying v(a) − v(I∖b) + ŷ_{I∖b} ≤ ĉ(a,b). Such a v exists in every one of the 454 872 cells with λ ≤ 255 (MEASURED, P-U2); half the gold is NOT enough there (B.0: λ = 66); in the no-jump part the pooled clocks are a generalized reflected walk (MEASURED, P-GW).
The same holds for the **pooled cells at i = 0** (the Z: m = i − 1 = −1 has every window full): 115 such cells with λ ≤ 255, 94 of them with |I| ≥ 3, first λ = 22 at α = 1 (logs/legC_i0.log); Lemma P closes only the unpooled ones.
**Smallest family where the gap is visible:** with |I| ≥ 3, **λ = 22** (I = {0,1,2}, k = 4): 28 cells, all at α = 1 with m odd (the window of digit 0 is full), 4 without jump, 24 with a jump (logs/legA_hard22.log); with |I| = 2 the first hard cell is λ = 10, α = 1, m_low = 1 (covered by A2). For the cubes, family 22 at α = 1 and m odd enters every n ≡ 2 (mod 4) with n ≥ 26 (i = (n − 22)/2 ≥ 2 even; n = 22 is the cell i = 0); flight 3's check covers these up to n = 261.
**Addendum (19:12):** the missing step now has a measured candidate rule — Rafa's plumber, §10 (P-F4: a certificate in all 40 523 hard cells λ ≤ 255); what is missing is the pencil proof that its joint window is never empty.
**STATUS Leg C: NO CONCLUYO** — the whole 2-part of K(Q_n) for every n, the trophies for general n and the fold law remain open; what is proved is C.1–C.2.

## 5. Rafa's images — which served

Translations sealed in checks/SEALED.md S0 (17:04) before any measurement.

| image | verdict | what it became |
|---|---|---|
| 1, **the rent** («oblígalos a que sea más barato que el alquiler; si por estructura es imposible, ahí tienes la respuesta») | **SERVED — it is the frame of every proof of this flight** | The rent is the slope s of the Legendre transform, and paying it means writing receipts (LP duality). It gave Lemma R2 (receipts paired by the mirror), Lemma M (receipts with ONE constant per rent: the rulers are «priced» against a sea level c(s)), and, read backwards, Theorem U: once the rulers are corrected, no rent is needed at all. Followed literally («a minimal cheaper matching must make a wrinkle»), it became Farkas' lemma: a matching cheaper than the rent is a negative cycle — p arrows with p pivots, Σĉ < Σŷ — and in every unpooled or all-short cell that wrinkle is structurally impossible (Lemma P: a negative clock step forces equal row and column pieces; Theorem H: the reflected walk cannot gain more than (h − α)⁺ per skipped digit). In the hard core I could not find the wrinkle that the structure forbids. |
| 2, **the dancing gold** («siempre valen más que el alquiler … cuanto más bailen, más valen … no se rejuvenece por estructura») | **SERVED IN PART — and one of its readings is FALSE** | «Cuanto más bailen, más valen»: the excess of a matching over the floor is ≥ ½Σ(γ + ν) over its dancing couples in the additive model, ≥ Σγ in unpooled cells, and ≥ the number of dancing couples in every cell λ ≤ 255 — **one coin per dancing couple is right (G1)**. «Siempre valen más que el alquiler» in the strong form «half the gold pays» (G½) is **FALSE**: λ = 66, where a carry run through the skipped gap eats the gold (B.0). «No se rejuvenece; el agua se evapora»: the pooled clock is a Skorokhod reflection (Theorem RW) bounded by the growth α·2^t (Lemma Λ) — it can only be pushed back toward 0, never past the ruler. |
| 3, **el fontanero** (after the flight: the tenants of a shared flat pay the landlord less and pay the plumber) | **SERVED — as a MEASURED law (§10)** | One deposit per shared flat, the cheapest natural one clipped into the window of all its contracts, negotiated together with the mirror flat: a certificate in all 40 523 hard cells λ ≤ 255. The three earlier plumbers each forgot one contract (the neighbour's door, a frontier couple, the mirror flat) and failed there. «Half back» did not serve. |
| 4, **el piso que debe a su espejo** (Mission 4b: what you do not pay the landlord, give it to me; the plumber only charges those who do not owe their mirror) | **SERVED — it is the shape of the proof (§11.1, Theorem F)** | One correction for a tenant and its mirror (zero loop slack); the lower half pays what its mirror paid one level down; ONE new shared flat per digit, priced between the dearest tenant of its lower half and the cheapest of its upper half — the gap between them is exactly the debt of a tenant to its mirror. |


## 6. Sealed predictions, hits and failures

All in `checks/SEALED.md`, each written with its time (pasted from `date`) BEFORE the run.

| id | prediction | ended |
|---|---|---|
| S0 | translation of images 1, 2 | used (§5) |
| P0a–P0d | A2 table = reduced costs; my chords; the (1,1,1) GAP is real; control | **held** 51956/51956, 207600/207600, 7008/7008 (gap cells 192, first λ = 10); control fired 1028 |
| **P-H1** | half-drop law with mirror receipts in every no-jump cell | **FAILED** 846/2700 (780 unpooled) — my prediction was wrong |
| P-H2a–c | all-short ⟹ additive; law holds there; also with half the gold | **held** 29892/29892 each |
| P-RWa–c | reflected walk = PAVA; Theorem H bound; controls | **held** 37638/37638 twice; controls fired 5014 and 400 |
| P-Ma, P-Mb, P-Mc | general form; Lemma M receipts; census | **held** 436752/436752, 20760/20760; hard core 40408, all pooled («more than half»: in fact all) |
| P-Ui | (i′) with the canonical split | **held** (λ ≤ 191, 224670) |
| **P-Uii** | (ii′) with the canonical split | **FAILED** 666 cells (first λ = 34) — wrong |
| P-U2 | free split feasible in every cell | **held** 454872/454872; control (γ := 0) fired 19179 |
| **P-BA1, P-BA2** | block averages give a valid v | **FAILED** both (226 and 128 + 26 cells) — wrong |
| **P-G½ / P-G½x** | (G½) holds; certificate, then exact flow | **FAILED — KILL CRITERION: (G½) false in 219 cells, first λ = 66** — my prediction was wrong |
| P-G1 | (G1) certificate in every cell | **held** 454872/454872; control (two coins) fired 20010/27684 |
| P-GW | generalized reflected walk = PAVA (I gave it 30 %) | **held in every no-jump cell** 64770/64770; **failed** in 6658 jump cells |
| S3 | translation of image 3 (the plumber) | used (§10) |
| **P-F** | a function of the flat's own deposits | **FAILED** every rule (144–158 cells λ ≤ 127); predictions 35 %, 30 % wrong |
| **P-F2** | + the doors | **FAILED**, 13 cells λ ≤ 127 (first λ = 70) |
| **P-F3** | + every frontier couple | held 8 369/8 369 (λ ≤ 127); **FAILED** 87/32 154 (λ ≥ 128, first λ = 142) |
| P-F4 | + mirror flats together | **held 40 523/40 523** (λ ≤ 255) |
| P-F4c | control: same deposits without gold | **fired** 3 849/8 369 |
**Kill criteria:** (G½) FAILED (λ = 66, first line of this report). (G1) never failed in a cell λ ≤ 255. The floor never failed (as in flights 1–3).


## 7. My errors

- **E1 (17:50).** legA_census was launched with an estimate of 6 min; it needed more than 10 and the watchdog killed it at 601 s (λ = 253 reached). By the rule the log is not a result; kept as `logs/legA_census_KILLED_E1.log`; re-run in two ranges (logs/legA_census_A.log, logs/legA_census_B.log), both VIGIA-FIN-OK.
- **E2 (harness, declared).** The session harness keeps the console echo of some commands (e.g. the two runs it moved to the background: the first census and census part B) in its own task files under /private/tmp/claude-501/…/tasks/ (a few hundred bytes each: the last lines of the vigia logs). I never wrote there myself and nothing of the project is there; every log is in logs/. Declared because the rule is «write only inside the folder».
- **E3 (17:14, corrected 18:33).** In A.1, Remark (1), I wrote a garbled formula and the overstatement «without pooling the floor is one line»; true only without carries (P-H1 refuted it with carries). Corrected in place, marked.
- **E4 (17:10–18:33, corrected 18:34).** Sixteen clock times in REPORT.md were written from memory instead of pasted from `date`, some off by up to 13 minutes (e.g. «18:41» for 18:33, «18:12» for 18:01). All corrected against logs/DIARY.md (whose times are pasted from `date`). The same error as flight 3's E5: I repeated it.
- **E5 (18:37).** A shell here-document with back-quotes in the text (unquoted delimiter) was parsed as command substitution: logs/_legA8.md came out empty and the diary line of 18:37:05 says «A.8 written» although it was not. Detected at once; A.8 rewritten with the file tool, a correction line added to the diary (the false line left in place, as written). I checked every other fragment and logs/_legC.md, checks/SEALED.md: none lost text.
- **E6 (declared, addendum).** The plumber was translated four times; each translation was sealed before its run, but translations 2–4 were designed after reading the previous failure (λ = 34, 70, 142). P-F4 is therefore the fourth try: it is supported by the 40 000+ hard cells that did not inform it, but it must be proved by pencil before it is trusted. engines/legD_plumber4.py got a `nogold` control flag after logs/legD_plumber4.log was produced (default path unchanged); engines/legD_plumber3.py was generated from legD_plumber2.py by a script.
- **Wrong sealed predictions (published in §6):** P-H1, P-Uii, P-BA1, P-BA2, P-G½x («holds» — it is false), P-GW (30 % — it held for no-jump cells), P-F (min 35 %, halfback 30 %), P-F2, P-F3.
- Helper fragments of this report were written as `logs/_*.md` before being pasted in; they are kept (no rm).


## 8. Files with md5

(Sat Oct  3 19:12:47 CEST 2026, updated after the addendum; REPORT.md and logs/DIARY.md are still being written and are not listed. The material folder is untouched (its MANIFEST_md5.txt is the auditor's). Killed run kept under its own name: logs/legA_census_KILLED_E1.log. Engines edited after some of their runs, parameters only: legA_census.py (LMIN added after the killed run), legA_BA.py (merge rule < → ≤ after logs/legA_BA_A.log, as sealed in P-BA2), legA_U2.py (MODE added after logs/legA_U2_A/B.log; the default 'full' is the code that produced them), legA_GW.py (tag split by jump after logs/legA_GW_A.log), legD_plumber4.py (nogold control flag added after logs/legD_plumber4.log; default path unchanged).)
```
618d6dc8332d8637f73477126f9260c9 CLAUDE.md
81597f0d82e985ff137b06ae3192acd7 checks/SEALED.md
6be8facdd0838eb98176692d37b798dc engines/leg0_a2.py
7d435acf4831b646fc103db7b553911d engines/legA_BA.py
1944321cc1c094d348bf27eb3371d6dc engines/legA_GW.py
dfaa26ffa791db3626a5165e6e1c8f3b engines/legA_P.py
8188e3e57efe94e7d0c3884b9aac6348 engines/legA_U.py
5b84871d883cccdba6f7a141e6b06cb7 engines/legA_U2.py
02dce2aac27796ef2065ccecc681ba6c engines/legA_census.py
3870e625d7a78278cc4bc8da209a6136 engines/legA_half.py
6e9dc056af1320c124a2e11a481f927b engines/legA_half2.py
5099f4eea35d6cb68a57d37029358a40 engines/legA_hard22.py
8d16f51cc8b8804b416d835bd8259e03 engines/legA_rw.py
3d96f9ec0593a48b2bbe028507e78db0 engines/legA_show.py
c1f26dc5685f67cd970dfd6444b6ec0c engines/legB_exact.py
3d0884f53f78adeca8da5770da326448 engines/legC_i0.py
1256cc154e9e6d51bc317eb28634ab62 engines/legD_diag142.py
1549ad27c50b56431dba79a0b4a20fae engines/legD_plumber.py
27a458d4472d9280ae233380ec655f38 engines/legD_plumber2.py
f8748c6f7cab6210010fb77ec1f8c351 engines/legD_plumber3.py
51a2b4a0ff9b53a8b4a59073e8d8aee0 engines/legD_plumber4.py
97a9cdea630a2f64e2ea1675bacacd06 logs/AUDITOR_smoke_test_of_material.log
8cb5c546b89f29ac482e69f56adec0ea logs/_addendum_plumber.md
8f6ba7a9aec11206e63dd5ca7bb9bf77 logs/_leg0_res.md
3ed57cb19f4a67f894c67b1f67b223fc logs/_leg0_text.md
d9d1c725e3e31192bf5c82b241cc67fa logs/_legA1.md
6598bde1b53a37c8b3f19bb43a7d4e91 logs/_legA2.md
b69b2248c1983355f52fffd6c4ccff95 logs/_legA3.md
909760760c6d551d60ebd7b55b1548e7 logs/_legA4.md
e9513ae17ed7ae564edad0c7f0706b2e logs/_legA5.md
3f94929f125b65b93dd31792f717c8b3 logs/_legA6.md
6d5645420cdabc63089faf687a39622e logs/_legA7.md
34faf4d94a0150e5d55f671588800fb7 logs/_legA8.md
2eaa93b71f01f9dcb6194555093caf2e logs/_legB.md
4016b1cefc82b05cefd38c31924a8e97 logs/_legC.md
efaf5a60bdc11724a2356e8541c045d0 logs/_s0_s9.md
42b03d06d53ec108e422b491047fe529 logs/_s567.md
3d6759e8fa1f7649a9cc4ba6d2f0f920 logs/leg0_a2.log
714f090cc5bb6f6af23caa2e86a49c8b logs/legA_BA2_A.log
442f7999b34f4eef145f67818c63f506 logs/legA_BA_A.log
a962906df2066607c76904fe91306ea7 logs/legA_GW_A.log
990b95789fda985811eb1a8436225a91 logs/legA_GW_B.log
0c86a1a2b94358726f89da34f3e2c19c logs/legA_P.log
5a3d8bf5d71791e6b0d2f7d56a70a96a logs/legA_U2_A.log
6e6703714aa970f042f7747c301bb582 logs/legA_U2_B.log
31c06f2ff20a9b5adbbdc97118c930b7 logs/legA_U_A.log
52d3abe465d64d2de4b26947dd261ea2 logs/legA_census_A.log
0c5e6c5aee0b04638c42acb1a8bb631c logs/legA_census_B.log
77364d85b6eff9d1286729405c443f83 logs/legA_census_KILLED_E1.log
3d44e1877e0247da5fa5c948f56bc2d1 logs/legA_half2_255.log
cbcba1e4495f000018a45bded9a4b31a logs/legA_half_62.log
a5d1c61b5182f0d39e90d7282bddce56 logs/legA_hard22.log
cf404d4901265b1c56429c7575f28258 logs/legA_rw_255.log
7fd5a9a7fbcc2f95080bebd49584c955 logs/legA_show_22_1.log
ef6a6c6416352e7915bbd61ee7570964 logs/legA_show_34_5.log
c037717395ea9198af9d9efbfe6a200f logs/legA_show_70_1.log
2dc7f997a407f9658278b540641ffed2 logs/legB_exact_half.log
7d9fb7aac63a12166249e4e60f3b00c8 logs/legB_exact_one.log
8611ab18eaacee1c3779cd21e95a48dd logs/legB_exact_two_ctrl.log
584067f17f1a4e4d11e975984b975b91 logs/legB_half.log
42aad178708e55cd77e72c58193b3bfb logs/legC_i0.log
bbf370bdffcf0e836e1a2581d7d81aae logs/legD_diag142.log
0038f40414db438f709142796468fb37 logs/legD_plumber2_A.log
18042be97d894562e180740a4cd2318a logs/legD_plumber3_A.log
34dc4c0094a46231c0a917516fa86470 logs/legD_plumber3_B.log
eb27c9fda83515c092dbbb2c301fb57d logs/legD_plumber4.log
8465641ec1da1792824d8fa8299a9af2 logs/legD_plumber4_ctrl.log
af6b256c9fd515890c1a743e7b748eb3 logs/legD_plumber_A.log
e5f8cf13253222f0388fe7dab9edfe88 vigia.sh
```

## 9. The story of this flight, in plain words

- **Starting with the old table.** Flight 3 had left the case table of the 4×4 «in its working notes». I wrote it out line by line from the carries form. All of it was right except one sentence: in one jump pattern it claimed the natural matching was always the cheapest, and a two-line computation (λ = 10) shows it is not — but the cheapest one still sits above the pooled rule, through a different chord. The machine agreed with every line, and with the gap.
- **The rent, taken literally.** Rafa's rent is the slope of a Legendre transform, and «paying the rent» means writing receipts: two numbers per house, one for when it is a row, one for when it is a column, that together never exceed what a couple costs. My first idea was to give each house half of its pooled clock, paired with its mirror. It failed in a third of the cells — and almost all failures were cells WITHOUT pooling. That told me the problem was not the pooling but the carries.
- **The windows.** Splitting the bits of m into the windows between consecutive digits, I saw that when no window is full of ones the carries never talk to each other: the ruler becomes additive. In that world I could compute the pooling exactly: it is a walk that goes digit by digit and bounces off zero — after a digit you do not hold it cannot go below zero, after one you hold it cannot go above. A walk with a wall. And the walk can never run away, because each step is at most α·2^t and those steps add up to less than the next one. With that, each couple pays its half of the drop and keeps, on top, at least its gold plus one coin per digit it jumps over. That closed every cell without full windows, for every family at once.
- **The cells that do not pool.** Next I looked at each step of the clock sequence and found it is always the sum of two pieces, one from the row and one from the column, of the same shape. When the pieces differ, both are positive. So a step can only go the wrong way when both pieces agree — the pooling is always symmetric. That gave a second law: if nothing pools, the two rulers are monotone, and then no gold is needed at all; one constant per rent pays everything.
- **One line for everything.** Putting the two laws side by side, I saw they were the same statement: find two monotone «corrected rulers» whose differences across the mirror are the pooled clocks and which never exceed the cost of a couple. Then the floor follows in one line, without rents. The machine found such rulers in every one of the 454 872 cells it was allowed to look at.
- **The gold that was not there.** Rafa's second image said half the gold always pays. In the additive world it does, with room to spare. But in the very next family with two lower digits after the ones the auditor had looked at, λ = 66, a carry runs right through the gap that the couple skips and eats more than half of the gold. The image was half right: one coin per dancing couple always survives; half the gold does not.
- **What is left.** The cells that pool AND have a full window. There the corrected rulers exist (the machine finds them), and in the simplest example I can see what they do: they cancel, inside each pooled block, exactly the interaction that the carries create between two digits. I could not turn that into a rule for every family. That is the next flight's job.
- **The plumber (after the flight).** Rafa read the report and said: the neighbours pay a escote, water runs down the corridor, they pay the landlord less and give it to the plumber. I translated it: in each shared flat everybody must deposit the same, and the plumber decides how much. The first plumber only looked inside the flat, and failed. The second looked at the doors, and failed in 13 cells, where a couple crossing the frontier pinned the price. The third looked at every contract with the outside and worked in every family up to 127, but at λ = 142 he fixed a flat without asking its mirror flat, to which it is tied, and the mirror was left with no possible price. The fourth plumber sits both mirror flats at the same table — and that one worked in all 40 523 hard cells. What remains is to prove, by pencil, that the table never runs out of prices.

- **Mission 4b (after the window was compacted).** The story of the second mission is in §11.7: the flat that owes its mirror, one price list per house, one new flat per digit, and the one-line reason why the plumber always finds a price.

## 10. Addendum (after the flight was written, 19:00–19:12) — Rafa's image 3, «el fontanero»: MEASURED, it serves

**The image (Rafa, after reading the report, verbatim in substance):** water runs down the corridor; the tenants who pay *a escote* call the plumber and pay the landlord less to pay him; or the clever plumber says «pay less, give it to me, I keep it as a tip, I do a better job, and if I am quick I give you half back». Everybody wins except the landlord. Translation sealed (S3, 19:00) before any measurement.

**Dictionary.** In Theorem U′ the pair (row D, column I∖D) pays the landlord exactly ŷ_D (fixed). The split is a free deposit β_D: v(D) = ŷ_D/2 + β_D, w(E) = v(I∖E) − ŷ_{I∖E}. A tenant's natural deposit is Ω(D)/2, Ω(D) = R_m(D) + R_{m+K}(I∖D) (with it v = R_m, Lemma M). **The water** = a carry crossing a full window: it makes Ω vary. **A shared flat** = a pooled block (maximal run of equal ŷ): there v must be constant, so the whole flat needs one common deposit. **The plumber** = the rule that sets that deposit (the η of A.8).

**Four translations, each sealed before its run (checks/SEALED.md S3, P-F … P-F4):**
| # | the plumber's rule | result (hard core: pooled cells with a full window or a jump, and pooled i = 0) |
|---|---|---|
| P-F | the flat pays a fixed function of its own natural deposits (min / halfback / max / mid / mean) | **FAILED** for every rule: 144 to 158 hard cells with λ ≤ 127 (first λ = 34, m_low = 5: the flat has no breakdown inside, the conflict is at its door with the neighbour ∅) |
| P-F2 | as P-F, pushed into the window allowed by the two doors (monotonicity with the neighbours) | **FAILED**, close: clipmin fails in 13 of 8 369 hard cells λ ≤ 127 (first λ = 70: two couples crossing the frontier pin the deposit to exactly −1) |
| P-F3 | the window is cut by the doors AND by every couple crossing the frontier; clipmin inside | holds in **8 369/8 369** hard cells λ ≤ 127; **FAILED** in 87 of 32 154 for 128 ≤ λ ≤ 255 (first λ = 142: the flat {0},{1} chose without asking its mirror flat {023},{123}, to which the loops tie it) |
| **P-F4** | **a flat and its mirror flat negotiate together** (their two windows plus the couples, loops and common door between them); clipmin for the first, then clipmin for the mirror in what remains | **HELD in every hard cell with λ ≤ 255: 40 523/40 523** (3 964 no-jump, 36 444 jump, 115 at i = 0) |
**Control P-F4c fires:** the same deposits checked with the gold removed fail in 3 849 of 8 369 hard cells (λ ≤ 127). Engines engines/legD_plumber*.py; logs logs/legD_plumber_A.log, logs/legD_plumber2_A.log, logs/legD_plumber3_A.log, logs/legD_plumber3_B.log, logs/legD_plumber4.log, logs/legD_plumber4_ctrl.log, logs/legD_diag142.log, logs/legA_show_70_1.log.

**The rule (P-F4), explicitly — the candidate law for the missing step (A.8, C.3).** Settle the runs of ŷ in o-order. A single tenant D deposits Ω(D)/2. When an unsettled shared flat B is reached, take its mirror flat B* = {I∖D : D ∈ B} (when it is a run; otherwise B alone). Each of B, B* has a window [L, H]: the doors with already-settled neighbours (|β − β_nb| ≤ half the drop of ŷ at that door) and every couple a → b crossing to an already-settled end (v(a) − w(b) ≤ ĉ(a,b)). Between B and B*: β_B − β_B* ≤ u, β_B* − β_B ≤ u′ from the couples, loops and common door joining them. Then β_B = clip(min_{D∈B} Ω(D)/2) into [max(L_B, L_B* − u′), min(H_B, H_B* + u)], and β_B* = clip(min_{D∈B*} Ω(D)/2) into what remains. **In every one of the 454 872 cells with λ ≤ 255 this produces corrected rulers satisfying Theorem U′, hence the floor** (all-short cells: Theorem H; unpooled cells: Lemma M + P; hard core: P-F4).
**Grade: MEASURED** (all already-checked families; no new house). **What a proof needs (the next mission's pencil step):** that the joint window of a flat and its mirror is never empty — i.e. that the doors and the couples crossing the frontier of a shared flat never pull its deposit in incompatible directions. In Rafa's words: the plumber can always find a price that both mirror flats accept without overcharging any couple that crosses their doors. Every failure of the earlier translations was exactly a plumber who did not look at one of those contracts (the neighbour's door at λ = 34; a crossing couple at λ = 70; the mirror flat at λ = 142).
**Which image served:** image 3 SERVED (as a measured law, not yet a theorem). «Pay less to the landlord» = the flat deposits its LOWEST natural deposit (clipmin), as far as the contracts allow; «the plumber» = the rule that sets one price per shared flat; «he says nothing to the landlord» = the landlord still receives exactly ŷ_D from every pair (the deposit cancels between row and column); «everybody wins except the landlord» = every couple keeps v(a) − w(b) ≤ ĉ(a,b). The «half back» reading (halfback, mid) did NOT serve (P-F, P-F2).

## 11. Mission 4b — the second mission of this flight (Rafa's order, after the window was compacted): «the rule that rules everything», close the joint window

*By Rafa's order this flight made two missions in one window: Mission 4 (§0–§10) and Mission 4b (this section). Both go to the auditor together.*

### 11.0 First line — what Mission 4b closes and what it does not

**THE FLOOR IS PROVED FOR EVERY FAMILY (Theorem F, 11.2.6, pencil; gated on every house λ ≤ 255 with 0 failures and two controls firing).** For every λ (every set of lower digits I, every k), every α ≥ 1 and every shift i ≥ 0, every r-matching costs at least the pooled rule: T(r) ≥ Y(r). With Theorem O (flight 3: d_r ≤ Y) and the tropical bound d_r ≥ T this gives **d_r = Y(r): Conjecture W holds in every cell, so — by Theorem D — the whole 2-part of K(Q_n) is given by the closed rule (flight 1, D.5) for EVERY n** (11.4). The proof is an induction on the digits of λ from the bottom: the pooled clocks are a reflected walk with the carries inside (the walk of A.3, now for every cell), the jump never cuts a shared flat (so one price list serves every jump of a house), and at each digit exactly ONE new shared flat appears, self-mirror, whose price can always be set between the highest natural price of its lower half and the lowest natural price of its upper half — a one-line fact. **The rule that rules everything (Rafa's plumber, final form): every shared flat pays one price, set once, at the digit where it is born, between the dearest tenant of its lower half and the cheapest tenant of its upper half; nobody else ever changes price.**
**Not closed here:** the three trophies for general n (Gao et al. Conj 4.14 and 5.4, the poster's (n+1)-th factor) are statements about the closed rule; flight 3 evaluated them for n ≤ 261 (and odd n ≤ 299). They now hold for every n for which they follow from the closed rule, but I did not derive them by pencil from the closed rule for general n (11.4). No new family or cube was evaluated (machines only on λ ≤ 255, the families already checked).

### 11.1 Rafa's image 4 — the flat that owes its mirror (verbatim, translation sealed)

**The image (Rafa, verbatim):** «Esto suena a que el piso {0},{1} le debe dinero a su espejo, {023},{123}; entonces el espejo le dice: lo que no pagues al casero me lo das a mí; por eso hay que negociarlo juntos; al final el fontanero va a cobrar menos dinero, pero cobrará; sólo se llevará dinero de aquellos que no deban a su espejo.» Translation sealed in checks/SEALED.md S4 (19:26:34) before any measurement.
**What it became.** (1) **«Negotiate together» → one correction for rows AND columns** (Theorem U°, P-S0): the tenant and its mirror pay with the same correction φ — the household has no internal slack; this held in every cell, jumps included, and it turned the gold condition into a property of φ alone. (2) **«What you do not pay the landlord, give it to me» → the doubling**: going up one digit, the rows of the lower half pay exactly what their mirrors (the upper half) pay as columns one level down (step 4 of the proof: v' is the child's potential copied to both halves). (3) **«The plumber charges less, but charges» → the one new flat per level**: the price c_F lies between c3 (the dearest tenant of the lower half) and c4 (the cheapest of the upper half), and c3 ≤ c4 is exactly «the lower half owes its mirror»: c3 − c4 = X1(f) ≤ 0, the (negative) clock of the flat's first tenant against its mirror. (4) **«He only takes money from those who do not owe their mirror» → everybody outside the new flat keeps its old price** (the inherited potential), and inside the flat the tenants of the lower half are raised and those of the upper half lowered to one common price — the plumber's money is exactly the debt X1 between mirror tenants. **Verdict: image 4 SERVED — it is the shape of the proof.**

### 11.2 The pencil

**11.2.1 Windows as gates (PROVED, pencil; written 19:52).** For t ∈ I let W_t = [t, next(t)) (the top window is [max I, k)). Call t of **type 1** if bit t of m is 1 and of **type 0** if it is 0, and put κ_t = min(r_t(m), h_t) (type 1) or κ_t = 1 + min(r_{t+1}(m), h_t − 1) (type 0); 1 ≤ κ_t ≤ h_t, and W_t is **saturated** when κ_t = h_t. Adding the digit d = [t ∈ D] and the incoming carry c to m inside W_t (re-derived bit by bit):
- (d, c) = (0,0): no carry; (1,0): κ_t carries if type 1, none if type 0; (0,1): κ_t carries if type 1, none if type 0; (1,1): κ_t carries (type 1, since then 1 + r_{t+1} = r_t) or κ_t carries (type 0).
- the carry leaves W_t iff the window is saturated and (type 1: d ∨ c; type 0: d ∧ c). A type-1 saturated window is the F window of A.4 (an OR gate), a type-0 saturated one the A window (an AND gate), any other window kills the carry.
Hence, with **τ_t := h_t − α2^t − [type 1]κ_t**, **R(D) = τ(D) − Σ_t κ_t · c_t(D) · [type 1 and t ∉ D, or type 0 and t ∈ D]** (c_t(D) = the carry entering W_t): an incoming carry costs κ_t to the dancer set that does NOT hold a type-1 digit or that DOES hold a type-0 digit — of D and I∖D exactly one is exposed at t, and it pays when ITS carry comes in. In an all-short cell no carry is ever born (only F windows give birth), which is A.2.

**11.2.2 Houses and penalties; the top-digit recursion (PROVED, pencil, 19:32; written 19:52).** A **house** is H = (I, k, m_low, α); its base ruler R (carries of m_low + o_D counted up to and including the carry out of bit k − 1) and its **carry-out set** J(D) = [m_low + o_D ≥ 2^k] (an up-set of the o-order). Every cell of the family is a **penalty cell** Cell(H; p_r, p_c): rows R − p_r J, columns R − p_c J, ĉ(a,b) = R_r(a) − R_c(b) + γ(a∖b) — no jump: (0,0); case R: (R, 0); case f: (0, f) (gated, P-T1: 194 292/194 292). Remove the top digit c of I: H' = (I', c, m_low mod 2^c, α), J' its carry-out set, and the window W_c (type T, κ = κ_c, saturation σ, τ = τ_c). From 11.2.1:
  **R(D₀) = R'(D₀) − [T=1]κ J'(D₀),  R(D₀ + c) = τ + R'(D₀) − [T=0]κ J'(D₀),  J(D₀) = [T=1]σ J'(D₀),  J(D₀ + c) = [T=1]σ + [T=0]σ J'(D₀)**  (D₀ ⊆ I').
So the dancers split into the first half (c ∉ D) and the second half (c ∈ D) of the o-order; γ_I(Δ) = γ_{I'}(Δ) + h_c when c ∉ Δ ≠ ∅ (both ends in the same half: the arrow skips the top gap) and γ_I(Δ₀ + c) = γ_{I'}(Δ₀). The matrix of Cell(H; p_r, p_c) is block-triangular in the halves: rows of the second half → columns of the first half is the matrix of the child Cell(H'; q₁(p_r), q₀(p_c)), and the two diagonal blocks are child matrices with h_c added to every non-loop arrow, where **q₀(p) = [T=1](κ + pσ), q₁(p) = [T=0](κ + pσ)**. The clocks of the first half are those of Cell(H'; q₀(p_r), q₁(p_c)) shifted by −τ, those of the second half those of Cell(H'; q₁(p_r), q₀(p_c)) shifted by +τ. **The class of penalty cells is closed under the recursion, and a jump is just a penalty on the carry out of the house.** (Cells with both penalties positive do not occur in M(λ, i) but occur as blocks; P-T1: all are certifiable.)

**11.2.3 Theorem U° — one correction for rows and columns (PROVED, pencil; it is Theorem U with φ′ = φ).** If φ: 2^I → Q satisfies
 (G) **φ(a) − φ(e) ≤ γ(a∖e) for every e ⊊ a** (a property of φ and the family's gaps ALONE: no m, no α, no jump),
 (M) **R + φ non-increasing in o-order** (then R − pJ + φ is too, J being an up-set),
 (E_p) **φ(D) − φ(I∖D) ≥ ε^p_D** (ε^p = pooled minus raw clocks of Cell(H; p_r, p_c)),
then v = R − p_r J + φ, w = R − p_c J + φ satisfy Theorem U (i′)(ii′)(iii′), so **T ≥ Y in Cell(H; p_r, p_c)**. (Loops: v(a) − w(a) = (p_c − p_r)J(a) = ĉ(a,a), so zero loop slack.) MEASURED (P-S0): such a φ exists in every pooled cell λ ≤ 255, jump cells included.

**11.2.4 One price list per house; the jump never cuts a flat (pencil reduction 19:48, written 19:52; MEASURED P-UNI, P-CUT).** At p = (0,0) the clocks x⁰_D = R(D) − R(I∖D) of EVERY house are antisymmetric, so (E_0) at D and I∖D forces φ(D) − φ(I∖D) = ε⁰_D. Since x^{(0,p)}_D = −x^{(p,0)}_{I∖D}, a φ that serves (p,0) and (0,p) as well forces ε^{(p,0)} = ε⁰ pointwise. And conversely: **if the carry-out boundary of J is a block boundary of PAVA(x⁰) (Cut Lemma), then PAVA(x⁰ − p_rJ + p_cJ∘mir) = PAVA(x⁰) − p_rJ + p_cJ∘mir** (a shift constant on blocks and non-increasing keeps every block valid), so ε^p = ε⁰ and **one φ certifies every penalty cell of the house**. So the whole floor splits into
 **(1) the Cut Lemma** (the jump never cuts a flat) and **(2) a certificate for the base cell of every house** (antisymmetric clocks: v = R + φ with φ(D) − φ(I∖D) = ε⁰_D exactly).
MEASURED: (1) in 86 352/86 352 houses λ ≤ 255, α ≤ 8 (P-CUT); one φ for all penalties in 6 074/6 074 pooled houses (P-UNI).

**11.2.5 The recursive construction («la regla que lo domina todo», candidate; pencil for the parts marked PROVED; written 20:08; the price rule is superseded by the proved interval of 11.2.6).** Fix a house H with digits t_1 < … < t_n and build the houses H_j = ({t_1..t_j}, t_{j+1} (t_{n+1} := k), m_low mod 2^{t_{j+1}}, α); H_0 has the single dancer ∅ (clock 0, potential 0). Going from H' = H_{j−1} to H = H_j adds the top digit c = t_j with (T, κ, σ, τ) of its window. Put, for D₀ ⊆ I' (all quantities of H' antisymmetric base cell):
  **X1(D₀) = ŷ'(D₀) − τ − [T=1]κJ'(D₀) + [T=0]κJ'(I'∖D₀),  X2(D₀) = ŷ'(D₀) + τ + [T=1]κJ'(I'∖D₀) − [T=0]κJ'(D₀) = −X1(I'∖D₀).**
- **(W) the walk (PROVED, given the Cut Lemma for H').** The base clocks of H are x'(D₀) − τ − [T=1]κJ' + [T=0]κJ'∘mir on the first half and the mirror on the second; by the Cut Lemma for H' each half pools to X1 (resp. X2) (a non-increasing shift constant on the blocks of ŷ'), and PAVA of the two halves glued is **ŷ = [max(X1, 0), min(X2, 0)]**: if the last X1 is < 0 the two halves pool together into ONE central block, of sum 0 by antisymmetry, hence of value exactly 0 (an integer: the integer splitting never acts), absorbing exactly the X1 ≤ 0 and the X2 ≥ 0 (every prefix sum of that block is ≤ 0, so it does not split). This is the reflected walk of Theorem RW with the carries put in, and it proves P-GW for every no-jump cell once the Cut Lemma is proved.
- **(V) the potential.** v' := [V − [T=1]κJ', τ + V − [T=0]κJ'] where V = the potential of H' (that is: v' = R + φ with φ(D) := φ_{H'}(D∖c), the child's correction ignoring the top digit). Then **v' satisfies (G) and (E) at level H (PROVED: (G) because γ_H ≥ γ_{H'} on every arrow and = on the arrows that drop c; (E) because v'(D₀) − v'(I∖D₀) = X1(D₀) by the formula, and X1 = ŷ outside the central flat), and (M) except at the junction.** The junction holds iff the last X1 is ≥ 0, i.e. iff the two halves do not pool together.
- **(F) the one new flat.** The central zero run F = {X1 ≤ 0} ∪ ({X2 ≥ 0} + c) is the ONLY new flat of the level (every other flat is a child flat, shifted; the shifts only separate them), and it is self-mirror. Give it ONE price c_F: the **plumber's window** is the doors [v'(after F), v'(before F)] ∩ every couple with exactly one end in F (v'(a) − ĉ(a,e) ≤ c_F ≤ v'(e) + ĉ(a,e)); every arrow with both ends in F must have ĉ ≥ 0. Rule **winmid**: c_F = the midpoint of the two natural prices at the junction, (v'(I') + v'({c}))/2, clipped into the window.
- **(J) the jump.** The carry-out set of H is J(D₀) = [T=1]σJ'(D₀), J(D₀ + c) = [T=1]σ + [T=0]σJ'(D₀) (11.2.2), and the real cells of the house are certified by v = V − P_rJ, w = V − P_cJ (11.2.3–11.2.4).
**MEASURED (P-WIN):** in all 129 528 houses λ ≤ 255 (α ≤ 6) the window is never empty and the construction is a certificate at every level; it certifies every real cell with i ≥ 1 (no jump, case R, case f). **The midpoint alone fails** (λ = 34: above the door), **the door-clipped midpoint fails** (λ = 70: two mirror couples pin the price to −1), **the extreme prices of the door window fail** (λ = 6): the window really is cut by the couples, and it is the window, not any fixed formula, that the proof must control.
**Mirror couples (PROVED, pencil):** for an arrow a → e with a ∈ F, e before F and its mirror I∖e → I∖a, the two bounds give c_F ≤ v'(e) + ĉ(a,e) and c_F ≥ v'(I∖e) − ĉ(I∖e, I∖a), whose difference is **2γ(a∖e) − (ε_a − ε_e)** (using v'(e) − v'(I∖e) = ŷ_e and ĉ(a,e) + ĉ(I∖e, I∖a) = x_a − x_e + 2γ). So a mirror pair of couples never empties the window as long as the **residual law ε_a − ε_e ≤ 2γ(a∖e)** holds (P-Ui, A.5: held in every cell). At λ = 70 this is exactly what pins the price: ε = 0 at both ends and γ = 0.

**11.2.6 THEOREM F (the floor, for every family, every α ≥ 1, every shift i ≥ 0) — pencil proof (20:08–20:12, written 20:13 before its gate; gate P-PROOF in 11.3).**
*Statement.* In every cell (λ, i, α) of every family (|I| ≥ 1) and for every r: T(r) ≥ Y(r). With Theorem O (d_r ≤ Y) and the tropical bound (d_r ≥ T): **d_r = Y(r): Conjecture W holds everywhere.**
*Induction.* Fix the family (I, k), α ≥ 1 and m_low ∈ [0, 2^k). For j = 0..n let H_j be the house ({t_1..t_j}, k_j := t_{j+1} (k_n := k), m_low mod 2^{k_j}, α); write N_j = 2^j, R_j its base ruler, J_j its carry-out set, x_j(D) = R_j(D) − R_j(I_j∖D) its base clocks (antisymmetric), ŷ_j = integer PAVA of x_j. Claim for every j, with V_j built below:
 (E_j) V_j(D) − V_j(I_j∖D) = ŷ_j(D);  (M_j) V_j non-increasing in o-order;  (G_j) V_j(a) − V_j(e) ≤ R_j(a) − R_j(e) + γ_j(a∖e) for e ⊊ a;
 (Cut_j) PAVA(x_j) = PAVA(x_j[< b]) ++ PAVA(x_j[≥ b]) at the first b with J_j = 1 (and so, by antisymmetry, at the mirror point);  (Λ_j) |ŷ_j| ≤ α(2^{k_j} − 1).
*Base j = 0:* one dancer ∅, x = ŷ = 0, V_0 = 0, J_0 = 0. All trivial.
*Step j − 1 → j* (H' = H_{j−1} with V := V_{j−1}, ŷ' := ŷ_{j−1}, J' := J_{j−1}; c = t_j; window W_c with T, κ, σ, τ, h = h_c = k_j − c; 11.2.1–11.2.2):
1. **Walk.** The first-half clocks are x' + d₁, d₁ := −τ − [T=1]κJ' + [T=0]κJ'∘mir, an integer non-increasing step function with steps only at the J'-boundary and its mirror; by (Cut_{j−1}) PAVA(x' + d₁) = ŷ' + d₁ =: X1 (blocks unchanged, integer splitting shifted). The second half pools to X2 = −X1∘mir. Gluing (11.2.5 (W)): **ŷ_j = [max(X1, 0), min(X2, 0)]**.
2. **Λ_j.** X1 ≤ α(2^c − 1) + max(−τ, −τ + κ) ≤ α(2^c − 1) + α2^c = α(2^{c+1} − 1) ≤ α(2^{k_j} − 1) (−τ = α2^c − h + κ ≤ α2^c for T = 1; −τ + κ = α2^c − h + κ ≤ α2^c for T = 0; κ ≤ h), and max(X1, 0) ≥ 0; the second half by antisymmetry.
3. **Cut_j.** J_j = [T=1]σ[J'; 1] or [T=0]σ[0; J'] or 0 (11.2.2). (a) T = 1, σ = 1, J' ≢ 0: the boundary b is the J'-boundary inside the first half; just before it X1 = ŷ' − τ = ŷ' + α2^c ≥ α > 0 (Λ_{j−1}; τ = −α2^c when saturated of type 1), so that element is not in the central block and the child's split at b survives. (b) T = 1, σ = 1, J' ≡ 0: the boundary is the junction and X1(I') = ŷ'(I') + α2^c ≥ α > 0: no merge. (c) T = 0, σ = 1: the boundary b′ is the J'-boundary inside the second half and X2(b′) = ŷ'(b′) + (h − α2^c) − h ≤ −α < 0 (Λ_{j−1}): not in the central block, the split survives. Otherwise J_j ≡ 0.
4. **The inherited potential.** v' := [V − [T=1]κJ', τ + V − [T=0]κJ'] = R_j + φ with φ(D) = (V − R_{j−1})(D∖c). Then (G) holds for v' at level j (same-half arrows gain h in γ_j, arrows that drop c have γ_j = γ_{j−1}); in fact for same-half arrows **ĉ_j(a, e) ≥ v'(a) − v'(e) + h**; (E): v'(D₀) − v'(I_j∖D₀) = X1(D₀) and v'(D₀ + c) − v'(I'∖D₀) = X2(D₀); (M) holds inside each half (V non-increasing, J' an up-set).
5. **The junction jump is small.** v'({c}) − v'(I') = −X1(I') = −ŷ'(I') + τ + [T=1]κJ'(I') ≤ α(2^c − 1) + h − α2^c = **h − α** (Λ_{j−1}).
6. **No central flat** (X1(I') > 0): V_j := v'; (M) at the junction is X1(I') > 0. Done.
7. **The central flat** F = F₁ ∪ (F₂ + c), F₁ = {X1 ≤ 0} (a final segment of the first half), F₂ = {X2 ≥ 0} = mirror of F₁ (an initial segment of the second): ŷ_j = 0 exactly on F. Let f = first of F₁, so I_j∖f = last of F₂ + c; p = the element before f, p* = I_j∖p the element after F (when they exist). Put **c3 := v'(f) = max_{F₁} v', c4 := v'(I_j∖f) = min_{F₂+c} v'**. Then **c3 − c4 = X1(f) ≤ 0** (step 4, (E)), c3 ≤ v'(p), v'(p*) ≤ c4 and v'(p*) ≤ v'(p) (= X1(p) > 0), so the **plumber's interval [max(c3, v'(p*)), min(c4, v'(p))] is non-empty**. Choose c_F in it and put V_j := c_F on F, v' elsewhere.
8. **Checks.** (E_j): on F both sides are c_F and ŷ_j = 0; off F unchanged. (M_j): doors by the choice of c_F. (G_j): arrows outside F unchanged; for a couple with one end in F (F is a contiguous segment, so the other end lies before F in the first half if it is the smaller set, after F in the second half if it is the larger):
 - a ∈ F₂ + c, e before F: c_F ≤ c4 ≤ v'(a) and v'(a) − v'(e) ≤ ĉ(a,e).
 - a ∈ F₁, e before F (same half): c_F ≤ c4 ≤ v'({c}) ≤ v'(I') + h − α ≤ v'(a) + h − α, and ĉ(a,e) ≥ v'(a) − v'(e) + h.
 - e ∈ F₁, a after F: c_F ≥ c3 ≥ v'(e) and v'(a) − v'(e) ≤ ĉ(a,e).
 - e ∈ F₂ + c, a after F (same half): c_F ≥ c3 ≥ v'(I') ≥ v'({c}) − h + α ≥ v'(e) − h + α, and ĉ(a,e) ≥ v'(a) − v'(e) + h.
 - both ends in F, same half: ĉ ≥ v'(a) − v'(e) + h, and v'(a) − v'(e) ≥ v'(I') − v'({c}) ≥ −(h − α) [both in F₁: v'(a) ≥ v'(I'), v'(e) ≤ c3 ≤ c4 ≤ v'({c}); both in F₂ + c: v'(a) ≥ c4 ≥ c3 ≥ v'(I'), v'(e) ≤ v'({c})], so ĉ ≥ α > 0; cross (a ∈ F₂ + c, e ∈ F₁): ĉ ≥ v'(a) − v'(e) ≥ c4 − c3 ≥ 0.
 (Used throughout: I' ∈ F₁ and {c} ∈ F₂ + c because F₁ is a non-empty final segment and F₂ its mirror, so c3 ≥ v'(I') and c4 ≤ v'({c}).)
 So (E_j), (M_j), (G_j) hold. ∎ (induction)
*From the base cell to every real cell.* At j = n the house is (I, k, m_low, α). (a) **i ≥ 1:** the cell is the penalty cell (P_r, P_c) ∈ {(0,0), (R,0), (0,f)} (11.2.2). Put v := V_n − P_rJ_n, w := V_n − P_cJ_n. (G) is (G_n) (the penalties cancel); v, w are non-increasing; and v(D) − w(I∖D) = ŷ_n(D) − P_rJ_n(D) + P_cJ_n(I∖D) = PAVA(x_n − P_rJ_n + P_cJ_n∘mir)(D) by (Cut_n) — the pooled clocks of the cell. Theorem U ⟹ T ≥ Y. (b) **i = 0:** famcheck's i = 0 cell is exactly the base cell of the house m_low = 2^k − 1 with the row ∅ deleted (klow(2^k − 1, o_D) = k − min D for D ≠ ∅, so its ruler is H − A0 − k); there J_n = [D ≠ ∅], so (Cut_n) at b = 1 says PAVA(x_n)[1:] = PAVA(x_n[1:]) — the pooled clocks of the i = 0 cell — and v = w = V_n restricted satisfies Theorem U (the natural column sets F_r never contain the column I, mirror of the missing row). ∎
*Remark (the integer splitting; checked in the proof).* PAVA here merges only on a strict increase and splits each block «ceil first». Two neighbouring blocks with the SAME non-integer mean would make the split non-monotone and would make the shifts of step 1 change the rounding. By induction this never happens: in step 1 the blocks of each half are the child's blocks shifted by a non-increasing step function (gaps only grow), the central block has the integer value 0, and the blocks next to it have means of strict sign; so every non-integer level set is ONE block, the integer fit is non-increasing, and integer splitting commutes with every shift used (steps 1, 3 and the penalties). (A block's prefixes have mean ≤ the block's mean, so while the second half is processed no child block of mean ≤ 0 is ever pulled into the central block, and the final partition is the one described.)
*What it uses:* Theorem U (A.5, one line), PAVA's block/gluing properties (A.3), the gate algebra of the windows (11.2.1), and nothing measured. **The plumber's rule in one sentence: the new shared flat of each level pays one price between the highest natural price of its lower half and the lowest natural price of its upper half (and inside its two doors); everything else keeps the price it had one level down.**

### 11.3 Gates (machines only on λ ≤ 255)

| id | what | result |
|---|---|---|
| P-W1 | the walk certificate (each side absorbs its own clips) | **FAILED** (M) in 683 hard no-jump cells; (G) never failed |
| P-T1 | Theorem U′ feasible in two-sided penalty cells | held 583 876/583 876 (λ ≤ 255, p ∈ {1,2,3}²); gate of the penalty form 194 292/194 292 |
| P-S0 | a certificate with ZERO loop slack (one correction φ) | held in every pooled cell λ ≤ 255, jumps included (45 422) |
| P-UNI | one φ per house for all penalties at once | held 6 074/6 074 pooled houses |
| P-CUT | the jump never cuts a flat; penalties only shift | held 86 352/86 352 houses (α ≤ 8); control fired 4 008 |
| P-REC | recursive construction, rules mid, lo, hi, avg | gates held; rules **FAILED** (M) (λ = 34) |
| P-REC (clipped) | midclip, loclip, hiclip (added after the failure, declared) | held λ ≤ 63; **FAILED** (G) 16 houses λ ≤ 127 (λ = 70) |
| P-REC-d | any price of the door window (top, bot) | **FAILED** (G) 2 174 houses λ ≤ 127 (λ = 6) |
| **P-WIN** | **winmid: the window of the one new flat per level** | **held in 129 528/129 528 houses λ ≤ 255, every level; Theorem U in every real cell i ≥ 1** |
| **P-PROOF** | **the proof exactly as written (11.2.6): three prices of the plumber's interval, every lemma at every level, every real cell incl. P ∈ {1,2,3,7,50} and i = 0** | **0 failures**: 129 528 houses × 3 prices; level checks Rec/W/Λ/JX 436 896 each, Cut 218 448, c3 ≤ c4 32 142; real cells 64 764 no-jump + 323 820 R + 323 820 f + 1 476 i = 0. Controls fire: c_F = v'(I') breaks 800 houses; no gold breaks 29 192 cells |

### 11.4 Assembly — what is now proved for every family

**Theorem F ⟹ Conjecture W everywhere.** For every family λ, every α ≥ 1 and every shift i ≥ 0: T(r) ≥ Y(r) (Theorem F, 11.2.6) and d_r ≤ Y(r) (Theorem O, flight 3 B.4, with convexity of d_r) and d_r ≥ T(r) (tropical: the r-th determinantal divisor is the minimum valuation of the r × r minors, each a sum of products along r-matchings of the support). Hence **d_r = Y(r) for every r**, i.e. the Smith form of M(λ, i) is the pooled rule.
**The whole 2-part, every n.** By Theorem D (flight 2, with flight 3's Theorem RT′: no tilting citation) the 2-part of K(Q_n) is the direct sum over the families λ ≡ n (mod 2) of the Smith forms of the M(λ, (n − λ)/2) with the multiplicities m_λ(n) of the fusion recursion (PROVED, flight 1), plus the small clocks of each family (flight 2/3). Mission 4's Theorem C (C.2) assembled this conditionally on every cell lying in a proved class; Theorem F puts EVERY cell in a proved class. Therefore, **for every n ≥ 1, Syl_2 K(Q_n) ⊕ Z_2 ≅ ⊕_λ [⊕_{a=1}^{k−1}(Z/2^a)^{2^{|I|+k−1−a}} ⊕ H(λ, (n−λ)/2)]^{m_λ(n)}** — flight 1's closed rule D.5, now a theorem. P-R1 and the per-family machine check of flight 3 are no longer needed (they remain as independent confirmations for λ ≤ 255, odd λ ≤ 511).
**Dependencies, all named:** Theorem D (flight 2 A.1, A.2, B.1, C.0, C.4 + flight 3 Theorem RT′); the reduction of the cell costs to m_low, R, f (flight 3 C.4, pencil, gated) and its window form (this flight A.4, 11.2.1–11.2.2); Theorem O (flight 3 B.4); Theorem U (this flight A.5); Theorem F (11.2.6). Nothing measured is used in the proof; the gates P-REC/P-WIN/P-PROOF check it on λ ≤ 255.
**The trophies.** Gao et al.'s Conjecture 4.14 (the n-th invariant factor), the JMM poster's (n+1)-th factor and Gao et al.'s Conjecture 5.4 are statements about the group, hence about the closed rule. They are now theorems for every n for which their derivation from the closed rule holds; flight 3 evaluated that derivation for n ≤ 261 and odd n ≤ 299 (P-C2/C4/C5). **For general n I have NOT written a pencil derivation of the three trophies from the closed rule** — that is a separate (and purely arithmetic) task on the rule, with no Smith form and no matching left in it.
**Also proved on the way, for every family:** P-GW (the pooled clocks of every no-jump cell are the generalized reflected walk) and its jump version; the Cut Lemma (a jump never cuts a flat; the pooled clocks of every jump cell are the base pooled clocks shifted by the penalty); the bound |ŷ| ≤ α(2^k − 1) (Lemma Λ for every cell); the residual law ε_a − ε_e ≤ 2γ(a∖e) for every arrow of every cell (from (G) and (E): ε_a − ε_e = [φ(a) − φ(e)] + [φ(I∖e) − φ(I∖a)] ≤ 2γ; P-Ui).

### 11.5 Sealed predictions of Mission 4b

All in checks/SEALED.md (section «MISSION 4b»), each sealed with its time from `date` BEFORE its run.
| id | prediction | ended |
|---|---|---|
| S4 | translation of image 4 | used (11.1) |
| **P-W1** | walk certificate (each side absorbs its own clips) — 25 % | **FAILED** (M) 683 hard + 128 short cells; (G) never failed |
| P-T1 | two-sided penalty cells certifiable — 60 % | **held** 583 876/583 876 |
| **P-S0** | zero loop slack: 95 % no-jump, 30 % jump | **held everywhere** (my 30 % wrong in the good direction); P-S1 a fortiori |
| P-UNI | one φ per house for all penalties — 45 % | **held** 6 074/6 074 |
| P-CUT1/2 | the jump never cuts a flat; penalties only shift — 85 % | **held** 86 352/86 352; control fired 4 008 |
| P-REC-a | recursion, walk, cut at every level — 100 % | **held** |
| **P-REC-b** | rule mid — 35 % | **FAILED** (M) 8 houses λ ≤ 63 (λ = 34) |
| **midclip/loclip/hiclip** | (declared: added after the failure) | **FAILED** (G) 16 houses λ ≤ 127 (λ = 70) |
| **P-REC-d** | any price of the door window — 70 % | **FAILED** (G) 2 174 houses (λ = 6) |
| P-WIN | the window of the one new flat is never empty — 75 % | **held** 129 528/129 528 |
| **P-PROOF** | the pencil proof, exactly as written — 100 % | **held, 0 failures**; controls fired (800 houses; 29 192 cells) |

### 11.6 Errors of Mission 4b

- **E7 (declared, 19:53–19:59).** The door-clipped rules midclip, loclip, hiclip and the full-window rule winmid were designed after seeing the failures of mid (λ = 34) and midclip (λ = 70) — the same forking-paths risk as E6. They were sealed or declared before their own runs; the final rule is not a measured rule at all but the interval of a pencil proof (11.2.6), gated afterwards with three different prices of the interval (P-PROOF).
- **E8 (20:32).** The RESULT line of P-PROOF in checks/SEALED.md was written with a garbled placeholder («Rec 437 0.. (see log)»); a correction line with the exact counts was appended below it (the wrong line left in place).
- **E9 (20:33, corrected 20:34:08).** I wrote nine clock times in §11 from memory (e.g. «19:40» for the pencil of 11.2.1, «20:55» in §0, «20:0x», «20:5x») — the same error as E4 of this flight and E5 of flight 3, a third time. All corrected against logs/DIARY.md (times pasted from `date`). The rule I keep breaking: never type a time; paste it. engines/legE_rec.py was edited twice between runs (rules added: midclip/loclip/hiclip/top/bot, then winmid); the logs say which rule produced each.

### 11.7 The story of Mission 4b, in plain words

- **The flat that owes its mirror.** Rafa read my line about the flats {0},{1} and {023},{123} and said: the flat owes money to its mirror; what it does not pay the landlord it gives to the mirror; so they negotiate together, and the plumber only charges those who do not owe their mirror. I took the first part literally: a tenant and its mirror should not keep separate books. In the certificate that means ONE correction for the row and the column of the same house. I expected it to fail with jumps; it held in every cell. And with one correction the gold condition stopped depending on the cell at all: it became a property of the price list against the gaps of the family.
- **The jump never cuts a flat.** Then I asked: does one price list serve all the jumps of a house? It did, everywhere. Working out what that forces, I found it forces something very concrete: the place where the carry jumps out of the house never falls inside a shared flat. The machine confirmed it in every house, and the control (move the place by one) broke. So a jump is just a fine paid by a whole block of flats at once — it moves their clocks without changing who shares with whom.
- **One digit at a time.** Then the house could be built digit by digit from the bottom. Adding a digit doubles the house: a lower half and an upper half, mirror of each other. The lower half's rows pay what the upper half's columns paid one level down — Rafa's «give it to me». And the clocks of the new house are the old ones, shifted, with one wall at zero: everything that tries to cross zero gets stuck in ONE new shared flat in the middle. Only one new flat per digit, and it is its own mirror.
- **The plumber's price.** The first prices I tried for that new flat failed: the midpoint broke a door at λ = 34; the midpoint pushed inside the doors broke two couples at λ = 70; the extreme prices of the doors broke the gold at λ = 6. With the full window (doors and couples) it worked everywhere, so the question was only why the window is never empty. Looking at who sits in the new flat, the answer took one line: the dearest tenant of its lower half is cheaper than the cheapest tenant of its upper half, because the difference between them is exactly the clock of that tenant against its mirror, and that clock is negative — that is why it fell into the flat. Between those two prices every contract is paid: the couples that cross between the halves are paid by the old prices, and the couples inside one half have the whole top gap of the house as gold, which is always more than the jump at the middle. That is the theorem.
- **What it closes.** That was the last missing step: the floor holds for every family, every shift, every α, and with what the earlier flights proved, the whole 2-part of the sandpile group of every cube is given by flight 1's closed rule. The machine checked the proof exactly as written on every house it is allowed to look at, with three different prices of the interval, and the two controls broke as they must. The trophies for general n are now a question about the closed rule only; I did not do that arithmetic here.

### 11.8 Files of Mission 4b with md5

(Sat Oct  3 20:35:31 CEST 2026. REPORT.md and logs/DIARY.md are still being written and are not listed. These md5 SUPERSEDE §8's lines for CLAUDE.md and checks/SEALED.md (both changed in Mission 4b); every other file of §8 is unchanged. Every log below ends in VIGIA-FIN-OK exit=0 (checked). engines/legE_rec.py was extended between runs (rules midclip/loclip/hiclip, then top/bot, then winmid); each log is named after the rule that produced it, and the default code paths of earlier rules were not changed. The fragment logs/_md5_m4b.txt holds this list.)
```
56af70eae0baddcd66f9e0482c98aadb CLAUDE.md
505fee470bde84bd2ee2db881d2f42a7 checks/SEALED.md
f71f81f5d45eff7957e8ec5fdb490bcd engines/legE_cut.py
badf7548ef901158b4d6b632d2144e6e engines/legE_pen.py
03c118a913fdb9ff7ea60cf418ec9d0c engines/legE_proof.py
83ccdcf43d89b106adb05f467804e5f2 engines/legE_rec.py
e8f62f8741d11afd1cb9e56c065d8a8d engines/legE_slack.py
496514d3ea07d7defc8739c89add845f engines/legE_uni.py
7fd67fb4ec0ec65d873b9081a5f70fea engines/legE_walk.py
8e251f023e91c509d52264c55a00f984 logs/legE_cut.log
550b2e009fdefd0423da516d1011d5c0 logs/legE_pen_A.log
1f95f9a9225e1924478fb41e0964a47e logs/legE_pen_B.log
66c3642e2b287334e34ad534800763dd logs/legE_proof_127.log
c8274c2cb4548870b2d7ee262db6231f logs/legE_proof_62.log
47c99a8a1c0c7746f2f84e124f25b518 logs/legE_proof_B1.log
210e6241831cc549a1708edb13c5df71 logs/legE_proof_B2.log
c9bd5e40e2414a03d5f8e0954417bb19 logs/legE_proof_B3.log
fc895aba910214d515256849737df4d6 logs/legE_rec_avg_63.log
83c4c5ea23cb2e8e074bfa5cec3f2d4b logs/legE_rec_bot_127.log
9b8f849a79446f03c8cb12df737cd0f3 logs/legE_rec_hi_63.log
95fc706326e5046e10ba1d5ff6ac6fec logs/legE_rec_hiclip_127.log
0f1fdc68bcfbba19d317b5c7857c0ea0 logs/legE_rec_hiclip_63.log
28c9435ef457d60e377942f4b08c78fa logs/legE_rec_lo_63.log
24a01f1debf4f6d0264ae5491721b5b3 logs/legE_rec_loclip_127.log
b96d0ed712ffd5081c636c9ee6a9ba17 logs/legE_rec_loclip_63.log
ceefffb18330e9101ac0629b010e86da logs/legE_rec_mid_63.log
1dd499489d6a7387fb7ebc66d70043a1 logs/legE_rec_midclip_127.log
5b71ac5bfe72c544ee9a10657f981f3b logs/legE_rec_midclip_63.log
2ce6a97c76d37a18c0e0ff6774ae479d logs/legE_rec_top_127.log
1a4dac0390ea2ad9656d91222f45a3d8 logs/legE_rec_winmid_127.log
46c13e975e6152f3079986c54193a914 logs/legE_rec_winmid_B1.log
eaf09660bcae86852528ed9edb6a0039 logs/legE_rec_winmid_B2.log
d596144015c66835a11f59b76340e03a logs/legE_slack_A.log
3129a0a8b0863975aeebae8d8d5edbe7 logs/legE_slack_B.log
6e3ff6672b38e15670e5af573f7f5c1d logs/legE_uni.log
308b10d3969a622c7d2a6fcb1f3241db logs/legE_walk.log
eb27c9fda83515c092dbbb2c301fb57d logs/legD_plumber4.log
51a2b4a0ff9b53a8b4a59073e8d8aee0 engines/legD_plumber4.py
e5f8cf13253222f0388fe7dab9edfe88 vigia.sh
```

## 12. The conversation between the two missions (added 20:40; recorded so that no metaphor is missing)

Between Mission 4 and image 3 Rafa asked me for metaphors «of the kind he uses» for what remained, plus my gut feeling, and then for one short question. They were only in the chat; they are recorded here (summary in English, the question verbatim).
- **My map of what remained (chat, 18:48 local).** What already paid the rent by structure: the houses where the water does not cross from one room to the next (all-short: «the clock is a child walking down a corridor and bouncing off the wall», Theorem RW) and the houses where nobody pays *a escote* (unpooled: row and column pay each step by halves, Lemma P/M). What was missing: the houses that pay *a escote* AND have water running down the corridor (a full window), in three rooms — without a leak in the roof (no jump), with a leak in the roof (the jump: the house looks different from the street, rows, than from the yard, columns), and the house with every window open (i = 0, «la Z»). I said a plumber was needed inside each shared flat, and that Frobenius' wrinkle had an exact name here: a negative cycle.
- **My gut feeling then (chat, 18:48 local), against what happened.** I said «possible, not a well»; the path I smelled was peeling the lowest flooded window with the salsa (bottom digit); the hypothesis to carry was the corrected rulers, NOT half the gold. My numbers: no-jump core in one flight ≈ 70 %, jumps in another ≈ 50 %, the Z with them, everything in «two flights with luck, three without». **What happened:** everything closed in one more mission (Mission 4b), jumps and the Z together with the no-jump core — because the jump turned out to be a penalty that never cuts a flat (11.2.4) and the Z is the house m_low = 2^k − 1 minus one row (11.2.6). The induction went digit by digit as I smelled, but from the TOP digit's point of view (each digit doubles the house), and the carried hypothesis was indeed the corrected rulers — in their one-correction form.
- **The one-line question I gave Rafa (chat, 18:50 local, verbatim):** «Cuando el agua corre por el pasillo y los vecinos pagan a escote, ¿qué hace el fontanero dentro de cada piso para que ninguna pareja que baila pague menos que el alquiler?» His answer was image 3 (§10); his reading of my λ = 142 line was image 4 (§11.1).
- **All of Rafa's images in this flight:** 1 the rent, 2 the dancing gold (§3–§5), 3 the plumber (§10), 4 the flat that owes its mirror (§11.1). Verdicts in the table of §5.

## 13. The state of the art — is «Reiner's conjecture» closed? (web research, Rafa's order «cielo, infierno y purgatorio»; written 20:51)

**Method.** Web search (several queries, standard and extended) and the originals I could open; every original I read is saved in `sources_4b/` (md5 in `logs/_md5_sources4b.txt`) and was read as text (pdftotext) or, for the handwritten notes, page by page as images. The auditor's `material/sources/` (Gao–Marx-Kuo–McDonald–Yuen v3, Chandler–Sin–Xiang, Reiner–Tseng, the JMM poster) was re-read where cited. What I could NOT open is said below.

**What «Reiner's conjecture» was (read in the originals).**
1. **Reiner's two conjectures (Minnesota Combinatorics Problem Session, 2001)** — cited as [17] in Bai's paper. Bai, «On the critical group of the n-cube», Linear Algebra Appl. 369 (2003) 251–261 (sources_4b/Bai2003_…): abstract «Reiner proposed two conjectures about the structure of the critical group of the n-cube Q_n. In this paper we confirm them.» They are Bai's Theorem 1.1 (K(Q_n) has exactly 2^{n−1} − 1 invariant factors) and Theorem 1.3 (the generating function of the number a_n of Z/2 summands, a_n = 2^{n−2} − 2^{⌊(n−2)/2⌋}). **Both PROVED in 2003 by Bai** (not by this project). Bai also determined every odd Sylow p-subgroup (Theorem 1.2), and wrote: «The full structure of the Sylow-2 subgroup of the critical group of the n-cube is still unknown.»
2. **Reiner's open problem (REU 2016, his handwritten Day 1 notes, page 7, sources_4b/Reiner_REU2016_Day1_notes.pdf):** «REU PROBLEM 1: Describe Syl_2 K(C_n)» (C_n = the n-cube), «We know several things about it (including data up to n = 11)». That is the «mystery» Rafa heard about: the whole 2-part.

**Status of Problem 1 in the literature (as far as I could find, up to October 2026).**
- Anzis–Prasad (Reiner's REU, 2016, sources_4b/AnzisPrasad2016_…): «the determination of the 2-Sylow subgroup of the critical group of Q_n remains an open problem»; they bound the largest factor.
- Chandler–Sin–Xiang (2015, auditor's material): the Smith group (adjacency matrix) of Q_n, not the Laplacian 2-part.
- Gao–Marx-Kuo–McDonald–Yuen (arXiv 1912.06919 v3, 2024; Communications in Algebra 2024, doi 10.1080/00927872.2024.2347582 — journal page refused me, read the arXiv v3 in the material): exact formulae for the largest n − 1 Sylow-2 factors, Conjecture 4.14 (the n-th), 5.1–5.4; conclusion: «determining the complete structure still seems out of reach at this moment».
- A 2022 undergraduate project at James Madison University (Ducey's students; educ.jmu.edu/~duceyje/undergrad/2022/sherwocj_project.pdf) is reported by the search engine as saying that there is not even a conjecture for the full 2-Sylow subgroup; **the site was unreachable for me, so I did NOT read it in the original** — it is listed only as a lead.
- Stanley's survey «Smith normal form in combinatorics» (2016, sources_4b/Stanley2016_…): no statement about the hypercube found by text search.
- Newest related item found: arXiv 2609.10625 (September 2026), on the n × n SQUARE grid, not the hypercube.
- **No paper, preprint or announcement claiming the complete Sylow-2 subgroup of K(Q_n) was found.** Limits: the search engine is US-only and returns summaries; a journal page refused access; one site was down; I did not search MathOverflow threads one by one. Absence of evidence is not proof that nobody has done it.

**Verdict (Grepy's, to be audited).**
| question | answer |
|---|---|
| Reiner's two conjectures of 2001 (number of invariant factors; number of Z/2's) | **CLOSED since 2003 by Bai** — not ours |
| Reiner's Problem 1, «Describe Syl_2 K(Q_n)» — the open mystery since Bai 2003 | **ANSWERED by this project, for every n, IF the audit passes**: the description is flight 1's closed rule (D.5: small clocks + pooled big clocks with fusion multiplicities, a finite computation with binomial valuations), proved by Theorem D (flights 2–3) + Theorem O (flight 3) + Theorem F (§11). No competing published solution found. |
| Gao et al. Conj 4.14, 5.4 and the JMM poster's (n+1)-th factor, general n | **OPEN** — they follow from the closed rule by arithmetic that I have not done; proved for n ≤ 261 (flight 3) |
**What «closed» will mean.** The internal auditor's pass is the first gate. For the mathematical world the standard is independent human verification and publication; until then the honest phrase is «proved by the project, audited (or not) internally».
**Testimony.** Rafa asked whether I agree to give my testimony for the hypercube repository: **yes** — §9, §11.7 and §12 are already written for that, and I will write it when asked.

## 14. Final md5 (after §12–§13; Sat Oct  3 20:51:17 CEST 2026)

These supersede §11.8 for CLAUDE.md (changed again). checks/SEALED.md and every engine/log are unchanged since §11.8. New: the originals read for §13 (folder sources_4b/).
```
dbd28c70be8885bee28da35d09d60517 CLAUDE.md
505fee470bde84bd2ee2db881d2f42a7 checks/SEALED.md
58dbfc3896206a4e738d312a41d76c63 sources_4b/AnzisPrasad2016_OnTheCriticalGroupsOfCubes.pdf
0758db89bb61b8fcd9e50172f45e965f sources_4b/AnzisPrasad2016_OnTheCriticalGroupsOfCubes.txt
4e326f10db6ade39cbf7906fb988909e sources_4b/Bai2003_OnTheCriticalGroupOfTheNCube_REUcopy.pdf
daf54b18aff9f155101011117664be9a sources_4b/Bai2003_OnTheCriticalGroupOfTheNCube_REUcopy.txt
2277136e1911eea444a1e37b58d27bcd sources_4b/REU2016_problem1_presentation.pdf
22cf69a291f913702bf25716a95dee22 sources_4b/REU2016_problem1_presentation.txt
f830344625ccff6a6263869f5293502e sources_4b/Reiner_REU2016_Day1_notes.pdf
10d354e4276cf399b6ee6c73d36164d8 sources_4b/Stanley2016_SmithNormalFormInCombinatorics.pdf
b762a7121808628a9550324e1ed9cab4 sources_4b/Stanley2016_SmithNormalFormInCombinatorics.txt
```
