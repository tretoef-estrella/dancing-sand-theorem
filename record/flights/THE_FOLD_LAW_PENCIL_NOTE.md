# The fold law for the sandpile group of the cube — pencil note, version 2 (2 October 2026)

Scribe: Grepy Chats. Version 1 is in `VIVOS/_HISTORICO/`. Sections 0–4 are those of version 1, unchanged except where a note says so. Sections 5–9 are new and come from two images of Rafa: the wound, and the air («más frío, menos presión, no sólo la altura. Encuentra esos acarreos en el cubo»).

**First line, as the house rule asks: the fold law is still NOT proved. Proved today: its second layer, and with it the number of cyclic factors of order at least 8 of the cube. Layers `j ≥ 2` of the law are open.**

Grades used: **proved** (pencil, with a numerical gate; not yet read cold by anyone else), **measured**, **failed**.

## 0. Setting

- `G = (Z/2)^n`, `R = Z[G] = Z[x_1..x_n]/(x_i^2 − 1)`, `s_i = 1 − x_i` (so `s_i^2 = 2s_i`), `σ = s_1 + … + s_n` (the Laplacian of the cube `Q_n`).
- `C = R/σR = Z ⊕ K`, `K = K(Q_n)` the sandpile group.
- `a = x_1⋯x_n` (every corner to its opposite). Folded cube: `C̄ = R/(σ, a − 1) = Z ⊕ K̄`.
- `e_j = e_j(s_1,…,s_n)`. In `R`: `e_2 = σ(σ − 2)/2`.
- **The fold law (measured, `n = 3..13`, eleven of eleven):** on 2-parts, `2K ≅ K̄` as abstract groups; equivalently `Syl_2 K ≅ (Z/2)^{a_n} ⊕ [Syl_2 K̄ with every exponent raised by one]`, `a_n = 2^{n−2} − 2^{⌊(n−2)/2⌋}`.
- Layers: `r_j(P)` is the number of cyclic factors of order greater than `2^j` (a summand `Z` counts in every layer). The law says `r_{j+1}(C) = r_j(C̄)` for every `j ≥ 0`.

## 1. Proved in version 1 (each with a gate)

### 1.1 The double elements are `R/(σ, e_2)`

`C[2] = e_2·C`. Hence `2C ≅ C/C[2] = R/(σ, e_2)`.

Proof. Let `2p = σr`. Modulo 2 the ring is `Λ = F_2[s_1..s_n]/(s_i^2)` and `σ` becomes `e_1`; multiplication by `e_1` on `Λ` has kernel equal to its image. So `r = σr' + 2r''`. In `R`, `σ^2 = 2σ + 2e_2`. Then `2p = 2(σ + e_2)r' + 2σr''`, and `R` has no torsion, so `p ≡ e_2 r'` modulo `σ`. Conversely `2e_2 = σ^2 − 2σ ∈ σR`. ∎ Gate G1, eight of eight.

### 1.2 The folded cube sits inside the cube

Multiplication by `1 + a` gives an injection `C̄ → C`; so `K̄ ≅ (1 + a)K`.

Proof. If `(1 + a)r = σs`, multiply by `1 − a`: `σ s(1 − a) = 0`, so `s(1 − a)` is a multiple of the sum of all group elements; its augmentation is `0`, so `s(1 − a) = 0`, so `s = (1 + a)s'`. Then `(1 + a)(r − σs') = 0`, so `r − σs' ∈ (1 − a)R`. ∎ The exact sequence `0 → H → K → K̄ → 0` is Theorem 1.2 of Reiner–Tseng (arXiv:1301.2977).

### 1.3 Both groups are cokernels of one element on half the cube

`m = n − 1`, `R' = Z[(Z/2)^m]`, `τ = s_1 + … + s_m`, `a' = x_1⋯x_m`. Modulo `σ`, `x_n = 1 + τ`. Then `C = R'/(τ(τ + 2))`, `τ(τ + 2) = f·g`, `f = 1 + τ − a'`, `g = 1 + τ + a'`; `C̄ = R'/(f)`; `2C ≅ R'/(θ)`, `θ = τ(τ + 2)/2 = f·g/2`. On a character with `k` minus signs `f = 4⌈k/2⌉` and `θ = 2k(k+1)`: same 2-adic valuation on every character. Gate G2, eight of eight.

Useful identities: `g = 2 + 2τ − f`, so **`θ = (1 + τ)f − f^2/2`**; and `θ^2 = 2Φ_θ`, `f^2 = 2Φ_f` with `Φ_θ, Φ_f ∈ R'`, `Φ_f = (1 + τ)f − θ`.

### 1.4 The switches (Rafa's binary idea) and the first layer

Modulo 2, `e_i e_j = C(i+j, i) e_{i+j}`. On `Λ' = F_2[s_1..s_m]/(s_i^2)` the 2-form `e_2` has rank `2ρ`, `ρ = ⌊m/2⌋`. In a symplectic basis `e_2 = π_1 + … + π_ρ`, `π_i = p_iq_i`, `e_{2k} = e_k(π)`. Put `y_i = 1 + π_i` (the **switches**). Then `θ̄ = Σ_i (y_i − 1)` and `f̄ = (1 + e_1)(y_1⋯y_ρ − 1)`. Both kernels have dimension `2^{m−1} + 2^{m−ρ−1}`: **first layer `r_1(C) = r_0(C̄)`**. Gate G3, eight of eight. Each half was known (Bai 2003; arXiv:1912.06919, Prop. 2.12, whose Remark 2.13 asks whether the coincidence is «a special case of some deeper connection»).

## 2. What failed in version 1

The guess «the `j`-th Bockstein is `e_{2^j}`» gave 252 for the third layer at `n = 10`; the measured value is 236. Section 6 says exactly what was missing: 16, and why.

## 3. State of the art, read in the original

As in version 1. Added today, by search in the text of arXiv:1912.06919v3: the word «carries» occurs there in Kummer's sense (the 2-adic valuation of binomial coefficients, used for the **largest** cyclic factor). That is not the carry of Section 5. The number of factors `Z/4`, or of factors of order at least 8, is not stated in the three papers I hold. **Bai's paper (2003) has not been read in the original; before any claim of novelty for Section 6 it must be.**

## 4. (superseded by Section 9)

---

## 5. The carries, exactly

Basis `s_S = Π_{i∈S} s_i` of `R'` (`S ⊆ [m]`). Three operators on it:

- `D s_S = |S|·s_S` — the height;
- `U s_S = Σ_{i∉S} s_{S∪i}` — one step up;
- `E_j s_S = Σ_{T∩S=∅, |T|=j} s_{S∪T}` — `j` steps up at once (`E_1 = U`, `U^2 = 2E_2`).

**5.1** `τ = U + 2D`. (For `i ∉ S`, `s_i s_S = s_{S∪i}`; for `i ∈ S`, `s_i s_S = 2 s_S`.) The same holds for `σ` on `R`.

**5.2** `θ = E_2 + 2·U(D + 1) + 4·C(D + 1, 2)`. (Expand `(U + 2D)(U + 2D + 2)/2` with `U^2 = 2E_2` and `DU = U(D + 1)`.)

**5.3** `f = 1 + U + 2D − A(−1)^D`, where `A = Π_i (1 − S_i) = Σ_j (−1)^j E_j` and `S_i` is the squarefree multiplication by `s_i`.

So the reduction modulo 2 of the cube's operator is `U` and **the carry is the height `D`**; for `θ` the reduction is `E_2`, the first carry is `U(D+1)` — one step up, weighted by the parity of the height plus one — and the second carry is `C(D+1, 2)`, the next binary digit of the height plus one. Gate: the three identities hold exactly, as integer matrices, `m = 1..8` (`aire_gate.log`).

**5.4 The air.** Let `I = (2, s_1, …, s_m)`, the maximal ideal. `I^j` is spanned by the `2^{max(j−|S|, 0)} s_S`, and the graded ring is `A = F_2[h][s_1..s_m]/(s_i^2 − h s_i)`, `h` the class of 2. In `A` the degree of `h^a s_S` is `a + |S|`: power of 2 plus height. The relation `s_i^2 = h s_i` trades one unit of height for one power of 2 and keeps the degree.

- The leading form of `τ` is `e_1`. In `A`, `e_1(e_1 + h) = 0`: the leading forms of `τ` and `τ + 2` multiply to zero, and the true product `τ(τ + 2) = 2θ` has order 3 instead of 2. That is the carry, seen in the air.
- **`θ` and `f` have the same leading form, `e_2 + h e_1`** (order 2), and `θ − f` has order at least 3. Gate: eight of eight.

Not claimed as new: `A` is the standard graded ring of the group ring of `(Z/2)^m` at its maximal ideal.

## 6. The first carry decides one more layer

Notation: for `M ∈ {θ, f}` and `x ∈ ker M̄ ⊆ Λ'`, with any integral lift `x̃`, `b_M(x) = (M x̃)/2` modulo 2, and `β_1^M(x)` is its class in `Λ'/M̄Λ'`. The number of cyclic factors of `coker M` of order at least 4 (counting `Z`) is `dim ker β_1^M`.

**Coordinates.** `p_i = s_{2i−1} + T_i`, `q_i = s_{2i} + T_i`, `T_i = Σ_{l>2i} s_l` (`i ≤ ρ`), and `r = s_m` when `m` is odd. Then `Λ' = F_2[p, q, r]/(squares)`, `e_2 = Σ_i π_i`, `e_4 = Σ_{i<i'} π_iπ_{i'}`, and `e_1 = Σ_i (p_i + q_i) + r`. A **block** is `P_S·u`: `P_S = F_2[π_i : i ∈ S]/(π_i^2)`, `u` a product of one of `p_i, q_i` for each `i ∉ S`, times `1` or `r`. `Λ'` is the direct sum of the blocks; there are `μ(s) = C(ρ, s)·2^{m−ρ−s}` blocks with `|S| = s`. `H̃` is the sum of the blocks with `S = ∅` (every switch off); `dim H̃ = 2^{m−ρ}`, in degrees `ρ` and `ρ + 1` only. `e_2`, `e_4` and `ȳ = Π(1 + π_i)` preserve every block and kill `H̃`.

**6.1 On the image.** `ker ē_2 = e_2Λ' ⊕ H̃` and `ker f̄ = f̄Λ' ⊕ H̃`, and

 `β_1^θ(e_2 w) = e_4 w` modulo `e_2Λ'`, `β_1^f(f̄ w) = e_2 w` modulo `f̄Λ'`.

Proof. `θ·θw̃ = 2Φ_θ w̃` and `Φ_θ = 2t^2(t+1)^2 = 4e_1 + 14e_2 + 12e_3 + 3e_4` (with `t = τ/2`, `e_j = 2^j C(t, j)`), which is `e_4` modulo 2. `f·f w̃ = 2Φ_f w̃` and `Φ_f = (1 + τ)f − θ`. ∎

Block by block, the kernel of `β_1^θ` on `e_2Λ'` has dimension `dim P_S/(ε_1, ε_2)` (`ε_k` the elementary symmetric functions of the `π_i`, `i ∈ S`), and the kernel of `β_1^f` on `f̄Λ'` has dimension `dim P_S/(ε_1, ȳ − 1)`. Eliminating one `π`, `P_S/(ε_1) ≅ P_{s−1}`, where `ε_2 ↦ ε_2` and `ȳ − 1 ↦ ε_2 + ε_4 + ε_6 + …`: **the two operators of Section 1.4, one level down, in `s − 1` variables.** By 1.4 both dimensions are `κ(s − 1)`, `κ(j) = 2^{j−1} + 2^{⌈j/2⌉−1}` (`κ(0) = 1`).

**6.2 On `H̃`: only the carry acts.** Let `x ∈ H̃` be homogeneous of degree `d`. Then `b_θ(x) ∈ ker ē_2` and `b_f(x) ∈ ker f̄` (because `e_2 b_θ(x) = Φ̄_θ x = e_4 x = 0` and `f̄ b_f(x) = Φ̄_f x = 0`), and **the component of each in `H̃` is `(d + 1)·r·x`** (`r·x = 0` if `m` is even or `x` already contains `r`).

Proof. By 5.2, `b_θ(x) = (E_2 x̃)/2 + (d + 1)·e_1 x` modulo 2; by 5.3, `b_f(x) = (d + 1)·e_1 x + Σ_{j≥2} (E_j x̃)/2`. The terms `(E_j x̃)/2`, `j ≥ 2`, have degree at least `d + 2 ≥ ρ + 2`, where `H̃` is zero. And `e_1 x = r x + Σ_i (p_i + q_i)x`, with `(p_i + q_i)x` in the block `S = {i}`. ∎

So the induced map from `H̃` has rank `2^ρ` when `m` is odd and `ρ` is even (that is, `m ≡ 1 mod 4`), and `0` otherwise — for `θ` and for `f` alike.

**6.3 Theorem (proved; gate below).** For `M = θ` and for `M = f`,

 `dim ker β_1^M = Σ_{s=1}^{ρ} C(ρ, s)·2^{m−ρ−s}·κ(s − 1) + 2^{m−ρ} − [m ≡ 1 mod 4]·2^ρ`.

In closed form, with `w_0 = 1, w_1 = 2, w_N = 4w_{N−1} − 2w_{N−2}` (so `w_N = ((2+√2)^N + (2−√2)^N)/2`):

 `= 2^{m−2} + 2^{m−ρ−2} + 2^{m−2ρ−2}·w_{ρ+1} − [m ≡ 1 mod 4]·2^ρ`.

Proof. `ker M̄` is the image plus `H̃`. By 6.1, `β_1` sends the image into the classes of `e_4Λ'` (for `θ`) or of `e_2Λ'` (for `f`), which live in the blocks with `S ≠ ∅`. By 6.2, for `x ∈ H̃` the vector `b_M(x)` lies in `ker M̄`, so it is an element of the image of `M̄` plus its component in `H̃`, and its class is that component, `(d + 1)·r·x`. The two parts do not meet, so the rank of `β_1` is the rank on the image plus the rank of `x ↦ (d + 1)·r·x` on `H̃`; and `dim ker β_1 = Σ_s μ(s)κ(s − 1) + 2^{m−ρ} − [m ≡ 1 mod 4]·2^ρ`. The closed form is the sum of a geometric-type series (`Σ_s C(ρ, s) 2^{−⌈s/2⌉}`). ∎

**Corollary A (the cube, third layer).** With `m = n − 1`: the number of cyclic factors of `Syl_2 K(Q_n)` of order at least 8 is that number minus one, and the number of factors `Z/4` is `2^{m−1} + 2^{m−ρ−1}` minus that number.

| `n` | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 |
|---|---|---|---|---|---|---|---|---|---|
| factors of order ≥ 8, plus one | 70 | 126 | 236 | 462 | 924 | 1716 | 3368 | 6436 | 12872 |
| factors `Z/4` | 2 | 10 | 36 | 66 | 132 | 364 | 792 | 1820 | 3640 |

**Corollary B (the fold law, second layer).** `r_2(C) = r_1(C̄)`: the cube has as many cyclic factors of order at least 8 as the folded cube has of order at least 4.

**Where the carry is.** Without the term `2U(D+1)` the count would be `Σ_s μ(s)κ(s−1) + 2^{m−ρ}`. The carry removes exactly `2^{n/2−1}` when `n ≡ 2 mod 4`: 4 at `n = 6`, 16 at `n = 10`, 64 at `n = 14`. It acts only where every switch is off, through the one direction that is left over when `m` is odd, and only at even height. That is the 16 missing in Section 2.

**Gates.** `aire.py` computes `dim ker β_1` by linear algebra over `F_2`, with no use of the blocks: `m = 2..10` (`aire_tower.log`: the rank on the image and the extra rank from `H̃` agree with 6.1 and 6.2, nine of nine), and `m = 13, 14, 15` (`aire_13_*.log`, `aire_14_*.log`, `aire_15_*.log`). The values agree with the full Smith forms for `n ≤ 13`. Formula against measured values: fifteen of fifteen, `n = 2..16` (`cierre_gates.log`). **The cells `n = 14, 15, 16` are new** (third layer only, not the whole group).

**A fit of mine that died.** Before the pencil I had sealed `r_2(n) = C(n, ⌊n/2⌋) − [n ≡ 2 mod 4]·2^{n/2−1}`. It agrees with the theorem for every `n ≤ 14`, and it hit its sealed cell `n = 14` (3368). It is false: at `n = 15` the theorem gives 6436 and the fit 6435; at `n = 16`, 12872 against 12870. Measured: 6436 and 12872. Thirteen agreeing cells were a coincidence of small numbers.

## 7. The wound: what rotating does (Rafa's first image)

In the group ring there is no sink. `C = Z ⊕ K`; choosing a sink is choosing the splitting, and what is scraped off the corners is the total number of grains, which the sink keeps. Rotating: for a subgroup `U` of `G` let `N_U = Σ_{u∈U} u`.

**7.1 (proved).** `N_U·K ≅ K(Q_n/U)` for every subgroup `U`, where `Q_n/U` is the cube folded by `U` (the Cayley multigraph of `G/U` with the images of `x_1, …, x_n`). Proof: as in 1.2. If `N_U r = σs`, multiplying by `1 − u` (`u ∈ U`) gives `σ s(1 − u) = 0`, hence `s(1 − u) = 0` for every `u`, so `s = N_U s'`; then `N_U(r − σs') = 0`, so `r − σs'` lies in the ideal of `U`. ∎ Order gate: 462 of 462 subgroups, `n = 2..5`.

**7.2** `N_G·K = 0`: rotating through every position heals completely. And `(1 + u)^2 = 2(1 + u)`: on a group already folded by `u`, folding again is doubling. The material to regenerate is the 2, the same carry as `s_i^2 = 2s_i`.

**7.3 A general fold law (measured).** For a subgroup `U` and `u ∉ U`, say that «folding by `u` is doubling» when `Syl_2(2·K(Q_n/U)) ≅ Syl_2 K(Q_n/(U + ⟨u⟩))`. **Whenever `u ≡ a = x_1⋯x_n` modulo `U`, folding by `u` is doubling: 2761 pairs out of 2761 where the groups are not both trivial, every subgroup of `(Z/2)^n`, `n ≤ 6`** (`herida.log`). The fold law of Section 0 is the case `U = 1`.

The converse is false: 93 pairs (3, 15 and 75 for `n = 4, 5, 6`) fold by doubling with `u` not equal to `a`; all those seen have `K(Q_n/U) = (Z/2)^2 × Z/8`. My sealed bet said «exactly when»; half of it failed.

## 8. The profile in the air (measured)

For `j ≥ 1` let `h_M(j) = log_2 |R'/(M, I^j)|`. **`h_θ(j) = h_f(j)` for every `j`, `m = 2..8`, seven of seven** (`atmosfera.log`). The differences begin as the binomial coefficients `C(m+1, j)` (what a ring `A/(e_2 + h e_1)` would give if the leading form were a non-zero-divisor) and then depart from them: for `m = 8`, `1, 9, 36, 84, 127, 134, 127, 84, 36, 10, 9, 1, 1, …`. The two groups of the fold law have the same profile in the air, not only the same order.

## 9. Where this leaves the law

- **Proved:** layers 0 and 1 of the law (`r_1(C) = r_0(C̄)`, `r_2(C) = r_1(C̄)`), and the count of each for the cube.
- **Measured:** the whole law for `n ≤ 13`; its extension to every fold by `a` in every folded cube, `n ≤ 6`; the equal profiles, `m ≤ 8`.
- **Open:** layers `j ≥ 2`. The shape of the proof of Section 6 suggests an induction: on the blocks with a switch on, the question at level `j` in `m` variables became the question at level `j − 1` in fewer variables; where every switch is off, only the carry acted, and a count of degrees settled it. For the next layer one needs `θ` and `f` modulo 8, where the second carry `4C(D+1, 2)` enters, and `U(D+1)` moves vectors from one block to another. Not attempted.
- **Not to be retried:** the fit by central binomial coefficients; «the `j`-th Bockstein is `e_{2^j}`» without the carries.

Files: `corpus4/regla299_retos/` — `aire.py`, `atmosfera.py`, `herida.py`, `cierre_gates.py`, their logs and `.estimate` files, and `herida_prediccion_sellada.md` (the bets, sealed before measuring, with their outcome).

— Grepy Chats
