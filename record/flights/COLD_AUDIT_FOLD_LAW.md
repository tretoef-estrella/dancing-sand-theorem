# Cold audit of «The fold law for the sandpile group of the cube — pencil note, version 2»

Auditor and scribe: **Grepy Hypercube** (auditor of the HYPERCUBE project). The file was created empty, with its sections, on 3 October 2026 before any re-derivation or computation (disk rule). The note was written by Grepy Chats; this is the **second reading**. Every item is rewritten in my own words and marked **CORRECT**, **GAP** or **ERROR**. The gates are my own code (`engines_gh/`), written today; none of the note's engines is imported or called.

Document under audit: `notes/THE_FOLD_LAW_PENCIL_NOTE_v2.md`, md5 `1c3128903b9017d0cf93f9c5ddf025a2`.

## 0. First line (the verdict)

**On my reading every proof in the note HOLDS: §1.1, §1.2, §1.3, §1.4, §5, §6 (Theorem 6.3, Corollaries A and B) and §7.1 are CORRECT. I found no GAP and no ERROR. There are nine presentation notes, of which three (P3, P5, P6) state steps that the note leaves implicit; none changes a statement.** My gates found 0 failures in 140 checks (55 + 77 + 8), and the controls fire. The no-carry control reproduces exactly the «252 against 236» of the note.

The proved part therefore now stands on **two readings** (the writer's and mine), each with its own code:
- layers 0, 1 and 2 of the fold law (`r_{j+1}(C) = r_j(C̄)` for `j = 0, 1`);
- the closed count of the cyclic factors of order `≥ 8` of `Syl_2 K(Q_n)` for every `n` (Theorem 6.3, Corollary A);
- `N_U K ≅ K(Q_n/U)` for every subgroup `U`.

**Still open, and not touched by this reading:** the fold law from the third layer on (`j ≥ 2`), and the whole 2-part. The measured statements (§0 for `n ≤ 13`; §7.3; §8) are re-measured by me where noted in §9; they remain measurements.

**Not settled by this reading:** novelty. Bai (2003) has not been read in the original by anyone (§11).

## 1. Setting and the statement of the law (note §0) — CORRECT

`G = (Z/2)^n` and `R = Z[G]`. Put `s_i = 1 − x_i`, so that `s_i^2 = 2s_i`, and `σ = Σ s_i`; σ is the Laplacian `n − Σ x_i`. Set `C = R/σR`.

- **The free part.** The augmentation `ε` kills `σ`, so it descends to `C → Z`, which is onto. Its kernel is the augmentation ideal modulo `σ`. That kernel is finite, because `σ` is invertible over `Q` on every non-trivial character (it takes the value `2k` there). Hence `C = Z ⊕ K`, `K = ker ε`, and `K` is the sandpile group.
- **The equivalence.** «`2K ≅ K̄` on 2-parts» is the same as «`r_{j+1}(C) = r_j(C̄)` for every `j`», since `r_j(2P) = r_{j+1}(P)`.
- **The number `a_n`.** Under the law, `a_n` is the number of `Z/2` factors of `K`. It equals `r_0(C) − r_1(C) = 2^{n−1} − (2^{n−2} + 2^{n−2−⌊(n−1)/2⌋})`, and `⌈(n−1)/2⌉ − 1 = ⌊(n−2)/2⌋` gives the printed formula. Gate: FOLD `n = 3..11`, 9 of 9.

## 2. Note §1.1 — `C[2] = e_2·C` — CORRECT

In `R`, `σ^2 = Σ s_i^2 + 2e_2 = 2σ + 2e_2`, so `2e_2 = σ(σ − 2) ∈ σR`, and `e_2 ∈ C[2]`.

Conversely, let `2p = σr`. Modulo 2 the ring is `Λ = F_2[s]/(s_i^2) = ⊗_i F_2[s_i]/(s_i^2)`, and `σ` becomes `e_1 = Σ s_i`. Multiplication by `e_1` on `Λ` is exact (kernel = image). For one factor, multiplication by `s_i` on `F_2[s_i]/(s_i^2)` is exact; for the tensor product, the Künneth formula for differential modules over a field gives the same (presentation note P1).

So `r = σr' + 2r''`. Then `2p = σ^2 r' + 2σr'' = 2(σ + e_2)r' + 2σr''`, and since `R` is torsion-free, `p = e_2 r' + σ(r' + r'')`. Hence `2C ≅ C/C[2] = R/(σ, e_2)`.

Gate G1, `n = 2..8`: the 2-part of `R/(σ, e_2)` is the 2-part of `C` with every exponent lowered by one and the `Z/2`'s dropped, 7 of 7.

**Weak control, reported.** The intended control `R/(σ, e_3)` differs from `2C`, but only because it equals `C` itself at the prime 2: `e_3` already lies in `σR` there. A control that differs for a trivial reason is a weak control; the strong controls are those of §7 and §9.

## 3. Note §1.2 — the folded cube sits inside the cube — CORRECT

`(1 + a)(a − 1) = a^2 − 1 = 0`, so `r ↦ (1 + a)r` is well defined from `C̄ = R/(σ, a − 1)` to `C`.

**Injectivity.** Suppose `(1 + a)r = σs`.
- Multiply by `1 − a`: `σ·s(1 − a) = 0`.
- The kernel of multiplication by `σ` on `Z[G]` is `Z·N_G`: `σ` vanishes only on the trivial character, and `Z[G] ∩ Q N_G = Z N_G`.
- The augmentation of `s(1 − a)` is 0, and that of `N_G` is `2^n`, so `s(1 − a) = 0`.
- `Z[G]` is free over `Z[⟨a⟩]`, so `ann(1 − a) = (1 + a)R`. Hence `s = (1 + a)s'`.
- Then `(1 + a)(r − σs') = 0`, so `r − σs' ∈ ann(1 + a) = (1 − a)R`.

So `r ∈ (σ, a − 1)`.

**The torsion parts** (implicit in the note; P2). `(1 + a)c` is torsion iff `ε((1 + a)c) = 2ε(c) = 0`, iff `c ∈ K`. So `tors((1 + a)C) = (1 + a)K`, and `K̄ ≅ (1 + a)K`.

Gate G2, `n = 2..5`, by an independent route. I computed the lattice `L = {r : (1 + a)r ∈ σR}` as a kernel lattice (flint HNF) and the abelian group `R/L`. It equals `C̄` computed directly, 4 of 4.

## 4. Note §1.3 — halving — CORRECT

Modulo `σ`, `s_n = −τ` with `τ = s_1 + … + s_m`, `m = n − 1`. So `x_n = 1 + τ`, and `x_n^2 = 1` becomes `τ(τ + 2) = 0`; hence `C = R'/(τ(τ + 2))`.

**The folded cube.** `a = a'(1 + τ)` and `a'^2 = 1`, so `a − 1 = a'·f` with `f = 1 + τ − a'`. Also `f·g = (1 + τ)^2 − 1 = τ(τ + 2)`, so `C̄ = R'/(f)`.

**The doubled cube** (not written in the note; P3).
- In `R'`, `τ^2 = 2τ + 2e_2'`, so `θ := τ(τ + 2)/2 = 2τ + e_2'` lies in `R'`.
- The full `e_2(s_1, …, s_n)` becomes `e_2' + s_nτ = e_2' − τ^2 = −θ`.
- So `R/(σ, e_2) = R'/(τ(τ + 2), θ) = R'/(θ)`.

**On characters** (`k` minus signs, so `τ = 2k` and `a' = (−1)^k`): `f = 2k + 1 − (−1)^k = 4⌈k/2⌉` and `θ = 2k(k + 1)`. Both have valuation `2 + v_2(⌈k/2⌉)` for `k ≥ 1`.

**The identities** `θ = (1 + τ)f − f^2/2`, `f^2 ∈ 2R'` and `θ^2/2 = Φ_θ = 4e_1 + 14e_2 + 12e_3 + 3e_4`: `Z[G]` embeds in a product of copies of `Z`, one per character, and on characters `e_j = 2^j C(t, j)` with `t = k`, while `θ^2/2 = 2t^2(t + 1)^2`. A polynomial of degree 4 that agrees at `t = 0..4` agrees everywhere; I checked those five values by hand.

Gates G3 (`n = 2..8` against the full ring; `n` up to 11 by halving) and G3b (`m = 1..6`): all pass.

## 5. Note §1.4 — the switches and the first layer — CORRECT

**The 2-form.** Modulo 2, `Λ'` is the exterior algebra on the space of linear forms: in characteristic 2 every linear form squares to 0.
- The 2-form `e_2` has Gram matrix `J − I` over `F_2`, of rank `m` for even `m` and `m − 1` for odd `m`, i.e. `2ρ`.
- The basis `p_i = s_{2i−1} + T_i`, `q_i = s_{2i} + T_i` (and `r = s_m` for odd `m`) is symplectic: gate G4-symplectic, `m = 2..9`, checks that `Σ p_iq_i ≡ e_2` and `Σ(p_i + q_i) + r ≡ e_1`.

**The divided powers** (P4). `e_{2k} = e_k(π)` needs divided powers on the even part of the exterior algebra. They are defined over `Z`, where `Λ_Z^{ev}` is torsion-free, and then reduced.
- Written with the terms `s_is_j`, `γ_k(e_2) = (2k − 1)!!·e_{2k} ≡ e_{2k}`.
- Written with the terms `π_i`, `γ_k(e_2) = e_k(π)`.
- So `ȳ = Π(1 + π_i) = Σ_k e_{2k}`.

**The two operators.**
- `θ̄ = e_2 = Σ(y_i − 1)`.
- `a' ≡ Π(1 + s_i) = Σ_j e_j`, so `f̄ = 1 + e_1 + Σ_j e_j = Σ_{j≥2} e_j`.
- `(1 + e_1)(ȳ − 1) = Σ_{k≥1} e_{2k} + Σ_{k≥1}(2k + 1)e_{2k+1} = Σ_{j≥2} e_j`.

**The first layer.** On a block `P_S·u` with `|S| = s ≥ 1`:
- `θ̄` acts as `ε_1(π)`, which is exact on `P_S`.
- `ȳ − 1` acts as `g − 1`, with `g` an involution of the group `(Z/2)^s` whose group algebra is `P_S`; its kernel is `(1 + g)P_S`, of dimension `2^{s−1}`.
- On the blocks with `s = 0` both operators vanish.

Summing gives `2^{m−1} + 2^{m−ρ−1}` for both. Since `r_1(C) = dim (2C ⊗ F_2) = dim coker θ̄ = dim ker θ̄`, and likewise for `f`, the first layer `r_1(C) = r_0(C̄)` follows.

Gate G4, `m = 1..11` (by rank over `F_2`, with no blocks): 11 of 11.

## 6. Note §5 — the carries and the air — CORRECT

**§5.1.** `s_is_S = s_{S∪i}` if `i ∉ S`, and `2s_S` if `i ∈ S`. So `τ = U + 2D`.

**§5.2.** Expand `(U + 2D)(U + 2D + 2)` with `U^2 = 2E_2` and `DU = U(D + 1)`:
`2E_2 + 4U(D + 1) + 4D(D + 1)`.
Halving gives `E_2 + 2U(D + 1) + 4C(D + 1, 2)`.

**§5.3.** `x_is_S = −s_S` if `i ∈ S`, and `s_S − s_{S∪i}` otherwise. So `a's_S = (−1)^{|S|}·A s_S`, with `A = Π(1 − S_i) = Σ_j(−1)^jE_j`, and `a' = A∘(−1)^D`.

Gate G5: the three identities, and `U^2 = 2E_2`, `DU = U(D + 1)`, hold exactly as integer matrices, `m = 1..8`.

**§5.4 (the air).** `I^j` is spanned by the `2^c s_S` with `c + |S| ≥ j`: a product of `a` twos and `b` letters `s_i` is `2^{a+b−|S|}s_S`. So `gr R' = F_2[h][s]/(s_i^2 − hs_i)`.
- `θ = e_2 + 2e_1` exactly, so its leading form is `e_2 + he_1`.
- `f = 2e_1 − e_2 + e_3 − ⋯` has the same leading form, and `θ − f` has order `≥ 3`.
- In `A`, `e_1^2 = he_1`, so `e_1(e_1 + h) = 0`; and `τ(τ + 2) = 2θ` has order 3.

Gate G5b, `m = 2..8`.

## 7. Note §6 — Theorem 6.3, Corollaries A and B — CORRECT

**The Bockstein count (P5).** Put `M` in Smith form `U·diag(2^{a_i})·V`.
- `ker M̄` is spanned by the `V^{−1}e_i` with `a_i ≥ 1`.
- For such a vector `x`, `b(x) = U·2^{a_i−1}e_i`. Modulo 2 and modulo `M̄Λ'` (which is spanned by `Ue_j` with `a_j = 0`), this vanishes iff `a_i ≥ 2`. The map is injective on the span of the `a_i = 1`.

So `dim ker β_1 = #{a_i ≥ 2}`, counting `Z`. The value `b(x)` is independent of the lift: it changes by `My ∈ M̄Λ'`.

**6.1 (the image).**
- For `θ`, take `x = θ̄w̄` with lift `θw̃`. Then `θ·θw̃ = 2Φ_θw̃`, and `Φ_θ ≡ 3e_4 ≡ e_4` (mod 2). On a block, `e_2 = ε_1(π)` and `e_4 = ε_2(π)`, so the map is `w ↦ ε_2w` from `P_S/ε_1P_S` to itself. The dimension of its kernel equals that of its cokernel, `dim P_S/(ε_1, ε_2)`.
- For `f`, `ker f̄ = ker(ȳ − 1)` because `1 + e_1` is a unit, and `f̄Λ' = (ȳ − 1)Λ'`. `β(f̄w) = Φ_fw ≡ (1 + e_1)f̄w + e_2w ≡ e_2w`. So the map is `w ↦ ε_1(π)w` on `P_S/(ȳ − 1)`, with kernel of dimension `dim P_S/(ε_1, ȳ − 1)`.

**The identification behind it (P6).** On a block, `e_2 ↔ ε_1` and `e_4 ↔ ε_2`. The note says it only through «`ε_k` the elementary symmetric functions of the `π_i`»; I misread it on a first pass, so it should be written out.

**Elimination of one π.** `π_s ↦ Σ_{i<s}π_i` (characteristic 2, and the square vanishes automatically).
- `ε_2 ↦ ε_2' + ε_1'^2 = ε_2'`.
- `Π(1 + π_i) ↦ (1 + ε_1')Σε_j' = Σ_{j even}ε_j'`, so `ȳ − 1 ↦ ε_2' + ε_4' + ⋯`.
- This differs from `f̄` one level down by the unit `1 + e_1`, so it has the same kernel.

Both dimensions are `κ(s − 1)` by §1.4. Gate G6-block, `s = 1..9`, both quotients equal `κ(s − 1)`.

**6.2 (`H̃`).** Take `x ∈ H̃` homogeneous of degree `d`. The lift is homogeneous in the `s`-basis: the change of coordinates is linear, so the degrees agree (P7).
- `b_θ(x) = (E_2x̃)/2 + (d + 1)Ux̃ + 2(⋯)`. Here `E_2x̃ ≡ e_2x = 0`, so the first term is integral.
- For `f`, both parities of `d` give `b_f(x) = (d + 1)e_1x + Σ_{j≥2}(±E_jx̃)/2`. Each `E_jx̃ ≡ e_jx = 0` for `j ≥ 2`: `e_{2k} = e_k(π)` and `e_{2k+1} = e_1e_{2k}` both kill `H̃`. I checked both parities by hand.
- The terms of degree `≥ d + 2 ≥ ρ + 2` have no component in `H̃`, which lives in degrees `ρ` and `ρ + 1` and is a sum of blocks spanned by monomials.
- `(p_i + q_i)x` lies in the block `{i}`, and `rx` stays in `H̃`.

So the component in `H̃` is `(d + 1)rx`. Its rank on `H̃` is `2^ρ` exactly when `m` is odd and `ρ` is even, i.e. `m ≡ 1 (mod 4)`.

**6.3 (assembly).** `M̄Λ'` is a sum of blocks (`e_2Λ'` and `(ȳ − 1)Λ'` are), so `Λ'/M̄Λ'` splits over the blocks.
- `β(image)` lies in the summands with `S ≠ ∅`.
- `β(H̃)` lies in the `H̃` summand, on which `M̄` is zero.

So the kernel of `β` on `image ⊕ H̃` is the direct sum of the two kernels. This gives the stated sum. The closed form agrees with the sum for `m = 1..60` (exact rationals).

**Gate G6.** `dim ker β_1` was computed by plain linear algebra over `F_2`, with no blocks and no Smith form, for `θ` and for `f`, `m = 1..11`: the sum and the closed form agree, 11 of 11. Against the Smith count, `n = 2..11`: 10 of 10.

**Control, which fires exactly.** With the carry removed (`θ_0 = e_2'`):
- `20 ≠ 16` at `m = 5` and `252 ≠ 236` at `m = 9`; it agrees elsewhere, as predicted.
- The no-carry values equal the formula without the correction term.

**Corollaries.** A (the table `n = 8..16`) and B follow, with `Z` counted once. The table is reproduced exactly from the closed form.

## 8. Note §7–§8 — the wound, the general fold law, the profiles

**§7.1 `N_U K ≅ K(Q_n/U)` — CORRECT.**
- `N_U(u − 1) = 0`, so `R/(σ, I_U) → C`, `r ↦ N_Ur`, is well defined.
- If `N_Ur = σs`, then `σs(1 − u) = 0`, so `s(1 − u) = 0` for every `u ∈ U` (as in §3), and `s ∈ ann(I_U) = N_UR`.
- Then `N_U(r − σs') = 0`, so `r − σs' ∈ ann(N_U) = I_UR`.
- Torsion: `ε(N_Uc) = |U|ε(c)`.
- `R/(σ, I_U)` is the critical module of the Cayley multigraph of `G/U` (loops contribute 0).

Gate G7, by an independent route: `R/L_U` with `L_U = {r : N_Ur ∈ σR}` (HNF), against the Laplacian of the quotient graph built as a graph. It holds for every subgroup `U`, `n = 2..5` (5, 16, 67, 374 subgroups), with 0 mismatches.

**§7.2:** CORRECT (one line).

**§7.3 (measured claim) — re-measured.** I counted pairs `(U, U + ⟨u⟩)`.
- `u ≡ a mod U`, groups not both trivial: `1, 7, 43, 291` pairs for `n = 2..5`, all doubling.
- Converse cases: `0, 0, 3, 15`.
- Every row of the note's `herida.log` is reproduced for `n = 2..5`.

Sealed before the run (`logs/gh_prediccion_sellada_G7_G8.md`, md5 `b82d9e01…`). **Two counting errors of mine**, found before writing this: I first counted elements `u` instead of pairs, then took «both trivial» to refer to `K(Q/U)` instead of the two groups compared. Both runs are kept in the bitácora. `n = 6` was not re-run.

**§8 (profiles):** measured in the note; not re-measured by me.

## 9. Gates of my own (code, logs, controls)

Code (`engines_gh/`; md5): `gh_ring.py` `6862c9bb…` (the ring in the basis `s_S`, a 2-adic Smith form modulo `2^30` in int64, kernels over `F_2`); `gh_gates.py` `ad0420e7…`; `gh_gates2.py` `4700e46f…`; `gh_gates3.py` `9a6f4e43…`.

| log | content | result | md5 |
|---|---|---|---|
| `logs/gh_gates_part1.log` | G1, G1b, route 2 (flint SNF), G2 (HNF), G3, G3b, FOLD `n = 3..11` | 55 PASS, 8 s, 118 MB | `5029d230…` |
| `logs/gh_gates_part2a.log` | G4, G4-symplectic, G5, G5b, G6-block, G6 + control, G6b, Corollary A, sum = closed | 77 PASS, 8 s, 316 MB | `17976637…` |
| `logs/gh_gates_part3.log` | G7, G8 | 8 PASS, 11 s, 33 MB | `de78849d…` |

**Independent routes:**
- 2-adic Smith (mine) against flint SNF, `n ≤ 5`;
- kernel lattices by HNF for §1.2 and §7.1;
- the Bockstein by plain linear algebra over `F_2`, against Smith counts and against the block formula;
- the quotient graph built as a graph, for §7.1.

**My `n = 9, 10, 11` cube** agrees with the published Table 1 of arXiv:1912.06919 as quoted in `notes/RETOS_AL_ALCANCE_v1.md`.

**My errors:** run 1 of part 1 was killed by the watchdog at 1.26 GB (flint SNF on a 64 × 128 non-square matrix, against my estimate of < 400 MB); plus the two counting errors of §8.

## 10. Metaphors (Rafa's order: constant metaphors of the problems)

| the problem | the metaphor | what it suggests to measure or prove |
|---|---|---|
| the cube's group, a building of `2^m` rooms in `m + 1` floors (height `D`) | **the lift `U` and the stairs**: modulo 2 only the lift is seen (one floor up); the carry is the floor number itself (`τ = U + 2D`) | the next layer needs the **floor number modulo 4**, `C(D + 1, 2)`: the second binary digit of the height |
| the blocks `P_S·u` | **apartments**: inside each one the switches `π_i` of its rooms are on or off; the lift moves people, but at layer 2 nobody changes apartment except through the one leftover door `r` (odd `m`) | at layer 3, `U(D + 1)` starts **moving furniture between apartments**; measure how much it moves (the rank of the off-diagonal part between blocks) |
| the induction of §6 | **Russian dolls (matrioskas)**: inside an apartment with `s` switches on lives the whole problem of layer 1 with `s − 1` switches | the guess for layer `j`: apartment with `s` switches → layer `j − 1` with fewer switches; to be sealed and tested |
| `H̃`, the rooms with every switch off | **the cellar**: only the carry reaches it, and only when `m ≡ 1 (mod 4)` (one door, even floor) | at layer 3, list which cellar rooms are reached by the second carry `C(D + 1, 2)` |
| the fold `Q_n → Q_n/⟨a⟩` | **a mirror**: each corner meets its opposite; «se van turnando» | the staircase of folds (§7.3): each further fold by the long diagonal halves the clocks |

## 11. What is not covered by this reading, and what is owed

1. **Bai (2003) in the original** (*Linear Algebra Appl.* 369, 251–261). Not in `sources/`; it is needed before any claim of novelty for Theorem 6.3 or for the fold law. **Rafa: if you can get the PDF, put it in `HYPERCUBE/sources/`.**
2. **The papers citing arXiv:1912.06919 (2024 and later)**, not looked at.
3. **Layers `j ≥ 2` of the fold law:** open, the next target.
4. **Presentation notes for a v3 of the note**, not changes of substance:
   - **P1** the exactness of `e_1` on `Λ` (Künneth);
   - **P2** torsion of `(1 + a)C`;
   - **P3** `e_2 ↦ −θ` in §1.3;
   - **P4** divided powers defined over `Z`;
   - **P5** the Bockstein–Smith lemma;
   - **P6** the identification `e_2 ↔ ε_1`, `e_4 ↔ ε_2` on blocks, and for `f` that the map is `w ↦ ε_1w` on `P_S/(ȳ − 1)`;
   - **P7** degree is preserved by the change of coordinates, and each `E_jx̃` is even for `j ≥ 2`;
   - **P8** the weak control of G1 (`e_3 ∈ σR` 2-adically);
   - **P9** Corollary A is about `Syl_2` only.

— Grepy Hypercube, 3 October 2026
