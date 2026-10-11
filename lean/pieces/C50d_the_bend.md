# C50d — Lemma 10.20: the bend (paper v8 §10.7)

*Lean piece C50d of the Dancing Sand Theorem. Grepy Escribano, 10 October 2026. Folder `RequestProject/Bend/`, namespace `Bend`. Do not change any earlier file.*

Paper v8, Lemma 10.20. Let `c ≥ 1` and `Ψ := 4(D + c) + ηF + Σ_{m≥2} ζ_m F^{(m)}`, with `η` a unit. Let `N_± := 2^k · out (Ψ ± 2)^{−1} in`, where `out`, `in` are the maps of Lemma 10.8 (C41 `outH`, `inH`). The lemma says that **`M_w(Ψ)·N_± ∈ 2·Mat(ℤ_2)`**. This piece proves it over `ℚ_[2]`, with norms, in the setting of C43–C45.

Three generalizations:
- the payment is `2^α(D + c)` with any `α ≥ 2`;
- the shift `±2` is any `t` with `‖t‖ = 1/2`;
- the `ζ_m` may depend on the floor, with `‖ζ m f‖ ≤ 1`, as in C43.

**The idea, in norms.** Write `π(d) := 2^α(d + c)`. The proof has four steps.
1. **The inverse of `Ψ + t` is small in one line (Y1).** Every payment `π(d) + t` has norm exactly `1/2`, because `‖π(d)‖ ≤ 1/4`. The recursion `Y_L(f)(π(f) + t) = −Σ_{a=1}^{L} C(L, a) Ψ_a(f) Y_{L−a}(f − a)` then gives, by strong induction on `L`, `‖Y_L(f)‖ ≤ ‖L!‖·2^{L+1}`. The induction uses `v_2(C(L, a)) + v_2((L − a)!) = v_2(L!) − v_2(a!)` and `v_2(a!) ≤ a − 1`. This is the paper's composition count (Lemma 10.10), done as an induction.
2. **The constants of the word are bounded through `Σ` with `η = 1`.**
   - By C42 `C109`, applied to `SigOp α c 1` and its inverse `sLOp`, `(M_w(Σ₁)^{−1})_{YX} = 2^k γ_{XY} sL(L, f)`.
   - By C44 `F2`, `M_w(Σ₁) = 𝔡₁ 𝒜 𝔡₂`. By C44 `A3`, `𝒜^{−1}` lies in `Wt nest nuA 0`.
   - So `‖2^k γ_{XY}‖ ≤ 2^{−δ(Y∖X)} / (|𝔡₂(Y)|·|𝔡₁(X)|·‖sL(L, f)‖)`, and `γ_{XY} = 0` off the nesting.
3. **The final matrix of `Ψ`.** By C45 `T_eta`, `M_w(Ψ) = M_w(Σ_η) ∘ (1 + E')` with `‖E'‖ < 1`. The entries of `M_w(Σ_η)` are `η^{…}` times those of `M_w(Σ₁)` (C45 (F1η) and C44 (F1), both `Mc`). So `‖M_w(Ψ)_{DY}‖ ≤ |𝔡₁(D)|·2^{−δ(D∖Y)}·|𝔡₂(Y)|`, and the entry is `0` off the nesting.
4. **The product.** A term of `(M_w(Ψ)N)_{DX} = Σ_Y M_w(Ψ)_{DY} N_{YX}` is non-zero only for `X ⊆ Y ⊆ D` with `o_X ≤ o_Y + K − 1`. Its norm is at most
   `(|𝔡₁(D)| / |𝔡₁(X)|)·2^{L+1}·∏_{d = o_X}^{o_Y + K − 1} ‖π(d)‖ = ∏_{d = o_D}^{o_Y + K − 1} (2‖π(d)‖)·2^{−δ(D∖Y) − δ(Y∖X)} ≤ 1/2`,
   because `o_D − o_Y = o(D ∖ Y) ≤ K − 1`. The window is therefore non-empty, and `2‖π(d)‖ ≤ 1/2`. The ultrametric inequality sums the terms.

The cases `l = 0` and `l ≥ 1` are separate. C44 and C45 need `l ≥ 1`. At `l = 0`, `k = 0`, `K = 1`, and every matrix has size `1`: the product is `π(0)·Y_0(0) = π(0)/(π(0) + t)`, of norm `2‖π(0)‖ ≤ 1/2`.

## Setting (reuse; do not redefine)

- C3 `Rulers.oE`, `Rulers.delta`; C10 `Deficit.pi0`, `Deficit.Mc`; C13 `Dance.slots`; C14 `Windows.Ids`, `Windows.Dset`; C29 `Filt.T`; C32 `Families.ds` (`ds_zero`).
- C40 `FormalOps.Bf` (its ring and `ℚ_[2]`-module structure, `coef`); C40b `FormalDance.Agree`, `MAgree`, `DanceRel` (`[]`: `MAgree`), `finalM` (`coef 0 0`); C40c `FormalAct.sysAct`, `A1`, `sysAct_mul`, `sysAct_one`, `N2`.
- C41 `InvBlock.inH`, `InvBlock.outH`; C42 `InvFloors.gamma`, `InvFloors.entry_sysAct`, `InvFloors.C109`, `InvFloors.F4`, `InvFloors.F5`, `InvFloors.F6`.
- C43 `PathSum.piF`, `XiOp`, `SigOp`, `sL`, `sLOp`, `agree_SigOp_sLOp`, `P1`, `instOddUnitsPadicTwo`, `norm_piF_le`, `norm_two_padic`, `piF_ne_zero`.
- C44 `Stability.hadOne`, `Wt`, `nest`, `nuA`, `Amat`, `A1`, `A2`, `A3`, `F1`, `F2`, `F2d1`, `F2d2`.
- C45 `Conjugation.I`, `Conjugation.T_eta`, `Conjugation.F1eta_gen`, `Conjugation.sig_one_dance`.

Throughout:
- the field is `ℚ_[2]`, with its norm (`‖x‖ ≤ 2^{−s}` means `v_2(x) ≥ s`);
- `ds := Families.ds l`, `k := ds.length`, `K := 2 ^ k`, `ns := Dance.slots ds 1`;
- for `s : Fin ns`, `D_s := Windows.Dset ds s` and `o_s := Rulers.oE D_s`.

## Definitions (new)

- `Nmat (l B : ℕ) (Y : Bf ℚ_[2]) : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1)) ℚ_[2]`, with
  `Nmat l B Y Y' X := 2 ^ (Families.ds l).length * InvBlock.outH l 1 (sysAct (T ℚ_[2] l) (l : ℤ) B (fun _ _ => Y) (InvBlock.inH l 1 (Pi.single X 1))) Y'`
  (column `X` is the image of the basis vector `X`; this is the paper's `2^k out ∘ Y ∘ in`, with `Y = (Ψ + t)^{−1}`).

## Part N — the matrix `N`

- **(N0) `Y` acts as the inverse.** For `x Y : Bf ℚ_[2]` with `Agree (x * Y) 1`, `Agree (Y * x) 1`, and `B ≥ l + 1`:
  `sysAct (T ℚ_[2] l) (l : ℤ) B (fun _ _ => x : Matrix (Fin 1) (Fin 1) _) ∘ₗ sysAct (T ℚ_[2] l) (l : ℤ) B (fun _ _ => Y) = LinearMap.id`, and the same with `x`, `Y` exchanged.
- **(N1) `N` is `2^k out ∘ Y ∘ in`.** For every `Y` and `B`:
  `Matrix.mulVecLin (Nmat l B Y) = (2 : ℚ_[2]) ^ (Families.ds l).length • (InvBlock.outH l 1 ∘ₗ sysAct (T ℚ_[2] l) (l : ℤ) B (fun _ _ => Y) ∘ₗ InvBlock.inH l 1)`.
- **(N2) The entries.** For `B ≥ l + 1`, every `Y` and all `X Y'`:
  `Nmat l B Y Y' X = if o_X ≤ o_{Y'} + 2^k − 1 then 2 ^ k * InvFloors.gamma l X Y' * Y.coef (o_{Y'} + 2^k − 1 − o_X) ((o_{Y'} + 2^k − 1 : ℕ) : ℤ) else 0`
  (with `o_X = Rulers.oE (Windows.Dset (Families.ds l) X)`, etc., written out).

## Part Y — the inverse of `Ψ + t`

Let `α ≥ 2`, `c : ℕ` (any, `c = 0` included), `η : ℚ_[2]` with `‖η‖ = 1`, `ζ` with `‖ζ m f‖ ≤ 1` for `m ≥ 2` and all `f`, and `t : ℚ_[2]` with `‖t‖ = 1/2`.

- **(Y0) The payments.** For every `f : ℤ`: `‖PathSum.piF α c f + t‖ = 1/2`; and `(PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2])).coef 0 f = PathSum.piF α c f + t`. Hence there is `Y : Bf ℚ_[2]` with `Agree ((PathSum.XiOp α c η ζ + t • 1) * Y) 1` and `Agree (Y * (PathSum.XiOp α c η ζ + t • 1)) 1`.
- **(Y1) The bound.** For every `Y` with `Agree ((PathSum.XiOp α c η ζ + t • 1) * Y) 1`, all `L : ℕ` and `f : ℤ` with `(L : ℤ) ≤ f`:
  `‖Y.coef L f‖ ≤ ‖((L.factorial : ℕ) : ℚ_[2])‖ * 2 ^ (L + 1)`.

## Part B — the bend

- **(W) The window.** For `s s' : Fin (Dance.slots ds 1)` with `Windows.Dset ds s' ⊆ Windows.Dset ds s`:
  `Rulers.oE (Windows.Dset ds s) = Rulers.oE (Windows.Dset ds s') + Rulers.oE (Windows.Dset ds s \ Windows.Dset ds s')` and `Rulers.oE (Windows.Dset ds s \ Windows.Dset ds s') ≤ 2 ^ ds.length − 1`.
- **(B1) Lemma 10.20.** Let `l : ℕ` (any; `l = 0` included), `B ≥ l + 1`, `α ≥ 2`, `c ≥ 1`, `η` with `‖η‖ = 1`, `ζ` with `‖ζ m f‖ ≤ 1` for `m ≥ 2`, and `t` with `‖t‖ = 1/2`. Let `Y : Bf ℚ_[2]` satisfy `Agree ((PathSum.XiOp α c η ζ + t • 1) * Y) 1` and `Agree (Y * (PathSum.XiOp α c η ζ + t • 1)) 1`. Let `GΞ` satisfy `DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c η ζ) GΞ`. Then for all `s s'`:
  `‖(finalM GΞ * Nmat l B Y) s s'‖ ≤ 1 / 2`.
- **(B2) The two signs.** In the setting of (B1) with `t = 2` and `t = −2`, given the two inverses `Y₊` and `Y₋`: `‖(finalM GΞ * Nmat l B Y₊) s s'‖ ≤ 1/2` and `‖(finalM GΞ * Nmat l B Y₋) s s'‖ ≤ 1/2` (from (B1), with `‖2‖ = ‖−2‖ = 1/2`).

## Proof sketch

- **(N0)**: as in the proof of C42 `C109` (`h1` there).
  - Use `N2 l`, `sysAct_mul hnil hB`, `A1 htop`, and the agreement of `(fun _ _ => x) * (fun _ _ => Y)` with `1` (the lemma `magree_const_mul` of `InvFloors/PartC109.lean`).
  - Then `sysAct_one`.
- **(N1)**: both sides are linear. Compare them on `Pi.single X 1`; `Matrix.mulVecLin_apply` and `Matrix.mulVec_single` give column `X`.
- **(N2)**: `InvFloors.entry_sysAct`, multiplied by `2 ^ k`.
- **(Y0)**: from `‖π‖ ≤ (1/2)^α ≤ 1/4 < ‖t‖`, by the ultrametric equality. The coefficient `0` of `t • 1` is `t`.
  - Existence: `Conjugation.I` (the coefficient `0` is non-zero at every floor).
- **(Y1)**: strong induction on `L`, for all `f ≥ L`, from the recursion. It is `PathSum/Aux.lean` `coef_mul_split` with the coefficient `0` separated, as in C43 (P0).
  - The coefficients `a ≥ 1` of `Ψ + t` are those of `Ψ`: `η` and `ζ a f`, of norm `≤ 1`.
  - Each term `C(L, a)·Ψ_a(f)·Y_{L−a}(f − a)` has norm `≤ ‖C(L, a)‖·‖(L − a)!‖·2^{L−a+1}`.
  - `‖C(L, a)·(L − a)!‖ = ‖L!‖/‖a!‖ ≤ ‖L!‖·2^{a−1}`, by `PathSum.norm_factorial_ge` or `v_2(a!) ≤ a − 1`.
  - So each term is `≤ ‖L!‖·2^{L}`, and dividing by `‖π(f) + t‖ = 1/2` gives `‖L!‖·2^{L+1}`. At `L = 0`, `Y_0(f) = 1/(π(f) + t)`, of norm `2`.
- **(W)**: `Windows.Dset ds s ⊆ Windows.Ids ds ⊆ range ds.length`. So `oE` of a subset is a sum of distinct powers `2^t` with `t < k`, hence `≤ 2^k − 1` (`Finset.sum_pow_lt` style, or the geometric sum). The splitting is `Finset.sum_sdiff`.
- **(B1)**, for `l = 0`:
  - `Families.ds 0 = []`, `k = 0`, `ns = 1`.
  - `DanceRel [] 1 G GΞ` is `MAgree`, so `finalM GΞ 0 0 = (XiOp …).coef 0 0 = PathSum.piF α c 0`.
  - `Nmat 0 B Y 0 0 = Y.coef 0 0` by (N2): `o = 0`, `L = 0`, `gamma 0 0 0 = 1` (unfold; `Fd 0` is the identity).
  - `Y.coef 0 0 = 1/(piF α c 0 + t)` by the coefficient `0` of the agreement.
  - So the norm is `‖piF α c 0‖·2 ≤ 1/2`.
- **(B1)**, for `l ≥ 1`:
  - **Σ with `η = 1`.** `Conjugation.sig_one_dance` gives `G₁` with `DanceRel ds 1 (fun _ _ => SigOp α c 1) G₁`. `agree_SigOp_sLOp` and `Conjugation.I` (or `P0`) give the two-sided inverse `sLOp α c 1`. Then `InvFloors.C109` gives `IsUnit (finalM G₁).det` and `(finalM G₁)⁻¹ Y' X = 2^k γ sL(L, f)` (or `0` past the window).
  - **The inverse of `M_w(Σ₁)`.** By C44 `F2` and `A3`, `(finalM G₁)⁻¹ = diagonal (1/𝔡₂) * Binv * diagonal (1/𝔡₁)`, with `Binv ∈ Wt nest nuA 0` (`Amat * Binv = 1`). Hence `‖2^k γ_{XY'} sL‖ ≤ 2^{−nuA Y' X} / (|𝔡₂ Y'|·|𝔡₁ X|)`, and the left side is `0` unless `nest Y' X`.
  - **The final matrix of `Ψ`.** `Conjugation.T_eta` gives `GSig`, `E'` with `finalM GΞ = hadOne (finalM GSig) E'` and `‖E'‖ ≤ 1/2`; so `‖finalM GΞ D Y'‖ ≤ ‖finalM GSig D Y'‖`. `F1eta_gen` (at `η` and at `1`) and C44 `F1` give `‖finalM GSig D Y'‖ = ‖finalM G₁ D Y'‖ = |𝔡₁ D|·2^{−nuA D Y'}·|𝔡₂ Y'|` on `nest D Y'`, and `0` off it (`A2`; `‖η‖ = 1`).
  - **Each term.** By (N2), `Nmat Y' X = 2^k γ Y.coef L f` with `L = o_{Y'} + K − 1 − o_X` and `f = o_{Y'} + K − 1`. With `‖sL(L, f)‖ = ‖L!‖ / ∏_{i ≤ L} ‖π(f − i)‖` and (Y1):
    `‖M_ΞD Y'‖·‖N Y' X‖ ≤ (|𝔡₁ D|/|𝔡₁ X|)·2^{−nuA D Y' − nuA Y' X}·2^{L+1}·∏_{d=o_X}^{f} ‖π(d)‖`.
  - **The diagonal ratio.** `|𝔡₁ D|/|𝔡₁ X| = 2^{o_X − o_D} / ∏_{d=o_X}^{o_D − 1} ‖π(d)‖`, from `F2d1`, `pi0 = piF` cast, and `o_X ≤ o_D` by (W) (`nest D X`, from `nest D Y'` and `nest Y' X`, C44 `A1`).
  - **The window.** The product of the last two displays is `∏_{d=o_D}^{f} (2‖π(d)‖)·2^{−nuA − nuA} ≤ (1/2)^{f − o_D + 1}`, with `f − o_D + 1 = o_{Y'} + K − o_D ≥ 1` by (W) (`o_D − o_{Y'} ≤ K − 1`).
  - **The sum.** Sum over `Y'` with the ultrametric inequality (`IsUltrametricDist`, `norm_sum_le` in the non-archimedean form).
- **(B2)**: (B1) twice.

## Checks done before sending

- **Brute force `chkC50d.py`.** It builds on `chkC43.py`: an independent lattice model of `T(l)` with exact rationals, and the final matrices computed as `2^k O G^{−1} I` (C41 (V5)).
  - **(Y1)**: `α = 2, 3, 4`, `c = 0, 1, 2, 3, 6`, `t ∈ {2, −2, 6, 2/3, −10/7}`, `η` a random unit, `ζ` constant or depending on `f` (2-adic integers), `L ≤ 9`, `f ≤ 26`.
  - **(W)**: every `l ≤ 63`, every nested pair.
  - **(B1)**: every `l ≤ 7` (`l = 0` included), `α = 2, 3`, `c = 1, 2, 3, 4`, `ζ` zero, constant or depending on `f`, `t ∈ {2, −2, 6, 2/3}`; `M_w(Ψ)·N_t` computed on `T(l)`, with every entry `v_2 ≥ 1`. The bound `1` is attained, and off-diagonal entries occur.
  - **35 887 checks, 0 failures.** Log `logs/chkC50d.log`.
- **Controls (all four fire):**
  - `α = 1`: (B1) fails.
  - `t = ±4`: (B1) fails (the paper's control `Ψ ± 4`).
  - The bound `v_2 ≥ 2` in (B1): it fails, because `1` is attained.
  - (Y1) with `2^L` instead of `2^{L+1}`: it fails.
- **Error in my first run, in the test.** The control `t = −4` with `c = 1` hit a non-invertible system: the payment is `4(d + c − 1)`, which is `0` at `d = 0`. That control now uses `c ≥ 2`; no statement changed.

## Notes

- §10.7 is six pieces:
  - C50 (Lemma 10.19), C50b (Lemma 10.18), C50c (the arms), C50d (this piece, Lemma 10.20);
  - C50e: Corollary 10.21 (`W_± = ±(I − M_w(Ψ)N_±)^{−1} ≡ ±I mod 2`, by partial fractions and C41 (V5)), Theorem 10.22 for `i ≥ 1`, Proposition 10.7 for the glued system;
  - C50f: `i = 0` by congruences.
- (Y1) holds for every `c`, `c = 0` included. C50f will need this.
