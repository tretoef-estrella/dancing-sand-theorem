# C50h — Theorem 10.22 at `i = 0`, and for every `i` (paper v8 §10.7)

*Lean piece C50h of the Dancing Sand Theorem. Grepy Escribano, 10 October 2026. Folder `RequestProject/EvenZero/`, namespace `EvenZero`. Do not change any earlier file.*

Paper v8, Theorem 10.22, case `i = 0`: **`X̄(2l + 2, 0) ≅ 2X(2l + 2, 0)`**. Together with C50g, this gives the fold law on every even family.

C50g proved the case `i ≥ 1`. At `i = 0`, the argument of C50g goes through for the arm `U` (it uses `Ψ_1`, with shift `1`). It fails only for the arm `U′ = Ψ_0(Ψ_0 + 2)/2`. There the shift is `0`, so the payment `4f` vanishes at `f = 0` and `Ψ_0` is not invertible: C50e cannot be applied to `Ψ_0`.

The paper replaces the shift by a parameter and passes to the limit. Here only the singular arm needs this, and the limit is taken by compactness.

**The idea.** Put `Ψ(c) := XiOpZ 2 c η ζ`, with `η = kJ 0 1` and `ζ_m = kJ 0 m`. Then `Ψ(0) = PsiF 0` (C49 `F5`). For `c_n := 2^n ≥ 1`:
1. C50c gives `Ψ(c_n)` as a good covariant system: `ArmsEven.P1` with `GPsi 0 0` at the position `c_n`.
2. C50c `H1` (with `h = 0`, `ε = 1`) gives the half `V_n` with `2V_n = Ψ(c_n)(Ψ(c_n) + 2)`, also good.
3. Both have dances (C48b `DanceXi.T2`).
4. C50g's one-arm argument (with any shift `c ≥ 1`) gives `W_n ∈ GL(ℤ_2)` with `W_n ≡ 1` (mod 2) and `M(V_n) = W_n·M(Ψ(c_n))`.
5. The systems converge as `n → ∞`:
   - `Ψ(c_n) ≡ Ψ(0)` modulo `2^{n+2}`, because the payments differ by `4c_n`;
   - `V_n ≡ V_0` modulo `2^{n+1}`, by halving `Ψ(c_n)(Ψ(c_n)+2) − Ψ(0)(Ψ(0)+2) ≡ 0` mod `2^{n+2}`.
6. By C49b `T1`, `T2`, the final matrices converge: modulo `2^{n+2−k}` and `2^{n+1−k}`.
7. `Matrix (Fin ns) (Fin ns) ℤ_[2]` is compact, so a subsequence of `(W_n)` converges, to `W∞`. The conditions `‖det W‖ = 1` and `‖W − 1‖ ≤ 1/2` are closed, so `W∞` satisfies them. Multiplication is continuous, so `M(V_0) = W∞·M(Ψ(0))`.

That is the arm `U′` at `i = 0`. Then the assembly of C50g `T` gives `i = 0`.

## Setting (reuse; do not redefine)

- C13 `Dance.slots`; C29 `Filt.T`; C32 `Families.ds`; C16 `FamilyGroup.X`; C38 `FoldGroup.XbarFam`, `FoldGroup.twoM`.
- C39 `FoldHalf.A4_even`; C39b `FoldCube.V6`.
- C40 `FormalOps.Bf`; C40b `FormalDance.Agree`, `MAgree`, `DanceRel`, `finalM`.
- C43 `PathSum.XiOp`, `PathSum.piF_ne_zero`; C45 `Conjugation.I`.
- C46 `Smith2.Bf.map`, `Smith2.XiOpZ`, `Smith2.M1`, `M4`, `M5`.
- C47 `RingK.covSys`; C48 `Cleanliness.Good`; C48b `DanceXi.T2`, `DanceXi.finOneDnEmpty`.
- C49 `FoldOdd.PsiF`, `FoldOdd.kJ`, `FoldOdd.F5`.
- C49b `ContZero.MCong`, `ContZero.T1`, `ContZero.T2`.
- C50 `GlueDance.D1`; C50c `ArmsEven.GPsi`, `uSys`, `P1`, `P3`, `H1`, `H2`.
- C50d `Bend.Y0`; C50e `BendCor.UOp`, `W3`.
- C50f `GlueEven.Q2`, `Q3`, `Q4`.
- C50g `EvenFold.P0`, `P1`, `M1`, `M2`, `A`, `T`.

Throughout: `ι := PadicInt.Coe.ringHom`, `Φ := Smith2.Bf.map ι`, `ds := Families.ds l`, `k := ds.length`, `ns := Dance.slots ds 1`, `h21 : (2 : ℕ) = 2 * 1`.

## Definitions (new)

- `PsiC (c : ℕ) : Bf ℤ_[2] := Smith2.XiOpZ 2 c (FoldOdd.kJ 0 1) (fun m _ => FoldOdd.kJ 0 m)` (the arm `Ψ_0` with its shift replaced by `c`).

## Part M — any shift

- **(M0) `Ψ_0` is the arm at shift `0`.** `PsiC 0 = FoldOdd.PsiF 0` and `IsUnit (FoldOdd.kJ 0 1)`.
- **(M1′) One arm, any shift `c ≥ 1`.** Let `l c : ℕ` with `1 ≤ c`, `η : ℤ_[2]` with `IsUnit η`, `z : ℕ → ℤ_[2]`, and `t : ℤ_[2]` with `t = 2 ∨ t = -2`. Put `Ξ := Smith2.XiOpZ 2 c η (fun m _ => z m)`. Let `V : Bf ℤ_[2]` with `(2 : ℤ_[2]) • V = Ξ * (Ξ + t • 1)`. Let `Xk Vk` (matrices over `Bf ℤ_[2]` indexed by `Fin (Dance.slots (Families.ds l) 1)`) satisfy `DanceRel (Families.ds l) 1 (fun _ _ => Ξ) Xk` and `DanceRel (Families.ds l) 1 (fun _ _ => V) Vk`.
  Then there is `W'` with
  - `IsUnit W'.det`;
  - `‖(((W' - 1) s s' : ℤ_[2]) : ℚ_[2])‖ ≤ 1 / 2` for all `s s'`;
  - `finalM Vk = W' * finalM Xk`.

  (This is C50g `M1` with `PsiF j` replaced by any `XiOpZ 2 c η z` with `c ≥ 1`. The proof is the same.)

## Part K — the approximation

- **(K1)** For every `n`: `ContZero.MCong (n + 2) (fun _ _ : Fin 1 => PsiC (2 ^ n)) (fun _ _ : Fin 1 => PsiC 0)`.
- **(K2)** For every `n`, and `V V₀ : Bf ℤ_[2]` with
  `(2 : ℤ_[2]) • V = PsiC (2 ^ n) * (PsiC (2 ^ n) + (2 : ℤ_[2]) • 1)` and `(2 : ℤ_[2]) • V₀ = PsiC 0 * (PsiC 0 + (2 : ℤ_[2]) • 1)`:
  `ContZero.MCong (n + 1) (fun _ _ : Fin 1 => V) (fun _ _ : Fin 1 => V₀)`.
- **(K3) The approximants exist.** For every `l n`, there are `V : Bf ℤ_[2]` and matrices `Xk Vk` with:
  - `(2 : ℤ_[2]) • V = PsiC (2 ^ n) * (PsiC (2 ^ n) + (2 : ℤ_[2]) • 1)`;
  - `DanceRel (Families.ds l) 1 (fun _ _ => PsiC (2 ^ n)) Xk`;
  - `DanceRel (Families.ds l) 1 (fun _ _ => V) Vk`.

## Part L — the singular arm

- **(L) The arm `U′` at `i = 0`.** Let `l : ℕ`, and let `V : Bf ℤ_[2]` with `(2 : ℤ_[2]) • V = FoldOdd.PsiF 0 * (FoldOdd.PsiF 0 + (2 : ℤ_[2]) • 1)`. Let `Xk Vk` satisfy `DanceRel (Families.ds l) 1 (fun _ _ => FoldOdd.PsiF 0) Xk` and `DanceRel (Families.ds l) 1 (fun _ _ => V) Vk`.
  Then there is `W' : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1)) ℤ_[2]` with
  - `IsUnit W'.det`;
  - `‖(((W' - 1) s s' : ℤ_[2]) : ℚ_[2])‖ ≤ 1 / 2` for all `s s'`;
  - `finalM Vk = W' * finalM Xk`.

## Part T — the fold law on every even family

- **(T0) `i = 0`.** For every `l : ℕ`:
  `Nonempty (FoldGroup.XbarFam (2 * l + 2) 0 ≃+ FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 2)) 1 0))`.
- **(TT) Theorem 10.22.** For all `l i : ℕ`:
  `Nonempty (FoldGroup.XbarFam (2 * l + 2) i ≃+ FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 2)) 1 i))`.

## Proof sketch

- **(M0)**: C49 `F5 0 c` (`(0 + 1) / 2 = 0`).
- **(M1′)**: the proof of C50g `M1`, with C46 `M5` applied to `XiOpZ 2 c η (fun m _ => z m)` directly instead of through `F5`. The facts needed:
  - `‖ι η‖ = 1`, from `IsUnit η`;
  - `‖ι (z m)‖ ≤ 1`;
  - `c ≥ 1`, for `piF_ne_zero` and `Conjugation.I`;
  - C50d `Y0` for the inverse of `Ψ + t`;
  - C50e `W3` (with `B := l + 1`);
  - the injectivity of `ι`.
- **(K1)**: `PsiC (2^n) − PsiC 0` has only the coefficient `0`, equal to `4·2^n = 2^{n+2}·1` at every floor (unfold `XiOpZ`: the payment is `2^α (f + c)`). Take `Z` with that single coefficient `1`; `MCong` is `∃ Z, MAgree (G − H) (2^M • Z)` (read the definition in C49b `Defs.lean`).
- **(K2)**: put `D := PsiC (2^n) − PsiC 0 = 2^{n+2}·e` (from (K1), as an equality of `Bf`). Then
  `2(V − V₀) = D·(PsiC (2^n) + 2) + PsiC 0·D`,
  which is `2^{n+2}·(…)`. The field `ℤ_[2]` has no 2-torsion, so `V − V₀ = 2^{n+1}·(…)`, coefficientwise.
- **(K3)**:
  - Use C50c with `Γ := ArmsEven.GPsi 0 0`, which is good (`P3`).
  - `ArmsEven.P1 (2^n) 0 0` gives `covSys ∅ 0 ((2^n : ℕ) : ℤ_[2]) Γ e∅ e∅ = Smith2.XiOpZ 2 (2^n + 0) (kJ 0 1) (fun m _ => kJ 0 m) = PsiC (2^n)`.
  - `ArmsEven.H1 Γ hΓ 0 1 (Or.inl rfl)` gives a good `Γ'` with `2Γ' = prodFun 0 Γ (Γ + 2·uSys)`. `ArmsEven.H2` gives `(2 : ℤ_[2]) • covSys ∅ 0 c Γ' = covSys ∅ 0 c Γ * (covSys ∅ 0 c Γ + 2 • 1)`. Take `V := covSys ∅ 0 c Γ' e∅ e∅`, the `(e∅, e∅)` entry (as C50c `E1` does).
  - The two dances come from `DanceXi.T2` (with `r = 1`, `h = 0`, `P = ∅`, `e = DanceXi.finOneDnEmpty`), applied to `Γ` and `Γ'`.
- **(L)**:
  - For each `n`:
    - (K3) gives `V_n`, `Xk_n`, `Vk_n`;
    - (M1′), with `c := 2^n ≥ 1`, `η := kJ 0 1` (a unit by (M0)), `z := kJ 0` and `t := 2`, gives `W_n`;
    - (K1) and (K2), with the given `V` as `V₀` and `PsiC 0 = PsiF 0` (M0), and C49b `T1` (with `M := n + 1 − k`, written as `M + k ≤ n + 1`; use `MCong.mono` or the definition for the smaller exponent) and `T2`, give
      `finalM Xk_n ≡ finalM Xk` and `finalM Vk_n ≡ finalM Vk` modulo `2^{n+1−k}`, entrywise.
  - Hence `finalM Xk_n → finalM Xk` and `finalM Vk_n → finalM Vk` in `Matrix … ℤ_[2]`, with the product topology. Use `‖2^m w‖ ≤ 2^{−m}` (`PadicInt.norm_le_one`, `norm_mul`, `norm_pow`, `ContZero.norm_two_padic`) and `tendsto_pi_nhds`.
  - `Matrix (Fin ns) (Fin ns) ℤ_[2]` is a compact space: `ℤ_[2]` is compact (Mathlib), and a finite product of compact spaces is compact. `IsCompact.tendsto_subseq` (or `CompactSpace.tendsto_subseq`) gives `φ` strictly monotone and `W∞` with `W_{φ n} → W∞`.
  - The relation passes to the limit: `finalM Vk_{φ n} = W_{φ n} * finalM Xk_{φ n}`. Matrix multiplication is continuous (`Continuous.matrix_mul`), and limits in a Hausdorff space are unique (`tendsto_nhds_unique`). So `finalM Vk = W∞ * finalM Xk`.
  - `det` is continuous (`Continuous.matrix_det`). The set `{x : ℤ_[2] | ‖x‖ = 1}` is closed, so `‖W∞.det‖ = 1`, hence `IsUnit` (`PadicInt.isUnit_iff`). The congruence `‖ι((W∞ − 1) s s')‖ ≤ 1/2` is closed in `W∞`, entrywise (`isClosed_le`, continuity of `ι` and of the norm).
- **(T0)**: the proof of C50g `T` at `i = 0`, with one change. The arm `U` uses C50g `M1` with `j := 1`, `t := −2` (`1 ≤ 1`). The arm `U′` uses (L) with `V := U′` instead of C50g `M1` with `j := 0`. Everything else is as in C50g `T`: `FoldHalf.A4_even l 0`, `GlueEven.Q2 h21 l 0 0`, `GlueDance.D1`, `GlueEven.Q4 l 0`, `GlueEven.Q3`, `EvenFold.M2`, `EvenFold.A`, `FoldCube.V6 l 0`.
- **(TT)**: `i = 0` is (T0); `i ≥ 1` is C50g `EvenFold.T`.

## Checks done before sending

- **Brute force `chkC50h.py`.** It uses the lattice model of `chkC43.py`, with exact rationals, and the series `K(j)` of `chkC49.py`. It takes the arm `Ψ(2^n)`: payment `4(f + 2^n)`, `η = K(0)_1 = 1`, `ζ_m = K(0)_m`. The cases are every `l ≤ 6` and `0 ≤ n ≤ 8`.
  - The final matrices `M_Ψ(2^n)` and `M_V(2^n)` are integral.
  - `W(2^n) = M_V·M_Ψ⁻¹` is in `GL(ℤ_2)` and `≡ I` modulo 2, and `M_V = W·M_Ψ` exactly.
  - **The convergence of (K1)/(K2) through `T1`.** `v_2(M_Ψ(2^{n+1}) − M_Ψ(2^n)) ≥ n + 2 − k` and `v_2(M_V(2^{n+1}) − M_V(2^n)) ≥ n + 1 − k`.
  - The matrices `W(2^n)` themselves converge in every case tested: `v_2(W(2^{n+1}) − W(2^n))` grows linearly in `n`. The proof does not need this, because compactness gives a convergent subsequence.
  - **302 checks, 0 failures.** Log `logs/chkC50h.log`.
- **Controls (all three fire):**
  - `c = 0` itself: `Ψ_0` is singular on `T(l)`. This is why the limit is needed.
  - The rate `n + 3 − k`, one more than claimed for `M_Ψ` on the same pairs: it fails somewhere.
  - The shifts `2^n + 1` do not approach the data at `2^n`: the difference is not small.
- **Theorem 10.22 at `i = 0`, numerically:** `chkC50f.py` found the two Smith forms equal in 7 of 7 cases (`l ≤ 6`).

## Notes

- After this piece:
  - C51: Theorem DW, the fold law for every `λ` and `i`, by C38b's Proposition 10.3 from C49c `C5` (odd families) and (TT) (even families);
  - C52: the odd parts.
- (M1′) is stated for any shift `c ≥ 1`, so that C51 or C52 may reuse it.
