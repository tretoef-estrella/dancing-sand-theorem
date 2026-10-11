# C43 — Lemma 10.10 (the path sum) and the relation of the final inverses (paper v8 §10.4)

*Lean piece C43 of the Dancing Sand Theorem. Grepy Escribano, 9 October 2026. Folder `RequestProject/PathSum/`, namespace `PathSum`. Do not change any earlier file.*

Paper v8 §10.4 fixes `α ≥ 2`, `c ≥ 1`, a unit `η` of `ℤ_2`, and
  `Σ := 2^α(D + c) + ηF`,  `Ξ := Σ + Σ_{m≥2} ζ_m(D) F^{(m)}`  (integral `ζ_m`),
with `π(d) := 2^α(d + c)`. Lemma 10.10 says that the coefficients of `Ξ^{−1}` are those of `Σ^{−1}` up to a factor `1 + e` with `v_2(e) ≥ α − 1`, and that `Σ^{−1}` is explicit. With C42 (Corollary 10.9), this gives the first half of the proof of Theorem 10.12: `M_w(Ξ)^{−1} = M_w(Σ)^{−1} ∘ (1 + E)` with `v_2(E) ≥ α − 1` entrywise. This piece proves both. Lemma 10.11 (stability) and Theorem 10.12 go to C44.

## Setting (reuse; do not redefine)

- C40 `FormalOps.Bf` (`coef : ℕ → ℤ → A`, the coefficient of `F^{(m)}` at the TARGET floor; the product `(xy)_m(f) = Σ_{a+b=m} C(m, a) x_a(f) y_b(f − a)`); C40b `FormalDance.Agree` (agreement at the floors `f ≥ m`), `DanceRel`, `finalM`; C29 `Filt.T`; C32 `Families.ds`; C3 `Rulers.oE`; C14 `Windows.Dset`.
- C42 `InvFloors.gamma`, `InvFloors.C109`.
- C20 `Doubling.OddUnits` and the instance `OddUnits ℤ_[2]`.

The field is `ℚ_[2]` with its norm `‖·‖` (so `‖x‖ ≤ 2^{−s}` means `v_2(x) ≥ s`). If no instance `OddUnits ℚ_[2]` exists in the project, prove one (every odd natural number is non-zero in a field of characteristic zero).

## Statements to prove

**Definitions (new).** For `α c : ℕ`, `η : ℚ_[2]` and `ζ : ℕ → ℤ → ℚ_[2]`:
- `piF α c : ℤ → ℚ_[2]`, `piF α c d = 2 ^ α * (d + c)`.
- `XiOp α c η ζ : Bf ℚ_[2]` with `coef 0 f = piF α c f`, `coef 1 f = η`, `coef m f = ζ m f` for `m ≥ 2`; and `SigOp α c η := XiOp α c η (fun _ _ => 0)`.
- `sL α c η (L : ℕ) (f : ℤ) : ℚ_[2] := (−1) ^ L * L ! * η ^ L / ∏_{i ∈ range (L + 1)} piF α c (f − i)` (the product over the floors `d = f − L, …, f`).

**(P0) Uniqueness of the right inverse.** For `x : Bf ℚ_[2]` with `x.coef 0 f ≠ 0` for every `f ≥ 0`, and `Y₁ Y₂ : Bf ℚ_[2]` with `Agree (x * Y₁) 1` and `Agree (x * Y₂) 1`: `Agree Y₁ Y₂` (that is, `Y₁.coef L f = Y₂.coef L f` for all `L` and `f ≥ L`).

**(P1) The inverse of `Σ`.** For `c ≥ 1` and `Y : Bf ℚ_[2]` with `Agree (SigOp α c η * Y) 1`: for all `L` and `f ≥ L`, `Y.coef L f = sL α c η L f`. (Here `η` is arbitrary.)

**(P2) Lemma 10.10, the path sum.** For `α ≥ 2`, `c ≥ 1`, `‖η‖ = 1`, `‖ζ m f‖ ≤ 1` for all `m ≥ 2` and `f`, and `Y : Bf ℚ_[2]` with `Agree (XiOp α c η ζ * Y) 1`: for all `L` and `f ≥ L` there is `e : ℚ_[2]` with
  `Y.coef L f = sL α c η L f * (1 + e)`  and  `‖e‖ ≤ 2 ^ (−(α − 1 : ℤ))`.
(Also `sL α c η L f ≠ 0`.)

**(R) The final inverses.** For `α ≥ 2`, `c ≥ 1`, `‖η‖ = 1`, `‖ζ m f‖ ≤ 1`, `l B : ℕ` with `B ≥ l + 1`, `YΞ YΣ : Bf ℚ_[2]` with `Agree (XiOp α c η ζ * YΞ) 1`, `Agree (YΞ * XiOp α c η ζ) 1`, `Agree (SigOp α c η * YΣ) 1`, `Agree (YΣ * SigOp α c η) 1`, and `GΞ GΣ` with `DanceRel (Families.ds l) 1 (fun _ _ => XiOp α c η ζ) GΞ`, `DanceRel (Families.ds l) 1 (fun _ _ => SigOp α c η) GΣ`: for all final slots `X Y'`,
  - if `(finalM GΣ)⁻¹ Y' X = 0` then `(finalM GΞ)⁻¹ Y' X = 0`;
  - otherwise there is `e` with `(finalM GΞ)⁻¹ Y' X = (finalM GΣ)⁻¹ Y' X * (1 + e)` and `‖e‖ ≤ 2 ^ (−(α − 1 : ℤ))`.
(The paper: `M_w(Ξ)^{−1} = M_w(Σ)^{−1} ∘ (1 + E)` with `v_2(E) ≥ α − 1`, with the same `γ`, by Corollary 10.9 and Lemma 10.10.)

## Proof sketch
- (P0), (P1): the `m`-th coefficient of `x * Y = 1` at a floor `f ≥ m` reads `x_0(f) Y_m(f) + Σ_{a=1}^{m} C(m, a) x_a(f) Y_{m−a}(f − a) = [m = 0]`, and `f − a ≥ m − a`; so `Y_m(f)` is determined by induction on `m`. For `Σ` only `a = 1` occurs: `Y_m(f) = −m η Y_{m−1}(f − 1)/π(f)`, which is the recursion of `sL`.
- (P2): strong induction on `L` (for all `f ≥ L`). With `Y_L(f) π(f) = −Σ_{a=1}^{L} C(L, a) Ξ_a(f) Y_{L−a}(f − a)`, the term `a = 1` is `−L η sL(L−1, f−1)(1 + e')` and `−L η sL(L−1, f−1)/π(f) = sL(L, f)`. For `a ≥ 2`, the ratio of the term to `−L η sL(L−1, f−1)` is `± ζ_a(f) η^{−a}/a! · ∏ π(d)` over the `a − 1` floors `d = f − a + 1, …, f − 1` that the jump skips, times `(1 + e'')`; its valuation is at least `α(a − 1) − v_2(a!) ≥ (α − 1)(a − 1) ≥ α − 1`, since `v_2(a!) ≤ a − 1`, `v_2(π(d)) ≥ α`, `‖η‖ = 1`, `‖ζ‖ ≤ 1`. The ultrametric inequality sums the terms.
- (R): `C109` for `Ξ` and for `Σ` (same `l`, so the same `gamma`) and (P1), (P2) at the same `L`, `f`: the entry is `2^k γ YΞ.coef L f` against `2^k γ sL L f`; if the `Σ` entry is `0` then `γ = 0` (as `sL ≠ 0`) or `oX > oY' + 2^k − 1`, and the `Ξ` entry is `0` too.

## Checks done before sending
- Brute force `chkC43.py` (on `chkC42.py`; exact rationals, `v_2` of fractions). (P1), (P2): `α = 2, 3, 4`, `c = 1, 2, 3, 6`, four random data each (`η` odd, `ζ_m(f)` random integers in `[−6, 6]`), the right inverse by the recursion of (P0), `L ≤ 9`, `f ≤ 24`: `Σ` exact and `v_2(e) ≥ α − 1`; the bound is attained (`v_2(e) = α − 1` occurs for `α = 2, 3, 4`). (R): `l ≤ 7`, `α = 2, 3`, `c = 1, 3`: the final inverses computed as `2^k O (act Ξ on T(l))^{−1} I` (C41 (V5), C42) — same zeros, and `v_2(M_Ξ^{−1}/M_Σ^{−1} − 1) ≥ α − 1` entrywise (the matrices are not trivial: e.g. 9 non-zero entries of 16 at `l = 6`). **19 713 checks, 0 failures.** `logs/chkC43.log`.
- Controls (all four fire): the bound `α` instead of `α − 1`; the product over `L` floors instead of `L + 1`; `sL` without `L!`; and at `α = 1` the bound is empty (`v_2(e) = 0` occurs), so the hypothesis `α ≥ 2` is needed for a non-trivial statement.
- An error of my first run, in the test: a loop variable named `L` shadowed the lattice library imported as `L`; renamed, nothing else changed.

## Notes
- §10.4 is in four pieces: C41 (Lemma 10.8, certified), C42 (floors, Corollary 10.9, certified), C43 (this piece), C44 (Lemma 10.11 stability, Theorem 10.12 rigidity: `M_w(Σ) = 𝔡_1 𝒜 𝔡_2`, the Smith form, the cokernel `X^{(α)}(l, c)`).
