# C52 — the odd parts: Bai's odd part of `K(Q_n)` and the odd part of the folded cube (paper v8 §1.1, Corollary 1.4)

*Lean piece C52 of the Dancing Sand Theorem. Grepy Escribano, 10 October 2026. Folder `RequestProject/OddParts/`, namespace `OddParts`. Do not change any earlier file.*

This is the last piece. It proves the odd Sylow subgroups of the two sandpile groups:

- **Bai** [Bai03, Theorem 1.2]: for every odd prime `p`, `Syl_p K(Q_n) ≅ Syl_p ⊕_{j=1}^{n} (ℤ/j)^{C(n,j)}`.
- **Corollary 1.4, odd part**: for every odd prime `p`, `Syl_p K̄(n) ≅ Syl_p ⊕_{j even, 2 ≤ j ≤ n} (ℤ/2j)^{C(n,j)}` (the paper cites [GMMY24, Proposition 1.9]).

**The idea, all elementary.** The characters of `(ℤ/2)^n` are `χ_S(g) = (−1)^{Σ_{i∈S} g_i}`, `S ⊆ {1,…,n}`. The integer Fourier map `F f (S) = Σ_g χ_S(g) f(g)` sends the Laplacian `L` to the diagonal map `D v (S) = 2|S|·v(S)`, and the inverse map `F′ v (g) = Σ_S χ_S(g) v(S)` satisfies `F′ F = 2^n` and `F F′ = 2^n`. Hence `coker L` and `coker D` are related by two maps whose composites are multiplication by `2^n`. Multiplication by `2^n` is bijective on any `p`-primary group, `p` odd, so the `p`-parts agree. For the folded cube, the same with the `2^{n−1}` characters with `|S|` even.

## Setting (reuse; do not redefine)

- C17 `CubeLaplacian.G`, `CubeLaplacian.e`, `CubeLaplacian.lap`, `CubeLaplacian.L`, `CubeLaplacian.lap_apply`, `CubeLaplacian.coker`, `CubeLaplacian.K`, `CubeLaplacian.K_finite`, `CubeLaplacian.cokerEquivK`, `CubeLaplacian.Syl2`.
- C38 `Fold.aElt`, `Fold.Gbar`, `Fold.mk`, `Fold.lapBar`, `Fold.lapBar_apply`, `Fold.cokerBar`, `Fold.KBar`.
- C38b `FoldGroup.KBar_finite`, `FoldGroup.cokerBarEquivKBar`.

## Definitions (new, in `OddParts`; write them exactly like this)

```lean
/-- The `p`-primary part of an abelian group: elements killed by a power of `p`. -/
def Sylp (p : ℕ) (T : Type*) [AddCommGroup T] : AddSubgroup T where
  carrier := {y | ∃ k : ℕ, (p ^ k : ℕ) • y = 0}
  -- zero_mem', add_mem', neg_mem' : as for `CubeLaplacian.Syl2`

/-- The character `χ_S` of `G n = Fin n → ZMod 2`. -/
def chi (n : ℕ) (S : Finset (Fin n)) (g : CubeLaplacian.G n) : ℤ :=
  (-1) ^ (∑ i ∈ S, (g i).val)

/-- The Fourier map and its inverse (without division). -/
def fourier (n : ℕ) : (CubeLaplacian.G n → ℤ) →ₗ[ℤ] (Finset (Fin n) → ℤ)
  -- (fourier n f) S = ∑ g, chi n S g * f g
def ifourier (n : ℕ) : (Finset (Fin n) → ℤ) →ₗ[ℤ] (CubeLaplacian.G n → ℤ)
  -- (ifourier n v) g = ∑ S, chi n S g * v S

/-- The diagonal map `v ↦ (S ↦ 2|S| · v S)`. -/
def diagD (n : ℕ) : (Finset (Fin n) → ℤ) →ₗ[ℤ] (Finset (Fin n) → ℤ)
  -- (diagD n v) S = 2 * S.card * v S

/-- The subsets of even size. -/
abbrev EvenS (n : ℕ) := {S : Finset (Fin n) // Even S.card}

/-- The character `χ_S` on `Gbar n`, for `|S|` even (it is constant on cosets of `aElt n`). -/
def chiBar (n : ℕ) (S : EvenS n) : Fold.Gbar n → ℤ
  -- defined through the quotient, with `chiBar n S (Fold.mk n g) = chi n S.1 g`

def fourierBar (n : ℕ) : (Fold.Gbar n → ℤ) →ₗ[ℤ] (EvenS n → ℤ)
  -- (fourierBar n u) S = ∑ x, chiBar n S x * u x
def ifourierBar (n : ℕ) : (EvenS n → ℤ) →ₗ[ℤ] (Fold.Gbar n → ℤ)
  -- (ifourierBar n v) x = ∑ S, chiBar n S x * v S
def diagDBar (n : ℕ) : (EvenS n → ℤ) →ₗ[ℤ] (EvenS n → ℤ)
  -- (diagDBar n v) S = 2 * S.1.card * v S
```

The exact Lean form of `chiBar` is free (for example `QuotientAddGroup.lift` of an additive hom into `Multiplicative ℤ`, or a `Quotient.lift`), as long as lemma (X0) below holds.

## Part Q — the transfer lemma

- **(Q0)** `Sylp 2 T = CubeLaplacian.Syl2 T` for every abelian group `T`.
- **(Q1)** For abelian groups `A`, `B`, additive maps `f : A →+ B`, `g : B →+ A`, a natural number `m` with `∀ a, g (f a) = m • a` and `∀ b, f (g b) = m • b`, and a prime `p` with `¬ p ∣ m`:
  `Nonempty (Sylp p A ≃+ Sylp p B)`.
- **(Q2)** For abelian groups `A`, `B` and every prime `p`: `Nonempty (Sylp p (A × B) ≃+ Sylp p A × Sylp p B)`; and `Sylp p ℤ = ⊥`.

## Part F — Fourier on the cube

- **(X)** `chi n S (g + h) = chi n S g * chi n S h`, `chi n S 0 = 1`, `chi n S (e n i) = if i ∈ S then -1 else 1`.
- **(F1)** For every `n` and `f`: `fourier n (CubeLaplacian.L n f) = diagD n (fourier n f)`.
- **(F2)** For every `n` and `v`: `CubeLaplacian.L n (ifourier n v) = ifourier n (diagD n v)`.
- **(F3)** For every `n`: `∀ f, ifourier n (fourier n f) = (2 ^ n : ℕ) • f` and `∀ v, fourier n (ifourier n v) = (2 ^ n : ℕ) • v`.

## Part B — Bai's odd part

- **(B0)** For every `n` and every prime `p ≠ 2`:
  `Nonempty (Sylp p (CubeLaplacian.K n) ≃+ Sylp p ((S : {S : Finset (Fin n) // S.Nonempty}) → ZMod (2 * S.1.card)))`.
- **(B1) Bai's form.** For every `n` and every prime `p ≠ 2`:
  `Nonempty (Sylp p (CubeLaplacian.K n) ≃+ Sylp p ((j : Fin n) → Fin (n.choose (j + 1)) → ZMod (j + 1)))`.

## Part C — the folded cube

- **(X0)** `chiBar n S (Fold.mk n g) = chi n S.1 g`.
- **(C1)** For every `n` and `u`: `fourierBar n (Fold.lapBar ℤ n u) = diagDBar n (fourierBar n u)`.
- **(C2)** For every `n` and `v`: `Fold.lapBar ℤ n (ifourierBar n v) = ifourierBar n (diagDBar n v)`.
- **(C3)** For every `n ≥ 1`: `∀ u, ifourierBar n (fourierBar n u) = (2 ^ (n - 1) : ℕ) • u` and `∀ v, fourierBar n (ifourierBar n v) = (2 ^ (n - 1) : ℕ) • v`.
- **(C4)** For every `n ≥ 1` and every prime `p ≠ 2`:
  `Nonempty (Sylp p (Fold.KBar n) ≃+ Sylp p ((S : {S : EvenS n // S.1.Nonempty}) → ZMod (2 * S.1.1.card)))`.
- **(C5) Corollary 1.4, the paper's form.** For every `n ≥ 1` and every prime `p ≠ 2`:
  `Nonempty (Sylp p (Fold.KBar n) ≃+ Sylp p ((t : Fin (n / 2)) → Fin (n.choose (2 * (t + 1))) → ZMod (2 * (2 * (t + 1)))))`.
  (Here `j = 2(t + 1)` runs over the even numbers `2 ≤ j ≤ n`.)

## Proof sketch

- **(Q1)**: restrict `f`, `g` to the `p`-parts (they map `Sylp p A` into `Sylp p B` and back). On `Sylp p A` the map `y ↦ m • y` is bijective: if `p^k • y = 0`, pick `m′` with `m · m′ ≡ 1 (mod p^k)` (`Nat.Coprime (m) (p^k)`, from `¬ p ∣ m`); then `m′ • (m • y) = y`. So `f` restricted is injective, and surjective onto `Sylp p B` because every `z ∈ Sylp p B` is `m • z′ = f (g z′)` with `z′ ∈ Sylp p B`. Then `AddEquiv.ofBijective`.
- **(F1)–(F2)**: by (X), `Σ_i chi n S (g + e i) = chi n S g · Σ_i chi n S (e i) = chi n S g · (n − 2|S|)`. Reindex the sum over `g` by `g ↦ g + e i`.
- **(F3)**: orthogonality, `Σ_g chi n S g · chi n T g = 2^n` if `S = T`, else `0`; and `Σ_S chi n S g · chi n S h = 2^n` if `g = h`, else `0`. Both follow from `Σ_{x : ZMod 2} (−1)^{x.val} = 0`, factored over the coordinates (`Fintype.piFinset`, `Finset.prod_univ_sum`, or `Finset.prod_add`).
- **(B0)**:
  - (F1)–(F3) give maps `coker (L n) → coker (diagD n)` and back, with composites `2^n •` (`Submodule.mapQ`).
  - (Q1) with `m = 2^n`.
  - `coker (L n) ≃ ℤ × K n` (`cokerEquivK`).
  - `coker (diagD n) ≃ ℤ × Π_{S nonempty} ZMod (2|S|)`: the quotient of `Π_S ℤ` by `Π_S (2|S|)ℤ`, product of the `ℤ ⧸ (k)` ≃ `ZMod k`; the factor `S = ∅` is `ℤ`.
  - (Q2) removes the two factors `ℤ`.
- **(B1)**: `Sylp p (ZMod (2j)) ≃+ Sylp p (ZMod j)` for `p` odd (the `p`-part of a cyclic group of order `2j` is the one of order `j`); then group the nonempty subsets by their size `j + 1`, of which there are `n.choose (j + 1)` (`Finset.card_powersetCard`), with an explicit equivalence of index types.
- **(C1)–(C5)**: the same with `Gbar n` (of size `2^{n−1}` for `n ≥ 1`) and the `2^{n−1}` even subsets.
  - `chiBar` is well defined because `chi n S (aElt n) = (−1)^{|S|} = 1`.
  - Orthogonality on `Gbar n` comes from orthogonality on `G n`: each fibre of `Fold.mk n` has two elements, `g` and `g + aElt n`.
  - The sum over the even subsets of `chi n S g` is `2^{n−1}` if `g ∈ {0, aElt n}` and `0` otherwise.
  - Note that `lapBar` counts edges with multiplicity (`n = 2` gives a double edge); (C1) is the computation `Σ_i chiBar n S (x + mk (e i)) = chiBar n S x · (n − 2|S|)` and holds for every `n`.
  - (C5): group the nonempty even subsets by size `2(t + 1)`.

(Any proof is fine; the statement is what matters.)

## Checks done before sending

- **Brute force `chkC52.py`** (log `logs/chkC52.log`).
  - (F1), (F2), (F3), (C1), (C2), (C3) as integer matrix identities, `n = 0, …, 6` (folded: `n = 1, …, 6`).
  - The `p`-parts of the direct Smith forms of `L(Q_n)` (`n ≤ 8`) and of the folded Laplacian (`n ≤ 9`), for `p = 3, 5, 7`, by elimination modulo `p^E`, against (B0), (B1), (C4), (C5); exactly one zero invariant factor each.
- **Controls** (each must fail somewhere):
  - the folded cube against all nonempty subsets (not only even);
  - the cube against the even subsets only;
  - the formula for `p = 2` against the `2`-part of the cube.

## Notes

- After this piece the Lean of the Dancing Sand Theorem is complete: Main Theorem (C33), Bai's counts (C34), Corollaries 1.5–1.7 (C34–C37), Theorem DW and §10.8 (C51), and the odd parts (C52).
- Nothing here is cited from outside: Bai's theorem and [GMMY24, Proposition 1.9] are proved in this piece.
