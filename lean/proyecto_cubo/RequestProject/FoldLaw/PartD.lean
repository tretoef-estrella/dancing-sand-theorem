module

public import RequestProject.FoldLaw.PartL
public import RequestProject.FoldLaw.Groups

/-!
# `C51_theorem_DW.md`: Part D, (DW′) — the equivalent form of Theorem DW

* (DW′) `DW'`: for `n ≥ 2`, `Syl2 (K n) ≃+ (Fin (aN n) → ZMod 2) × H` with `H` finite,
  `Syl2 (KBar n) ≃+ twoM H` and `ℓ_0(H) = ℓ_1(H)`.

Proof: decompose `Syl2 (K n)` as `Π_i ZMod (2 ^ f i)` with `f i ≥ 1` (structure theorem), take for
`H` the product of the factors with `f i ≥ 2`, count the factors `ℤ/2` with C34 (B1), (B2), and
use (DW) together with `twoM (A × H) ≃+ twoM H` when `2A = 0`.
-/

@[expose] public section

noncomputable section

namespace FoldLaw

open CubeLaplacian Fold FoldGroup BaiCounts

/-- If `2A = 0`, then `twoM (A × H) ≃+ twoM H` (auxiliary for (DW′) of `C51_theorem_DW.md`). -/
def twoMProdKill {A H : Type*} [AddCommGroup A] [AddCommGroup H]
    (hA : ∀ a : A, (2 : ℕ) • a = 0) : twoM (A × H) ≃+ twoM H where
  toFun y := ⟨y.1.2, by
    obtain ⟨x, hx⟩ := mem_twoM.1 y.2
    exact mem_twoM.2 ⟨x.2, by rw [← hx]; rfl⟩⟩
  invFun z := ⟨(0, z.1), by
    obtain ⟨x, hx⟩ := mem_twoM.1 z.2
    exact mem_twoM.2 ⟨(0, x), by rw [← hx]; ext <;> simp⟩⟩
  left_inv y := by
    obtain ⟨⟨a, b⟩, hy⟩ := y
    obtain ⟨x, hx⟩ := mem_twoM.1 hy
    have ha : a = 0 := by
      have := congrArg Prod.fst hx
      simp only [Prod.smul_fst] at this
      rw [← this, hA]
    subst ha
    rfl
  right_inv z := rfl
  map_add' y y' := rfl

/-- Splitting off the factors `ℤ/2` of `Π_i ZMod (2 ^ f i)` (auxiliary for (DW′) of
`C51_theorem_DW.md`). -/
def piSplit {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℕ) :
    ((i : ι) → ZMod (2 ^ f i)) ≃+
      ((Fin (Fintype.card {i // f i = 1}) → ZMod 2) × ((j : {i // f i ≠ 1}) → ZMod (2 ^ f j))) :=
  let e1 : ((i : ι) → ZMod (2 ^ f i)) ≃+
      (((j : {i // f i = 1}) → ZMod (2 ^ f j)) × ((j : {i // ¬ f i = 1}) → ZMod (2 ^ f j))) :=
    { Equiv.piEquivPiSubtypeProd (fun i => f i = 1) (fun i => ZMod (2 ^ f i)) with
      map_add' := fun _ _ => rfl }
  let e2 : ((j : {i // f i = 1}) → ZMod (2 ^ f j)) ≃+ ({i // f i = 1} → ZMod 2) :=
    AddEquiv.piCongrRight fun j => (ZMod.ringEquivCongr (by rw [j.2]; rfl)).toAddEquiv
  let e3 : ({i // f i = 1} → ZMod 2) ≃+ (Fin (Fintype.card {i // f i = 1}) → ZMod 2) :=
    (LinearEquiv.funCongrLeft ℤ (ZMod 2) (Fintype.equivFin {i // f i = 1}).symm).toAddEquiv
  e1.trans (AddEquiv.prodCongr (e2.trans e3) (AddEquiv.refl _))

/-- `2 • x = 0` in `ZMod 2` (auxiliary for (DW′) of `C51_theorem_DW.md`). -/
lemma two_nsmul_zmod_two : ∀ x : ZMod 2, (2 : ℕ) • x = 0 := by decide

/-- **(DW′)** of `C51_theorem_DW.md` (Part D, the equivalent form of Theorem DW): for every
`n ≥ 2` there are a type `H : Type` with `[AddCommGroup H]` and `[Finite H]` such that
`Nonempty (CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+ (Fin (BaiCounts.aN n) → ZMod 2) × H)`,
`Nonempty (CubeLaplacian.Syl2 (Fold.KBar n) ≃+ FoldGroup.twoM H)` and
`BaiCounts.l0 H = BaiCounts.l1 H` (`H` has no cyclic factor `ℤ/2`). -/
theorem DW' (n : ℕ) (hn : 2 ≤ n) :
    ∃ (H : Type) (_ : AddCommGroup H) (_ : Finite H),
      Nonempty (CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+
        (Fin (BaiCounts.aN n) → ZMod 2) × H) ∧
      Nonempty (CubeLaplacian.Syl2 (Fold.KBar n) ≃+ FoldGroup.twoM H) ∧
      BaiCounts.l0 H = BaiCounts.l1 H := by
  classical
  haveI := K_finite n
  obtain ⟨ι, hι, f, hf1, ⟨e⟩⟩ := two_group_structure (Syl2 (K n)) fun x => by
    obtain ⟨k, hk⟩ := x.2
    exact ⟨k, Subtype.ext hk⟩
  let E := e.trans (piSplit f)
  have hA : ∀ (k : ℕ) (a : Fin k → ZMod 2), (2 : ℕ) • a = 0 := fun k a =>
    funext fun i => two_nsmul_zmod_two (a i)
  have hH0 : l0 ((j : {i // f i ≠ 1}) → ZMod (2 ^ f j)) =
      2 ^ Fintype.card {i // f i ≠ 1} := by
    rw [l0_pi, Finset.prod_congr rfl fun (j : {i // f i ≠ 1}) _ => l0_zmod (hf1 j.1)]
    simp
  have hH1 : l1 ((j : {i // f i ≠ 1}) → ZMod (2 ^ f j)) =
      2 ^ Fintype.card {i // f i ≠ 1} := by
    rw [l1_pi, Finset.prod_congr rfl fun (j : {i // f i ≠ 1}) _ =>
      l1_zmod (by have := hf1 j.1; have := j.2; omega)]
    simp
  have hA0 : ∀ k, l0 (Fin k → ZMod 2) = 2 ^ k := fun k => by
    rw [l0_pi]; simp [l0_zmod_two]
  have hA1 : ∀ k, l1 (Fin k → ZMod 2) = 1 := fun k => by
    rw [l1_pi]; simp [l1_zmod_two]
  have hk : Fintype.card {i // f i = 1} = aN n := by
    have h0 := l0_congr E
    rw [l0_prod, hA0, hH0, B1 n (by omega), ← pow_add] at h0
    have h1 := l1_congr E
    rw [l1_prod, hA1, one_mul, hH1, B2 n hn] at h1
    have h0' := Nat.pow_right_injective le_rfl h0
    have h1' := Nat.pow_right_injective le_rfl h1
    have := aN_le n hn
    omega
  refine ⟨(j : {i // f i ≠ 1}) → ZMod (2 ^ f j), inferInstance, inferInstance, ?_, ?_,
    by rw [hH0, hH1]⟩
  · rw [← hk]; exact ⟨E⟩
  · obtain ⟨d⟩ := DW n (by omega)
    exact ⟨d.trans ((twoMCongr E).trans (twoMProdKill (hA _)))⟩

end FoldLaw
