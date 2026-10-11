import RequestProject.WeylFilt.All

/-! Auditor's check file for Lean piece C19 (Grepy Escribano, 7 Oct 2026).
The four maps restated on basis vectors by hand, in the words of
`C19_weyl_filtrations_of_V_tensor.md` (out-of-range vectors written as `0`); short exactness
unfolded (injective, surjective, range = ker); (S1)–(S4) and (M2) restated; then `#print axioms`. -/

open Finset DPLattice WeylFilt

-- the out-of-range convention
example {A : Type} [CommRing A] (l : ℕ) (k : ℤ) (j : Fin (l + 1)) :
    (ev l k : Fin (l + 1) → A) j = if (j : ℤ) = k then 1 else 0 := rfl

-- fΔ : e'_R ↦ b_0 e_R + b_1 e_{R−1}
example {A : Type} [CommRing A] (m : ℕ) (R : Fin (m + 1 + 1)) (hR : (R : ℕ) ≤ m) (h1 : 1 ≤ (R : ℕ)) :
    (fDelta A m).toLin (Pi.single R 1) =
      bvec 0 (Pi.single (⟨R, by omega⟩ : Fin (m + 1)) (1 : A)) +
      bvec 1 (Pi.single (⟨(R : ℕ) - 1, by omega⟩ : Fin (m + 1)) (1 : A)) := by
  change fDeltaLin m _ = _
  rw [fDeltaLin_single]
  congr 2
  · funext j; simp [ev, Pi.single_apply, Fin.ext_iff]
  · funext j; simp only [ev, Pi.single_apply, Fin.ext_iff]; split_ifs <;> first | rfl | omega
-- the two ends: e'_0 ↦ b_0 e_0 and e'_{m+1} ↦ b_1 e_m
example {A : Type} [CommRing A] (m : ℕ) :
    (fDelta A m).toLin (Pi.single (0 : Fin (m + 1 + 1)) 1) = bvec 0 (Pi.single (0 : Fin (m + 1)) (1 : A)) :=
  (S3 m).1
example {A : Type} [CommRing A] (m : ℕ) :
    (fDelta A m).toLin (Pi.single (Fin.last (m + 1)) 1) = bvec 1 (Pi.single (Fin.last m) (1 : A)) := by
  change fDeltaLin m _ = _
  rw [fDeltaLin_single, ev_of_gt m _ (by simp), map_zero, zero_add]
  congr 1; funext j; simp only [ev, Fin.val_last, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega
-- gΔ: the case list of the file
example {A : Type} [CommRing A] (m : ℕ) (hm : 1 ≤ m) :
    (∀ (s : ℕ) (hs : s ≤ m - 1), (gDelta A m hm).toLin (bvec 1 (Pi.single ⟨s, by omega⟩ 1)) =
      (Pi.single (⟨s, by omega⟩ : Fin (m - 1 + 1)) (1 : A))) ∧
    (gDelta A m hm).toLin (bvec 1 (Pi.single (Fin.last m) 1)) = 0 ∧
    (gDelta A m hm).toLin (bvec 0 (Pi.single (0 : Fin (m + 1)) 1)) = 0 ∧
    (∀ (R : ℕ) (h1 : 1 ≤ R) (h2 : R ≤ m), (gDelta A m hm).toLin (bvec 0 (Pi.single ⟨R, by omega⟩ 1)) =
      -(Pi.single (⟨R - 1, by omega⟩ : Fin (m - 1 + 1)) (1 : A))) :=
  gDeltaLin_cases m hm
-- f∇ : w''_r ↦ b_0 w_{r+1} − b_1 w_r
example {A : Type} [CommRing A] (m : ℕ) (hm : 1 ≤ m) (r : Fin (m - 1 + 1)) :
    (fNabla A m hm).toLin (Pi.single r 1) =
      bvec 0 (Pi.single (⟨(r : ℕ) + 1, by omega⟩ : Fin (m + 1)) (1 : A)) -
      bvec 1 (Pi.single (⟨r, by omega⟩ : Fin (m + 1)) (1 : A)) := by
  change fNablaLin m _ = _
  rw [fNablaLin_single]
  congr 2
  · funext j; simp only [ev, Pi.single_apply, Fin.ext_iff]; split_ifs <;> first | rfl | omega
  · funext j; simp [ev, Pi.single_apply, Fin.ext_iff]
-- g∇ : b_0 w_r ↦ w'_r, b_1 w_r ↦ w'_{r+1}
example {A : Type} [CommRing A] (m : ℕ) (r : Fin (m + 1)) :
    (gNabla A m).toLin (bvec 0 (Pi.single r 1)) = (Pi.single (⟨r, by omega⟩ : Fin (m + 1 + 1)) (1 : A)) ∧
    (gNabla A m).toLin (bvec 1 (Pi.single r 1)) =
      (Pi.single (⟨(r : ℕ) + 1, by omega⟩ : Fin (m + 1 + 1)) (1 : A)) := by
  obtain ⟨h0, h1⟩ := gNablaLin_single (A := A) m r
  refine ⟨?_, ?_⟩
  · refine h0.trans ?_; funext j; simp [ev, Pi.single_apply, Fin.ext_iff]
  · refine h1.trans ?_; funext j
    simp only [ev, Pi.single_apply, Fin.ext_iff]; split_ifs <;> first | rfl | omega

-- (S1), (S2) with short exactness unfolded
example {A : Type} [CommRing A] (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (fDelta A m).toLin ∧ Function.Surjective (gDelta A m hm).toLin ∧
    LinearMap.range (fDelta A m).toLin = LinearMap.ker (gDelta A m hm).toLin :=
  ⟨(S1 m hm).inj, (S1 m hm).surj, (S1 m hm).exact⟩
example {A : Type} [CommRing A] (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (fNabla A m hm).toLin ∧ Function.Surjective (gNabla A m).toLin ∧
    LinearMap.range (fNabla A m hm).toLin = LinearMap.ker (gNabla A m).toLin :=
  ⟨(S2 m hm).inj, (S2 m hm).surj, (S2 m hm).exact⟩
-- the morphisms: their underlying maps are the four maps
example {A : Type} [CommRing A] (m : ℕ) (hm : 1 ≤ m) :
    (fDelta A m).toLin = fDeltaLin m ∧ (gDelta A m hm).toLin = gDeltaLin m ∧
    (fNabla A m hm).toLin = fNablaLin m ∧ (gNabla A m).toLin = gNablaLin m := ⟨rfl, rfl, rfl, rfl⟩
-- (S3)
example {A : Type} [CommRing A] (m : ℕ) :
    LinearMap.range (fDelta A m).toLin = Submodule.span A (Set.range fun R : Fin (m + 1 + 1) =>
      (tensorV (delta A m)).Fd R (bvec 0 (Pi.single (0 : Fin (m + 1)) (1 : A)))) := (S3 m).2
-- (S4)
example {A : Type} [CommRing A] :
    (∃ (φ : Hom (tensorV (delta A 0)) (V A)) (ψ : Hom (V A) (tensorV (delta A 0))),
      (ψ.toLin ∘ₗ φ.toLin = LinearMap.id) ∧ (φ.toLin ∘ₗ ψ.toLin = LinearMap.id)) ∧
    (∃ (φ : Hom (tensorV (nabla A 0)) (V A)) (ψ : Hom (V A) (tensorV (nabla A 0))),
      (ψ.toLin ∘ₗ φ.toLin = LinearMap.id) ∧ (φ.toLin ∘ₗ ψ.toLin = LinearMap.id)) := by
  obtain ⟨⟨φ, ψ, h1, h2⟩, ⟨φ', ψ', h1', h2'⟩⟩ := (S4 (A := A))
  exact ⟨⟨φ, ψ, congrArg Hom.toLin h1, congrArg Hom.toLin h2⟩,
    ⟨φ', ψ', congrArg Hom.toLin h1', congrArg Hom.toLin h2'⟩⟩
-- (M2)
example {A : Type} [CommRing A] {M N P Q : DPLattice A} (f : Hom M N) (g : Hom N P) (h : Hom P Q) :
    Hom.comp h (Hom.comp g f) = Hom.comp (Hom.comp h g) f ∧
    Hom.comp (Hom.id N) f = f ∧ Hom.comp f (Hom.id M) = f :=
  ⟨(M2 f g h).2.2.1, (M2 f g h).2.2.2.1, (M2 f g h).2.2.2.2⟩

#print axioms fDeltaLin_single
#print axioms gDeltaLin_single
#print axioms fNablaLin_single
#print axioms gNablaLin_single
#print axioms gDeltaLin_cases
#print axioms M1_fDelta
#print axioms M1_gDelta
#print axioms M1_fNabla
#print axioms M1_gNabla
#print axioms M2
#print axioms S1
#print axioms S2
#print axioms S3
#print axioms S4_delta
#print axioms S4_nabla
#print axioms S4
