module

public import RequestProject.Smith2.Defs
public import RequestProject.PathSum.Defs

/-!
# `C46_smith_form_and_cokernel_over_Z2.md`, Part M — the formal dance along a ring homomorphism

(M1) `M1`; (M2) `M2`; (M3) `M3`; (M4) `M4`; (M5) `M5`, with the individual lemmas
(`Bf.map_mul`, `tw10_map`, `cleanStep_map`, `danceRel_map`, …).
-/

@[expose] public section

noncomputable section

namespace Smith2

open FormalOps FormalDance Doubling Finset

variable {A A' : Type*} [CommRing A] [CommRing A'] (φ : A →+* A')

/-! ### (M1) -/

/-- Part of (M1) of `C46_smith_form_and_cokernel_over_Z2.md`: `Bf.map_zero`. -/
lemma Bf.map_zero : Bf.map φ (0 : Bf A) = 0 := by ext m f; simp

/-- Part of (M1) of `C46_smith_form_and_cokernel_over_Z2.md`: `Bf.map_one`. -/
lemma Bf.map_one : Bf.map φ (1 : Bf A) = 1 := by
  ext m f; simp only [Bf.coef_map, Bf.coef_one]; split_ifs <;> simp

/-- Part of (M1) of `C46_smith_form_and_cokernel_over_Z2.md`: `Bf.map_add`. -/
lemma Bf.map_add (x y : Bf A) : Bf.map φ (x + y) = Bf.map φ x + Bf.map φ y := by
  ext m f; simp

/-- Part of (M1) of `C46_smith_form_and_cokernel_over_Z2.md`: `Bf.map_mul`. -/
lemma Bf.map_mul (x y : Bf A) : Bf.map φ (x * y) = Bf.map φ x * Bf.map φ y := by
  ext m f; simp [map_sum]

/-- Part of (M1) of `C46_smith_form_and_cokernel_over_Z2.md`: `Bf.map_smul`. -/
lemma Bf.map_smul (a : A) (x : Bf A) : Bf.map φ (a • x) = φ a • Bf.map φ x := by
  ext m f; simp

/-- Part of (M1) of `C46_smith_form_and_cokernel_over_Z2.md`: `Bf.map_fd`. -/
lemma Bf.map_fd (m : ℕ) : Bf.map φ (Bf.fd m : Bf A) = Bf.fd m := by
  ext m' f; simp only [Bf.coef_map, Bf.coef_fd]; split_ifs <;> simp

/-- Part of (M1) of `C46_smith_form_and_cokernel_over_Z2.md`: `Bf.map_dg`. -/
lemma Bf.map_dg (p : ℤ → A) : Bf.map φ (Bf.dg p) = Bf.dg (φ ∘ p) := by
  ext m f; simp only [Bf.coef_map, Bf.coef_dg, Function.comp]; split_ifs <;> simp

/-- Proof of (M1) of `C46_smith_form_and_cokernel_over_Z2.md`: a ring homomorphism with underlying
function `Bf.map φ`. -/
lemma Bf.exists_ringHom : ∃ F : Bf A →+* Bf A', ∀ x, F x = Bf.map φ x :=
  ⟨{ toFun := Bf.map φ, map_one' := Bf.map_one φ, map_mul' := Bf.map_mul φ,
     map_zero' := Bf.map_zero φ, map_add' := Bf.map_add φ }, fun _ => rfl⟩

/-- **(M1)** of `C46_smith_form_and_cokernel_over_Z2.md`: `Bf.map φ` is (the underlying function
of) a ring homomorphism `Bf A →+* Bf A'`; `Bf.map φ (a • x) = φ a • Bf.map φ x`;
`Bf.map φ (Bf.fd m) = Bf.fd m`; `Bf.map φ (Bf.dg p) = Bf.dg (φ ∘ p)`. -/
theorem M1 :
    (∃ F : Bf A →+* Bf A', ∀ x, F x = Bf.map φ x) ∧
    (∀ (a : A) (x : Bf A), Bf.map φ (a • x) = φ a • Bf.map φ x) ∧
    (∀ m : ℕ, Bf.map φ (Bf.fd m : Bf A) = Bf.fd m) ∧
    (∀ p : ℤ → A, Bf.map φ (Bf.dg p) = Bf.dg (φ ∘ p)) :=
  ⟨Bf.exists_ringHom φ, Bf.map_smul φ, Bf.map_fd φ, Bf.map_dg φ⟩

/-! ### (M2) -/

/-- Part of (M2) of `C46_smith_form_and_cokernel_over_Z2.md`: `map_ringInverse_of_isUnit`. -/
lemma map_ringInverse_of_isUnit {u : A} (hu : IsUnit u) :
    φ (Ring.inverse u) = Ring.inverse (φ u) := by
  obtain ⟨v, rfl⟩ := hu
  rw [Ring.inverse_unit]
  have h1 : φ (↑v⁻¹ : A) = ((Units.map (φ : A →* A') v)⁻¹ : A'ˣ) := by simp
  have h2 : φ (v : A) = ((Units.map (φ : A →* A') v) : A'ˣ) := by simp
  rw [h1, h2, Ring.inverse_unit]

/-- Part of (M2) of `C46_smith_form_and_cokernel_over_Z2.md`: `map_dfi`. -/
lemma map_dfi [OddUnits A] (s : ℕ) : φ (dfi s : A) = dfi s := by
  rw [dfi, dfi, map_ringInverse_of_isUnit φ (isUnit_df s), map_natCast]

/-- Part of (M2) of `C46_smith_form_and_cokernel_over_Z2.md`: `tw00_map`. -/
lemma tw00_map [OddUnits A] (x : Bf A) : Bf.map φ (tw00 x) = tw00 (Bf.map φ x) := by
  ext q f; simp [map_dfi]

/-- Part of (M2) of `C46_smith_form_and_cokernel_over_Z2.md`: `tw11_map`. -/
lemma tw11_map [OddUnits A] (x : Bf A) : Bf.map φ (tw11 x) = tw11 (Bf.map φ x) := by
  ext q f; simp [map_dfi]

/-- Part of (M2) of `C46_smith_form_and_cokernel_over_Z2.md`: `tw10_map`. -/
lemma tw10_map [OddUnits A] (x : Bf A) : Bf.map φ (tw10 x) = tw10 (Bf.map φ x) := by
  ext q f; simp [map_dfi]

/-- Part of (M2) of `C46_smith_form_and_cokernel_over_Z2.md`: `tw01_map`. -/
lemma tw01_map [OddUnits A] (x : Bf A) : Bf.map φ (tw01 x) = tw01 (Bf.map φ x) := by
  ext q f; rcases q with _ | q <;> simp [map_dfi, map_ofNat]

/-- Part of (M2) of `C46_smith_form_and_cokernel_over_Z2.md`: `vplus_map`. -/
lemma vplus_map (x : Bf A) : Bf.map φ (vplus x) = vplus (Bf.map φ x) := by ext q f; simp

/-- Part of (M2) of `C46_smith_form_and_cokernel_over_Z2.md`: `vprime_map`. -/
lemma vprime_map (x : Bf A) : Bf.map φ (vprime x) = vprime (Bf.map φ x) := by ext q f; simp

/-- **(M2)** of `C46_smith_form_and_cokernel_over_Z2.md`: if `[OddUnits A]`, `Bf.map φ` commutes
with `tw00`, `tw11`, `tw10`, `tw01`; and (with no hypothesis) with `vplus`, `vprime`. -/
theorem M2 :
    ([OddUnits A] → ∀ x : Bf A,
      Bf.map φ (tw00 x) = tw00 (Bf.map φ x) ∧ Bf.map φ (tw11 x) = tw11 (Bf.map φ x) ∧
      Bf.map φ (tw10 x) = tw10 (Bf.map φ x) ∧ Bf.map φ (tw01 x) = tw01 (Bf.map φ x)) ∧
    (∀ x : Bf A, Bf.map φ (vplus x) = vplus (Bf.map φ x) ∧
      Bf.map φ (vprime x) = vprime (Bf.map φ x)) :=
  ⟨fun x => ⟨tw00_map φ x, tw11_map φ x, tw10_map φ x, tw01_map φ x⟩,
    fun x => ⟨vplus_map φ x, vprime_map φ x⟩⟩

/-! ### (M3) -/

/-- Part of (M3) of `C46_smith_form_and_cokernel_over_Z2.md`: `agree_map`. -/
lemma agree_map {x y : Bf A} (h : Agree x y) : Agree (Bf.map φ x) (Bf.map φ y) :=
  fun m f hf => by simp [h m f hf]

section Mat

variable {n : Type*}

/-- Part of (M3) of `C46_smith_form_and_cokernel_over_Z2.md`: `magree_map`. -/
lemma magree_map {G H : Matrix n n (Bf A)} (h : MAgree G H) :
    MAgree (G.map (Bf.map φ)) (H.map (Bf.map φ)) := fun s s' => agree_map φ (h s s')

/-- Part of (M3) of `C46_smith_form_and_cokernel_over_Z2.md`: `map_eq_mapMatrix`. -/
lemma map_eq_mapMatrix {F : Bf A →+* Bf A'} (hF : ∀ x, F x = Bf.map φ x) [Fintype n]
    [DecidableEq n] (G : Matrix n n (Bf A)) : G.map (Bf.map φ) = F.mapMatrix G := by
  ext s s'; simp [hF]

/-- Part of (M3) of `C46_smith_form_and_cokernel_over_Z2.md`: `matrix_map_mul`. -/
lemma matrix_map_mul [Fintype n] [DecidableEq n] (G H : Matrix n n (Bf A)) :
    (G * H).map (Bf.map φ) = G.map (Bf.map φ) * H.map (Bf.map φ) := by
  obtain ⟨F, hF⟩ := Bf.exists_ringHom φ
  simp only [map_eq_mapMatrix φ hF, map_mul]

/-- Part of (M3) of `C46_smith_form_and_cokernel_over_Z2.md`: `matrix_map_add`. -/
lemma matrix_map_add (G H : Matrix n n (Bf A)) :
    (G + H).map (Bf.map φ) = G.map (Bf.map φ) + H.map (Bf.map φ) := by
  ext s s'; simp [Bf.map_add]

/-- Part of (M3) of `C46_smith_form_and_cokernel_over_Z2.md`: `matrix_map_sub`. -/
lemma matrix_map_sub (G H : Matrix n n (Bf A)) :
    (G - H).map (Bf.map φ) = G.map (Bf.map φ) - H.map (Bf.map φ) := by
  ext s s' m f; simp

/-- Part of (M3) of `C46_smith_form_and_cokernel_over_Z2.md`: `matrix_map_one`. -/
lemma matrix_map_one [DecidableEq n] : (1 : Matrix n n (Bf A)).map (Bf.map φ) = 1 :=
  Matrix.map_one _ (Bf.map_zero φ) (Bf.map_one φ)

/-- Part of (M3) of `C46_smith_form_and_cokernel_over_Z2.md`: `matrix_map_two_smul`. -/
lemma matrix_map_two_smul (G : Matrix n n (Bf A)) :
    ((2 : A) • G).map (Bf.map φ) = (2 : A') • G.map (Bf.map φ) := by
  ext s s' m f; simp [map_ofNat]

/-- Part of (M3) of `C46_smith_form_and_cokernel_over_Z2.md`: `twP_map`. -/
lemma twP_map [OddUnits A] (G : Matrix n n (Bf A)) :
    (twP G).map (Bf.map φ) = twP (G.map (Bf.map φ)) := by
  funext s s'; exact tw10_map φ _

/-- Part of (M3) of `C46_smith_form_and_cokernel_over_Z2.md`: `twC_map`. -/
lemma twC_map [OddUnits A] (G : Matrix n n (Bf A)) :
    (twC G).map (Bf.map φ) = twC (G.map (Bf.map φ)) := by
  funext s s'; exact tw11_map φ _

/-- Part of (M3) of `C46_smith_form_and_cokernel_over_Z2.md`: `twB_map`. -/
lemma twB_map [OddUnits A] (G : Matrix n n (Bf A)) :
    (twB G).map (Bf.map φ) = twB (G.map (Bf.map φ)) := by
  funext s s'; exact tw00_map φ _

/-- Part of (M3) of `C46_smith_form_and_cokernel_over_Z2.md`: `twD_map`. -/
lemma twD_map [OddUnits A] (G : Matrix n n (Bf A)) :
    (twD G).map (Bf.map φ) = twD (G.map (Bf.map φ)) := by
  funext s s'; exact tw01_map φ _

/-- Part of (M3) of `C46_smith_form_and_cokernel_over_Z2.md`: `vsplit_map`. -/
lemma vsplit_map (G : Matrix n n (Bf A)) :
    (vsplit G).map (Bf.map φ) = vsplit (G.map (Bf.map φ)) := by
  funext q q'
  simp only [Matrix.map_apply, vsplit]
  split_ifs
  · rfl
  · exact vprime_map φ _
  · exact vplus_map φ _
  · exact Bf.map_zero φ

end Mat

/-- **(M3)** of `C46_smith_form_and_cokernel_over_Z2.md`: `Agree` is preserved by `Bf.map φ`;
for matrices (mapped entrywise, `G.map (Bf.map φ)`) products and sums commute with the map,
`MAgree` is preserved, `vsplit` commutes with the map, and
`((2 : A) • G).map (Bf.map φ) = (2 : A') • G.map (Bf.map φ)`; under the hypothesis `[OddUnits A]`
of (M2) (needed for the factors `dfi` of the twist map), `twP`, `twC`, `twB`, `twD` commute with
the map. -/
theorem M3 :
    (∀ x y : Bf A, Agree x y → Agree (Bf.map φ x) (Bf.map φ y)) ∧
    (∀ (n : Type) [Fintype n] [DecidableEq n] (G H : Matrix n n (Bf A)),
      (G * H).map (Bf.map φ) = G.map (Bf.map φ) * H.map (Bf.map φ) ∧
      (G + H).map (Bf.map φ) = G.map (Bf.map φ) + H.map (Bf.map φ) ∧
      (MAgree G H → MAgree (G.map (Bf.map φ)) (H.map (Bf.map φ))) ∧
      (vsplit G).map (Bf.map φ) = vsplit (G.map (Bf.map φ)) ∧
      ((2 : A) • G).map (Bf.map φ) = (2 : A') • G.map (Bf.map φ)) ∧
    ([OddUnits A] → ∀ (n : Type) (G : Matrix n n (Bf A)),
      (twP G).map (Bf.map φ) = twP (G.map (Bf.map φ)) ∧
      (twC G).map (Bf.map φ) = twC (G.map (Bf.map φ)) ∧
      (twB G).map (Bf.map φ) = twB (G.map (Bf.map φ)) ∧
      (twD G).map (Bf.map φ) = twD (G.map (Bf.map φ))) :=
  ⟨fun _ _ => agree_map φ,
    fun _ _ _ G H => ⟨matrix_map_mul φ G H, matrix_map_add φ G H, magree_map φ,
      vsplit_map φ G, matrix_map_two_smul φ G⟩,
    fun _ G => ⟨twP_map φ G, twC_map φ G, twB_map φ G, twD_map φ G⟩⟩

/-! ### (M4) -/

/-- Part of (M4) of `C46_smith_form_and_cokernel_over_Z2.md`: `cleanStep_map`. -/
lemma cleanStep_map [OddUnits A] {n : Type*} [Fintype n] [DecidableEq n]
    {G G' : Matrix n n (Bf A)} (h : CleanStep G G') :
    CleanStep (G.map (Bf.map φ)) (G'.map (Bf.map φ)) := by
  obtain ⟨Q, h1, h2, h3⟩ := h
  refine ⟨Q.map (Bf.map φ), ?_, ?_, ?_⟩
  · have := magree_map φ h1
    rwa [matrix_map_mul, twP_map, matrix_map_one] at this
  · have := magree_map φ h2
    rwa [matrix_map_mul, twP_map, matrix_map_one] at this
  · have := magree_map φ h3
    rwa [matrix_map_sub, matrix_map_mul, matrix_map_mul, twD_map, twB_map, twC_map,
      matrix_map_two_smul] at this

/-- Part of (M4) of `C46_smith_form_and_cokernel_over_Z2.md`: `danceRel_map`. -/
lemma danceRel_map [OddUnits A] (ds : List Bool) :
    ∀ (r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf A))
      (Gk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf A)),
      DanceRel ds r G Gk → DanceRel ds r (G.map (Bf.map φ)) (Gk.map (Bf.map φ)) := by
  induction ds with
  | nil => intro r G Gk h; exact magree_map φ h
  | cons d rest ih =>
    cases d
    · rintro r G Gk ⟨G', h1, h2⟩
      exact ⟨G'.map (Bf.map φ), cleanStep_map φ h1, ih r G' Gk h2⟩
    · rintro r G Gk ⟨G'', h1, h2⟩
      refine ⟨G''.map (Bf.map φ), ?_, ih (r * 2) _ Gk h2⟩
      rw [← vsplit_map]
      exact cleanStep_map φ h1

/-- Part of (M4) of `C46_smith_form_and_cokernel_over_Z2.md`: `finalM_map`. -/
lemma finalM_map {m : Type*} (Gk : Matrix m m (Bf A)) :
    finalM (Gk.map (Bf.map φ)) = (finalM Gk).map φ := rfl

/-- **(M4)** of `C46_smith_form_and_cokernel_over_Z2.md`: if `[OddUnits A]`,
`CleanStep G G' → CleanStep (G.map (Bf.map φ)) (G'.map (Bf.map φ))`,
`DanceRel ds r G Gk → DanceRel ds r (G.map (Bf.map φ)) (Gk.map (Bf.map φ))`, and
`finalM (Gk.map (Bf.map φ)) = (finalM Gk).map φ`. -/
theorem M4 [OddUnits A] :
    (∀ (n : Type) [Fintype n] [DecidableEq n] (G G' : Matrix n n (Bf A)),
      CleanStep G G' → CleanStep (G.map (Bf.map φ)) (G'.map (Bf.map φ))) ∧
    (∀ (ds : List Bool) (r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf A))
      (Gk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf A)),
      DanceRel ds r G Gk → DanceRel ds r (G.map (Bf.map φ)) (Gk.map (Bf.map φ))) ∧
    (∀ (m : Type) (Gk : Matrix m m (Bf A)), finalM (Gk.map (Bf.map φ)) = (finalM Gk).map φ) :=
  ⟨fun _ _ _ _ _ h => cleanStep_map φ h, fun ds => danceRel_map φ ds,
    fun _ Gk => finalM_map φ Gk⟩

/-! ### (M5) -/

/-- Part of (M5) of `C46_smith_form_and_cokernel_over_Z2.md`: `map_ext0`. -/
lemma map_ext0 (q : ℕ → A) (f : ℤ) : φ (ext0 q f) = ext0 (fun k => φ (q k)) f := by
  unfold ext0; split_ifs <;> simp

/-- Part of (M5) of `C46_smith_form_and_cokernel_over_Z2.md`: `paySys_map`. -/
lemma paySys_map {n : Type*} [LinearOrder n] (p : n → ℕ → A) (κ : n → n → ℕ → A) :
    (paySys p κ).map (Bf.map φ) = paySys (fun s f => φ (p s f)) (fun s s' f => φ (κ s s' f)) := by
  have hdg : ∀ q : ℕ → A, Bf.dg (φ ∘ ext0 q) = Bf.dg (ext0 fun k => φ (q k)) := by
    intro q; congr 1; funext f; exact map_ext0 φ q f
  funext s s'
  simp only [Matrix.map_apply, paySys]
  split_ifs
  · rw [Bf.map_add, Bf.map_fd, Bf.map_dg, hdg]; simp [map_ofNat]
  · rw [Bf.map_dg, hdg]; simp [map_ofNat]
  · exact Bf.map_zero φ

/-- **(M5)** of `C46_smith_form_and_cokernel_over_Z2.md`: with `ι : ℤ_[2] →+* ℚ_[2]` the
coercion (Mathlib's `PadicInt.Coe.ringHom`),
`Bf.map ι (XiOpZ α c η ζ) = PathSum.XiOp α c (η : ℚ_[2]) (fun j f => (ζ j f : ℚ_[2]))` and
`(paySys (Dance.pσ (A := ℤ_[2]) α c) Dance.κσ).map (Bf.map ι) =
paySys (Dance.pσ (A := ℚ_[2]) α c) Dance.κσ`. -/
theorem M5 (α c : ℕ) (η : ℤ_[2]) (ζ : ℕ → ℤ → ℤ_[2]) :
    Bf.map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]) (XiOpZ α c η ζ) =
      PathSum.XiOp α c (η : ℚ_[2]) (fun j f => (ζ j f : ℚ_[2])) ∧
    (paySys (Dance.pσ (A := ℤ_[2]) α c) Dance.κσ).map
        (Bf.map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])) =
      paySys (Dance.pσ (A := ℚ_[2]) α c) Dance.κσ := by
  refine ⟨?_, ?_⟩
  · ext m f
    simp only [Bf.coef_map, XiOpZ, PathSum.XiOp, PathSum.piF]
    split_ifs
    · simp only [map_mul, map_pow, map_add, map_intCast, map_natCast, map_ofNat]
    · rfl
    · rfl
  · rw [paySys_map]
    congr 1

end Smith2
