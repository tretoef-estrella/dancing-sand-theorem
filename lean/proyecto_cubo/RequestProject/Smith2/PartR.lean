module

public import RequestProject.Smith2.PartV
public import RequestProject.FormalProp.All
public import RequestProject.FamilyGroup.All

/-!
# `C46_smith_form_and_cokernel_over_Z2.md`, Part R — Theorem 10.12, second half

(R1) `R1`; (R2) `R2`; (R3) `R3`; (R4) `R4`; (R5) `R5`, all under the hypotheses (H) of Part V.

`T(l)` is C29's `Filt.T ℤ_[2] l` (written `T ℤ_[2] l` in the file), the action is C40c's
`FormalAct.sysAct (Filt.T ℤ_[2] l) l B G` on `Fin 1 → (Filt.T ℤ_[2] l).ι → ℤ_[2]`, and the
cokernel of a linear map `f` is `M ⧸ LinearMap.range f`, as in C40d.
-/

@[expose] public section

noncomputable section

namespace Smith2

open FormalOps FormalDance Windows DanceSmith Matrix Finset
open scoped Pointwise

/-- Proof of (R1), (R2) of `C46_smith_form_and_cokernel_over_Z2.md`: reindexing a Smith-type
identity along an equivalence of index types. -/
lemma smith_reindex {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : m ≃ n) {P X Q : Matrix m m R} {d : m → R}
    (h : P * X * Q = diagonal d) :
    P.submatrix e.symm e.symm * X.submatrix e.symm e.symm * Q.submatrix e.symm e.symm =
      diagonal (d ∘ e.symm) := by
  rw [submatrix_mul_equiv, submatrix_mul_equiv, h, submatrix_diagonal_equiv]

/-- (R2) of `C46_smith_form_and_cokernel_over_Z2.md` on `Fin (2 ^ m)`, for
`X = (finalM GkZ).submatrix cs cs` (proof of (R1), (R2)). -/
lemma R2_fin {l α c : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) (hc : 1 ≤ c) {η : ℤ_[2]} (hη : IsUnit η)
    (ζ : ℕ → ℤ → ℤ_[2])
    (GkZ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => XiOpZ α c η ζ) GkZ) :
    ∃ P Q : Matrix (Fin (2 ^ Dance.mCount (Families.ds l)))
        (Fin (2 ^ Dance.mCount (Families.ds l))) ℤ_[2],
      IsUnit P.det ∧ IsUnit Q.det ∧ ∃ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount (Families.ds l),
          (E j : ℤ) = Cst (Families.ds l) α c +
            yHat (Families.ds l) α c (2 ^ Dance.mCount (Families.ds l) - 1 - j)) ∧
        P * (finalM GkZ).submatrix (Fin.cast (slots_cast _)) (Fin.cast (slots_cast _)) * Q =
          diagonal (fun j : Fin (2 ^ Dance.mCount (Families.ds l)) => (2 : ℤ_[2]) ^ E j) := by
  have hk := Stability.length_ds_pos hl
  set X := (finalM GkZ).submatrix (Fin.cast (slots_cast (Families.ds l)))
    (Fin.cast (slots_cast (Families.ds l)))
  obtain ⟨N₀, hN₀⟩ := V2 hl hα hc hη ζ GkZ hG
  obtain ⟨hG1, hEb⟩ := hN₀ N₀ le_rfl
  obtain ⟨P, Q, hP, hQ, u, hu, E, hE, hD⟩ :=
    G1 (Families.ds l) hk α c (by omega) hc (trunc N₀ X) hG1
  have hXY : ∃ R : Matrix (Fin (2 ^ Dance.mCount (Families.ds l)))
      (Fin (2 ^ Dance.mCount (Families.ds l))) ℤ_[2],
      ∀ i j, X i j - (trunc N₀ X i j : ℤ_[2]) = 2 ^ N₀ * R i j :=
    ⟨fun i j => (Z0 (X i j) N₀).1.choose, fun i j => by
      have := (Z0 (X i j) N₀).1.choose_spec
      simp only [trunc]; push_cast; exact this⟩
  obtain ⟨P', Q', hP', hQ', hD'⟩ := Z1 X (trunc N₀ X) N₀ hXY P Q hP hQ u hu E (hEb E hE) hD
  exact ⟨P', Q', hP', hQ', E, hE, hD'⟩

/-- **(R2)** of `C46_smith_form_and_cokernel_over_Z2.md` (Smith form): under (H) there are `P, Q`
over `ℤ_[2]` with unit determinants and `E : ℕ → ℕ` with
`(E j : ℤ) = Cst ds α c + yHat ds α c (N − 1 − j)` for `j < N`, such that
`P * finalM GkZ * Q = diagonal (fun j => (2 : ℤ_[2]) ^ E j)`. -/
theorem R2 {l α c : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) (hc : 1 ≤ c) {η : ℤ_[2]} (hη : IsUnit η)
    (ζ : ℕ → ℤ → ℤ_[2])
    (GkZ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => XiOpZ α c η ζ) GkZ) :
    ∃ P Q : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
        ℤ_[2],
      IsUnit P.det ∧ IsUnit Q.det ∧ ∃ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount (Families.ds l),
          (E j : ℤ) = Cst (Families.ds l) α c +
            yHat (Families.ds l) α c (2 ^ Dance.mCount (Families.ds l) - 1 - j)) ∧
        P * finalM GkZ * Q =
          diagonal (fun j : Fin (Dance.slots (Families.ds l) 1) => (2 : ℤ_[2]) ^ E j) := by
  obtain ⟨P, Q, hP, hQ, E, hE, hD⟩ := R2_fin hl hα hc hη ζ GkZ hG
  set e := finCongr (slots_cast (Families.ds l))
  refine ⟨P.submatrix e.symm e.symm, Q.submatrix e.symm e.symm,
    by rw [det_submatrix_equiv_self]; exact hP, by rw [det_submatrix_equiv_self]; exact hQ,
    E, hE, ?_⟩
  have h := smith_reindex e hD
  have hX : ((finalM GkZ).submatrix (Fin.cast (slots_cast _)) (Fin.cast (slots_cast _))).submatrix
      e.symm e.symm = finalM GkZ := by
    ext s s'; rfl
  rw [hX] at h
  rw [h]; rfl

/-- **(R1)** of `C46_smith_form_and_cokernel_over_Z2.md`: under (H), for every `GkS` with
`DanceRel ds 1 (paySys (Dance.pσ (A := ℤ_[2]) α c) Dance.κσ) GkS` there are `P Q` over `ℤ_[2]`
with unit determinants and `finalM GkZ = P * finalM GkS * Q`. -/
theorem R1 {l α c : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) (hc : 1 ≤ c) {η : ℤ_[2]} (hη : IsUnit η)
    (ζ : ℕ → ℤ → ℤ_[2])
    (GkZ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => XiOpZ α c η ζ) GkZ) :
    ∀ GkS : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
        (Bf ℤ_[2]),
      DanceRel (Families.ds l) 1 (paySys (Dance.pσ (A := ℤ_[2]) α c) Dance.κσ) GkS →
      ∃ P Q : Matrix (Fin (Dance.slots (Families.ds l) 1))
          (Fin (Dance.slots (Families.ds l) 1)) ℤ_[2],
        IsUnit P.det ∧ IsUnit Q.det ∧ finalM GkZ = P * finalM GkS * Q := by
  intro GkS hS
  have hk := Stability.length_ds_pos hl
  set e := finCongr (slots_cast (Families.ds l))
  set ι := Int.castRingHom ℤ_[2]
  -- the final matrix of `Σ` is the image of the integer dance matrix
  obtain ⟨hw, hwM⟩ := L4_sigma (A := ℤ_[2]) (Families.ds l) α c
  have h2 : ∀ a : ℤ_[2], 2 * a = 0 → a = 0 := fun a h => by
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hSw := (L5 h2 hS hw).2
  have hY : finalM GkS = ((finalMatrix ℤ (Families.ds l) α c).map ι).submatrix e.symm e.symm := by
    rw [hSw, ← finalMatrix_eq_map]
    ext t t'
    have := hwM (Fin.cast (one_mul _).symm (e.symm t)) (Fin.cast (one_mul _).symm (e.symm t'))
    exact this
  -- Smith form of the integer dance matrix, over `ℤ_[2]`
  obtain ⟨P, Q, hP, hQ, u, hu, E, hE, hD⟩ := S3 (Families.ds l) hk α c (by omega) hc
  obtain ⟨P₁, Q₁, hP₁, hQ₁, hD₁⟩ := Z1 ((finalMatrix ℤ (Families.ds l) α c).map ι)
    (finalMatrix ℤ (Families.ds l) α c)
    ((univ.sup fun j : Fin (2 ^ Dance.mCount (Families.ds l)) => E j) + 1)
    ⟨0, fun i j => by simp [ι]⟩ P Q hP hQ u hu E
    (fun j hj => Nat.lt_succ_of_le
      (le_sup (f := fun j : Fin (2 ^ Dance.mCount (Families.ds l)) => E j)
      (mem_univ ⟨j, hj⟩))) hD
  -- Smith form of `Ξ`
  obtain ⟨P₂, Q₂, hP₂, hQ₂, E₂, hE₂, hD₂⟩ := R2_fin hl hα hc hη ζ GkZ hG
  have hEE : (fun j : Fin (2 ^ Dance.mCount (Families.ds l)) => (2 : ℤ_[2]) ^ E₂ j) =
      fun j : Fin (2 ^ Dance.mCount (Families.ds l)) => (2 : ℤ_[2]) ^ E j := by
    funext j
    have : (E₂ j : ℤ) = E j := (hE₂ j j.2).trans (hE j j.2).symm
    rw [show E₂ j = E j by exact_mod_cast this]
  rw [hEE] at hD₂
  obtain ⟨P₃, Q₃, hP₃, hQ₃, hX⟩ := Z2 hD₁ hD₂ hP₁ hQ₁ hP₂ hQ₂
  refine ⟨P₃.submatrix e.symm e.symm, Q₃.submatrix e.symm e.symm,
    by rw [det_submatrix_equiv_self]; exact hP₃, by rw [det_submatrix_equiv_self]; exact hQ₃, ?_⟩
  rw [hY, submatrix_mul_equiv, submatrix_mul_equiv, ← hX]
  ext s s'; rfl

/-- **(R3)** of `C46_smith_form_and_cokernel_over_Z2.md` («`coker Ξ ≅ coker Σ`»): under (H), for
every `B ≥ l + 1` and every `h`, the cokernel of
`(2 : ℤ_[2]) ^ h • sysAct (T ℤ_[2] l) l B (fun _ _ => XiOpZ α c η ζ)` is isomorphic to the
cokernel of `(2 : ℤ_[2]) ^ h • sysAct (T ℤ_[2] l) l B (paySys (Dance.pσ α c) Dance.κσ)` (both on
`Fin 1 → (T ℤ_[2] l).ι → ℤ_[2]`). -/
theorem R3 {l α c : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) (hc : 1 ≤ c) {η : ℤ_[2]} (hη : IsUnit η)
    (ζ : ℕ → ℤ → ℤ_[2])
    (GkZ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => XiOpZ α c η ζ) GkZ) :
    ∀ B : ℕ, l + 1 ≤ B → ∀ h : ℕ,
      Nonempty (((Fin 1 → (Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
          LinearMap.range ((2 : ℤ_[2]) ^ h • FormalAct.sysAct (Filt.T ℤ_[2] l) (l : ℤ) B
            (fun _ _ => XiOpZ α c η ζ : Matrix (Fin 1) (Fin 1) (Bf ℤ_[2])))) ≃ₗ[ℤ_[2]]
        ((Fin 1 → (Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
          LinearMap.range ((2 : ℤ_[2]) ^ h • FormalAct.sysAct (Filt.T ℤ_[2] l) (l : ℤ) B
            (paySys (Dance.pσ (A := ℤ_[2]) α c) Dance.κσ)))) := by
  intro B hB h
  obtain ⟨hw, -⟩ := L4_sigma (A := ℤ_[2]) (Families.ds l) α c
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := R1 hl hα hc hη ζ GkZ hG _ hw
  obtain ⟨e⟩ := FormalProp.Q3 l 1 hw hG P Q hP hQ hPQ B hB h
  exact ⟨e.symm⟩

/-- **(R4)** of `C46_smith_form_and_cokernel_over_Z2.md`: under (H), for every `B ≥ l + 1` there
is `E : ℕ → ℕ` with `(E p : ℤ) = k + Cst ds α c + yHat ds α c p` for `p < N`, and the cokernel of
`sysAct (T ℤ_[2] l) l B (fun _ _ => XiOpZ α c η ζ)` is isomorphic to
`FamilyGroup.SC ds × ((p : Fin (2 ^ m)) → FamilyGroup.Q (E p))`. -/
theorem R4 {l α c : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) (hc : 1 ≤ c) {η : ℤ_[2]} (hη : IsUnit η)
    (ζ : ℕ → ℤ → ℤ_[2])
    (GkZ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => XiOpZ α c η ζ) GkZ) :
    ∀ B : ℕ, l + 1 ≤ B →
      ∃ E : ℕ → ℕ, (∀ p < 2 ^ Dance.mCount (Families.ds l),
          (E p : ℤ) = (Families.ds l).length + Cst (Families.ds l) α c +
            yHat (Families.ds l) α c p) ∧
        Nonempty (((Fin 1 → (Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
            LinearMap.range (FormalAct.sysAct (Filt.T ℤ_[2] l) (l : ℤ) B
              (fun _ _ => XiOpZ α c η ζ : Matrix (Fin 1) (Fin 1) (Bf ℤ_[2])))) ≃ₗ[ℤ_[2]]
          FamilyGroup.SC (Families.ds l) ×
            ((p : Fin (2 ^ Dance.mCount (Families.ds l))) → FamilyGroup.Q (E p))) := by
  intro B hB
  set k := (Families.ds l).length
  set M := 2 ^ Dance.mCount (Families.ds l)
  obtain ⟨P, Q, hP, hQ, E, hE, hD⟩ := R2 hl hα hc hη ζ GkZ hG
  refine ⟨fun p => k + E (M - 1 - p), fun p hp => ?_, ?_⟩
  · rw [Nat.cast_add, hE _ (by omega), show M - 1 - (M - 1 - p) = p by omega]
    ring
  obtain ⟨e1⟩ := FormalProp.Q1 l 1 _ GkZ hG B hB 0
  rw [pow_zero, one_smul, zero_add] at e1
  obtain ⟨e2⟩ := FamilyGroup.L2 ((2 : ℤ_[2]) ^ k) (finalM GkZ) P Q
    (fun j => (2 : ℤ_[2]) ^ E j) hP hQ hD
  rw [Matrix.toLin'_apply'] at e2
  obtain ⟨e3⟩ := FamilyGroup.piQuotReindex (R := ℤ_[2])
    (fun j : Fin (Dance.slots (Families.ds l) 1) => (2 : ℤ_[2]) ^ k * 2 ^ E j)
    (fun p : Fin M => (2 : ℤ_[2]) ^ (k + E (M - 1 - p)))
    ((Fin.revPerm (n := M)).trans (finCongr (slots_cast (Families.ds l))))
    (fun p => by
      simp only [Equiv.trans_apply, Fin.revPerm_apply, finCongr_apply, Fin.val_cast,
        Fin.val_rev]
      rw [← pow_add, show M - (p + 1) = M - 1 - p by omega])
  have e0 : ((a : Fin k) → (Fin (1 * 2 ^ (k + Dance.mCount (Families.ds l) - 1 - a)) → ℤ_[2]) ⧸
      (2 : ℤ_[2]) ^ (0 + (a : ℕ)) • (⊤ : Submodule ℤ_[2]
        (Fin (1 * 2 ^ (k + Dance.mCount (Families.ds l) - 1 - a)) → ℤ_[2]))) ≃ₗ[ℤ_[2]]
      FamilyGroup.SC (Families.ds l) :=
    LinearEquiv.piCongrRight fun a => Dance.pqCast (A := ℤ_[2]) (one_mul _) (zero_add _)
  exact ⟨e1.trans (LinearEquiv.prodCongr e0 (e2.trans e3))⟩

/-- **(R5)** of `C46_smith_form_and_cokernel_over_Z2.md` («`coker(Ξ on T(l)) ≅ X^{(α)}(l, c)`»):
under (H), for every `B ≥ l + 1` the cokernel of
`sysAct (T ℤ_[2] l) l B (fun _ _ => XiOpZ α c η ζ)` is isomorphic to `FamilyGroup.X ds α c`. -/
theorem R5 {l α c : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) (hc : 1 ≤ c) {η : ℤ_[2]} (hη : IsUnit η)
    (ζ : ℕ → ℤ → ℤ_[2])
    (GkZ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => XiOpZ α c η ζ) GkZ) :
    ∀ B : ℕ, l + 1 ≤ B →
      Nonempty (((Fin 1 → (Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
          LinearMap.range (FormalAct.sysAct (Filt.T ℤ_[2] l) (l : ℤ) B
            (fun _ _ => XiOpZ α c η ζ : Matrix (Fin 1) (Fin 1) (Bf ℤ_[2])))) ≃ₗ[ℤ_[2]]
        FamilyGroup.X (Families.ds l) α c) := by
  intro B hB
  have hk := Stability.length_ds_pos hl
  obtain ⟨E, hE, ⟨e⟩⟩ := R4 hl hα hc hη ζ GkZ hG B hB
  obtain ⟨E', hE', ⟨e'⟩⟩ := FamilyGroup.X1 (Families.ds l) hk α c (by omega) hc
  have hEE : ∀ p : Fin (2 ^ Dance.mCount (Families.ds l)), E p = E' p := fun p => by
    have : (E p : ℤ) = E' p := (hE p p.2).trans (hE' p p.2).symm
    exact_mod_cast this
  exact ⟨e.trans ((LinearEquiv.prodCongr (LinearEquiv.refl _ _)
    (LinearEquiv.piCongrRight fun p => Submodule.quotEquivOfEq _ _ (by rw [hEE p]))).trans
      e'.symm)⟩

end Smith2
