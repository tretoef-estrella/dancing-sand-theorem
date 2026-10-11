import RequestProject.InvBlock.All

/-! Auditor's check file for Lean piece C41, Lemma 10.8 the inverse block (Grepy Escribano,
9 Oct 2026). Restated by hand from `C41_inverse_block.md`: inj₀, out₁, lift by `rfl`; the types of
inH, outH; (V1)–(V5) with the file's statements (V1, V2 without the unused half of the clean step,
as Aristotle noted); then `#print axioms`. -/

open DPLattice Doubling Filt FormalOps FormalDance FormalAct InvBlock
open scoped Pointwise

section defs
variable {A : Type} [CommRing A]
example {n ι : Type} (x : n → ι → A) : inj0 x = pack (x, 0) := rfl
example {n ι : Type} (w : n → Fin 2 × ι → A) : out1 w = (pack.symm w).2 := rfl
example {n : Type} [Fintype n] (N : DPLattice A) (W : ℤ) (B' : ℕ) (Q G : Matrix n n (Bf A))
    (v : n → N.ι → A) :
    lift N W B' Q G v = pack (-sysAct N W B' (Q * twC G) v, v) := rfl
end defs

section main
variable {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A]

noncomputable example (l r : ℕ) :
    (Fin (Dance.slots (Families.ds l) r) → A) →ₗ[A] (Fin r → (T A l).ι → A) := inH l r
noncomputable example (l r : ℕ) :
    (Fin r → (T A l).ι → A) →ₗ[A] (Fin (Dance.slots (Families.ds l) r) → A) := outH l r

-- (V1)
example {n : Type} [Fintype n] [DecidableEq n] {N : DPLattice A} {W : ℤ} {BN B B' : ℕ}
    (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (hnil : ∀ s ≥ BN, N.Fd s = 0)
    (hB : 2 * BN ≤ B) (hB' : BN ≤ B') (hB1 : 1 ≤ B') {G G' Q : Matrix n n (Bf A)}
    (hPQ : MAgree (twP G * Q) 1) (hS : MAgree (twD G - twB G * Q * twC G) ((2 : A) • G'))
    (v : n → N.ι → A) :
    sysAct (phi N) (2 * W + 1) B G (pack (-sysAct N W B' (Q * twC G) v, v)) =
        pack ((2 : A) • sysAct N W B' G' v, 0) ∧
      (pack.symm (pack (-sysAct N W B' (Q * twC G) v, v) : n → Fin 2 × N.ι → A)).2 = v :=
  V1 htop hnil hB hB' hB1 hPQ hS v

-- (V2)
example {n : Type} [Fintype n] [DecidableEq n] {N : DPLattice A} {W : ℤ} {BN B B' : ℕ}
    (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (hnil : ∀ s ≥ BN, N.Fd s = 0)
    (hB : 2 * BN + 1 ≤ B) (hB' : BN ≤ B') (hB1 : 1 ≤ B') {G : Matrix n n (Bf A)}
    {G'' Q : Matrix (n × Fin 2) (n × Fin 2) (Bf A)}
    (hPQ : MAgree (twP (vsplit G) * Q) 1)
    (hS : MAgree (twD (vsplit G) - twB (vsplit G) * Q * twC (vsplit G)) ((2 : A) • G''))
    (v : n × Fin 2 → N.ι → A) :
    sysAct (tensorV (phi N)) (2 * W + 2) B G
        (vpack (pack (-sysAct N W B' (Q * twC (vsplit G)) v, v) : n × Fin 2 → (phi N).ι → A)) =
        vpack (pack ((2 : A) • sysAct N W B' G'' v, 0) : n × Fin 2 → (phi N).ι → A) ∧
      (pack.symm (vpack.symm (vpack (pack (-sysAct N W B' (Q * twC (vsplit G)) v, v) :
        n × Fin 2 → (phi N).ι → A)))).2 = v :=
  V2 htop hnil hB hB' hB1 hPQ hS v

-- (V3)
example (l r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf A))
    (Gk : Matrix (Fin (Dance.slots (Families.ds l) r)) (Fin (Dance.slots (Families.ds l) r)) (Bf A))
    (hG : DanceRel (Families.ds l) r G Gk) (B : ℕ) (hB : l + 1 ≤ B) :
    ∃ L : (Fin (Dance.slots (Families.ds l) r) → A) →ₗ[A] (Fin r → (T A l).ι → A),
      sysAct (T A l) (l : ℤ) B G ∘ₗ L =
        (2 : A) ^ (Families.ds l).length • (inH l r ∘ₗ Matrix.mulVecLin (finalM Gk)) ∧
      outH l r ∘ₗ L = LinearMap.id :=
  V3 l r G Gk hG B hB

-- (V4)
example (l r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf A))
    (Gk : Matrix (Fin (Dance.slots (Families.ds l) r)) (Fin (Dance.slots (Families.ds l) r)) (Bf A))
    (hG : DanceRel (Families.ds l) r G Gk) (B : ℕ) (hB : l + 1 ≤ B)
    (hinj : Function.Injective (sysAct (T A l) (l : ℤ) B G)) :
    Function.Injective (Matrix.mulVecLin (finalM Gk)) :=
  V4 l r G Gk hG B hB hinj
end main

-- (V5)
example {K : Type} [Field K] [CharZero K] [OddUnits K] (l r : ℕ)
    (G : Matrix (Fin r) (Fin r) (Bf K))
    (Gk : Matrix (Fin (Dance.slots (Families.ds l) r)) (Fin (Dance.slots (Families.ds l) r)) (Bf K))
    (hG : DanceRel (Families.ds l) r G Gk) (B : ℕ) (hB : l + 1 ≤ B)
    (e : (Fin r → (T K l).ι → K) ≃ₗ[K] (Fin r → (T K l).ι → K))
    (he : (e : (Fin r → (T K l).ι → K) →ₗ[K] (Fin r → (T K l).ι → K)) =
      sysAct (T K l) (l : ℤ) B G) :
    IsUnit (finalM Gk).det ∧
      Matrix.mulVecLin ((finalM Gk)⁻¹) =
        (2 : K) ^ (Families.ds l).length •
          (outH l r ∘ₗ (e.symm : (Fin r → (T K l).ι → K) →ₗ[K] (Fin r → (T K l).ι → K)) ∘ₗ
            inH l r) :=
  V5 l r G Gk hG B hB e he

#print axioms InvBlock.V1
#print axioms InvBlock.V2
#print axioms InvBlock.V3
#print axioms InvBlock.V4
#print axioms InvBlock.V5
