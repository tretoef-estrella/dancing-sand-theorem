import RequestProject.Tensor2.All

/-! Auditor's check file for Lean piece C23 (Grepy Escribano, 7 Oct 2026).
Restated by hand from `C23_the_tensor_product.md`: the Kronecker product on basis vectors
(Setting); the tensor product (basis, weights, the coproduct of `F^{(r)}`, `E^{(r)}` written on
`δ_{(i,j)}` as a sum of products of coordinates, `IsDP`); (P2) `f ⊠ g` on basis vectors,
identities, composites, `tensorIso`; (P3) the identity maps; (P4), (P5), (P8) on basis vectors
both ways; (P6) `bvec e m ↦ bvec e (f m)`; (P7) blockwise; then `#print axioms`. -/

open Finset DPLattice WeylFilt Doubling Lemma35 Tensor2

variable {A : Type} [CommRing A]

-- Setting: (f ⊠ g)(δ_{(i,j)}) (i', j') = f(δ_i)(i') · g(δ_j)(j')
example {ι κ ι' κ' : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (f : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A)) (i : ι) (j : κ) (i' : ι')
    (j' : κ') :
    kron f g (Pi.single (i, j) 1) (i', j') = f (Pi.single i 1) i' * g (Pi.single j 1) j' :=
  kron_single_apply f g i j i' j'

-- (P1) basis, weights, the operators as sums of Kronecker products
example (M N : DPLattice A) : (tensor M N).ι = (M.ι × N.ι) := rfl
example (M N : DPLattice A) (i : M.ι) (j : N.ι) : (tensor M N).wt (i, j) = M.wt i + N.wt j := rfl
example (M N : DPLattice A) (r : ℕ) :
    (tensor M N).Fd r = ∑ a ∈ range (r + 1), kron (M.Fd a) (N.Fd (r - a)) := rfl
example (M N : DPLattice A) (r : ℕ) :
    (tensor M N).Ed r = ∑ a ∈ range (r + 1), kron (M.Ed a) (N.Ed (r - a)) := rfl
-- (P1) the coproduct on δ_{(i,j)}, written out coordinate by coordinate
example (M N : DPLattice A) (r : ℕ) (i : M.ι) (j : N.ι) :
    (tensor M N).Fd r (Pi.single (i, j) 1) =
      ∑ a ∈ range (r + 1), fun p : M.ι × N.ι =>
        M.Fd a (Pi.single i 1) p.1 * N.Fd (r - a) (Pi.single j 1) p.2 := by
  rw [single_prod_eq_tprod, tensor_Fd_tprod]; rfl
example (M N : DPLattice A) (r : ℕ) (i : M.ι) (j : N.ι) :
    (tensor M N).Ed r (Pi.single (i, j) 1) =
      ∑ a ∈ range (r + 1), fun p : M.ι × N.ι =>
        M.Ed a (Pi.single i 1) p.1 * N.Ed (r - a) (Pi.single j 1) p.2 := by
  rw [single_prod_eq_tprod, tensor_Ed_tprod]; rfl
-- (P1) IsDP: (W), (P0), (P1), (K)
example (M N : DPLattice A) :
    IsDP (fun p : M.ι × N.ι => M.wt p.1 + N.wt p.2)
      (fun r => ∑ a ∈ range (r + 1), kron (M.Fd a) (N.Fd (r - a)))
      (fun r => ∑ a ∈ range (r + 1), kron (M.Ed a) (N.Ed (r - a))) := tensor_isDP M N

-- (P2) f ⊠ g on basis vectors, identities, composites, tensorIso
example {M M' N N' : DPLattice A} (f : Hom M M') (g : Hom N N') (i : M.ι) (j : N.ι) (i' : M'.ι)
    (j' : N'.ι) : (kronHom f g).toLin (Pi.single (i, j) 1) (i', j') =
      f.toLin (Pi.single i 1) i' * g.toLin (Pi.single j 1) j' :=
  kronHom_single_apply f g i j i' j'
example (M N : DPLattice A) : kronHom (Hom.id M) (Hom.id N) = Hom.id (tensor M N) := kronHom_id
example {M M' M'' N N' N'' : DPLattice A} (f : Hom M' M'') (g : Hom N' N'') (f' : Hom M M')
    (g' : Hom N N') :
    kronHom (Hom.comp f f') (Hom.comp g g') = Hom.comp (kronHom f g) (kronHom f' g') :=
  kronHom_comp f g f' g'
example {M M' N N' : DPLattice A} (u : Iso M M') (v : Iso N N') :
    (tensorIso u v).hom.toLin = kron u.hom.toLin v.hom.toLin ∧
    (tensorIso u v).inv.toLin = kron u.inv.toLin v.inv.toLin := ⟨rfl, rfl⟩

-- (P3) tensorV M ≅ V A ⊗ M by the identity, both ways; same operators
example (M : DPLattice A) : (tensorVIsoTensor M).hom.toLin = LinearMap.id := rfl
example (M : DPLattice A) : (tensorVIsoTensor M).inv.toLin = LinearMap.id := rfl
example (M : DPLattice A) (r : ℕ) : (tensorV M).Fd r = (tensor (V A) M).Fd r := tensorV_Fd_eq M r
example (M : DPLattice A) (r : ℕ) : (tensorV M).Ed r = (tensor (V A) M).Ed r := tensorV_Ed_eq M r
example (M : DPLattice A) (e : Fin 2) (i : M.ι) : (tensorV M).wt (e, i) = (tensor (V A) M).wt (e, i) :=
  (P3 M).2.2.1 e i

-- (P4) on basis vectors, both ways
example (M N P : DPLattice A) (i : M.ι) (j : N.ι) (k : P.ι) :
    (assocIso M N P).hom.toLin (Pi.single ((i, j), k) 1) = Pi.single (i, (j, k)) 1 :=
  (P4 M N P).2.2.1 i j k
example (M N P : DPLattice A) (i : M.ι) (j : N.ι) (k : P.ι) :
    (assocIso M N P).inv.toLin (Pi.single (i, (j, k)) 1) = Pi.single ((i, j), k) 1 :=
  (P4 M N P).2.2.2 i j k

-- (P5) on basis vectors, both ways, both sides
example (M N P : DPLattice A) (i : M.ι) (k : P.ι) :
    (distribRightIso M N P).hom.toLin (Pi.single (Sum.inl i, k) 1) = Pi.single (Sum.inl (i, k)) 1 :=
  (P5 M N P).1.2.2.1 i k
example (M N P : DPLattice A) (j : N.ι) (k : P.ι) :
    (distribRightIso M N P).hom.toLin (Pi.single (Sum.inr j, k) 1) = Pi.single (Sum.inr (j, k)) 1 :=
  (P5 M N P).1.2.2.2.1 j k
example (M N P : DPLattice A) (j : N.ι) (k : P.ι) :
    (distribRightIso M N P).inv.toLin (Pi.single (Sum.inr (j, k)) 1) = Pi.single (Sum.inr j, k) 1 :=
  (P5 M N P).1.2.2.2.2.2 j k
example (M N P : DPLattice A) (i : M.ι) (j : N.ι) :
    (distribLeftIso M N P).hom.toLin (Pi.single (i, Sum.inl j) 1) = Pi.single (Sum.inl (i, j)) 1 :=
  (P5 M N P).2.2.2.1 i j
example (M N P : DPLattice A) (i : M.ι) (k : P.ι) :
    (distribLeftIso M N P).hom.toLin (Pi.single (i, Sum.inr k) 1) = Pi.single (Sum.inr (i, k)) 1 :=
  (P5 M N P).2.2.2.2.1 i k
example (M N P : DPLattice A) (i : M.ι) (j : N.ι) :
    (distribLeftIso M N P).inv.toLin (Pi.single (Sum.inl (i, j)) 1) = Pi.single (i, Sum.inl j) 1 :=
  (P5 M N P).2.2.2.2.2.1 i j

-- (P6) bvec e m ↦ bvec e (f m); identities, composites; tensorVIso
example {M N : DPLattice A} (f : Hom M N) (e : Fin 2) (m : M.ι → A) :
    (tensorVHom f).toLin (bvec e m) = bvec e (f.toLin m) := tensorVHom_bvec f e m
example (M : DPLattice A) : tensorVHom (Hom.id M) = Hom.id (tensorV M) := tensorVHom_id
example {M N P : DPLattice A} (g : Hom N P) (f : Hom M N) :
    tensorVHom (Hom.comp g f) = Hom.comp (tensorVHom g) (tensorVHom f) := tensorVHom_comp g f
example {M N : DPLattice A} (u : Iso M N) :
    (tensorVIso u).hom = tensorVHom u.hom ∧ (tensorVIso u).inv = tensorVHom u.inv := ⟨rfl, rfl⟩

-- (P7) blockwise
example {M M' N N' : DPLattice A} (u : Iso M M') (v : Iso N N') (z : M.ι ⊕ N.ι → A) :
    (dsumIso u v).hom.toLin z = Sum.elim (u.hom.toLin (z ∘ Sum.inl)) (v.hom.toLin (z ∘ Sum.inr)) :=
  (P7 u v).2.2.1 z

-- (P8) on basis vectors, both ways
example (M : DPLattice A) (i : M.ι) :
    (unitLeftIso M).hom.toLin (Pi.single ((), i) 1) = Pi.single i 1 := (P8 M).2.2.1 i
example (M : DPLattice A) (i : M.ι) :
    (unitLeftIso M).inv.toLin (Pi.single i 1) = Pi.single ((), i) 1 := (P8 M).2.2.2.1 i
example (M : DPLattice A) (i : M.ι) :
    (unitRightIso M).hom.toLin (Pi.single (i, ()) 1) = Pi.single i 1 := (P8 M).2.2.2.2.2.2.1 i
example (M : DPLattice A) (i : M.ι) :
    (unitRightIso M).inv.toLin (Pi.single i 1) = Pi.single (i, ()) 1 := (P8 M).2.2.2.2.2.2.2 i

#print axioms Tensor2.kron_single_apply
#print axioms Tensor2.tensor
#print axioms Tensor2.tensor_isDP
#print axioms Tensor2.P1
#print axioms Tensor2.tensor_Fd_tprod
#print axioms Tensor2.P2
#print axioms Tensor2.tensorIso
#print axioms Tensor2.P3
#print axioms Tensor2.tensorV_Fd_eq
#print axioms Tensor2.P4
#print axioms Tensor2.P5
#print axioms Tensor2.P6
#print axioms Tensor2.tensorVIso
#print axioms Tensor2.P7
#print axioms Tensor2.dsumIso
#print axioms Tensor2.P8
