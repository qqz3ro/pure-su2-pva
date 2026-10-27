module

public import KhanSL2.Factorization.WeightedRootModelPolynomialActions
public import KhanSL2.Factorization.WeightedRootModelBlockTensor
public import KhanSL2.SymmetricFamily.RootPolynomialBlock

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped TensorProduct
namespace KhanSL2.Macdonald
open SymmetricFamily Factorization.WeightedRootModel

/-- Literal restriction of the two labelled alphabets to the two weighted blocks. -/
def weightedRootPolynomialBlock (q₁ q₂ r₁ r₂ : ℕ) :
    LabelledWeightedRing (q₁+q₂) (r₁+r₂) →ₐ[ℂ]
      LabelledWeightedRing q₁ r₁ ⊗[ℂ] LabelledWeightedRing q₂ r₂ :=
  MvPolynomial.aeval (appendWeightedRoots
    (fun i => (MvPolynomial.X i : LabelledWeightedRing q₁ r₁) ⊗ₜ[ℂ] 1)
    (fun i => 1 ⊗ₜ[ℂ] (MvPolynomial.X i : LabelledWeightedRing q₂ r₂)))

@[simp] theorem weightedRootPolynomialBlock_X_first (q₁ q₂ r₁ r₂ : ℕ)
    (i : Fin q₁ ⊕ Fin r₁) :
    weightedRootPolynomialBlock q₁ q₂ r₁ r₂
      (MvPolynomial.X (firstWeightedInclusion q₁ q₂ r₁ r₂ i)) =
        (MvPolynomial.X i : LabelledWeightedRing q₁ r₁) ⊗ₜ[ℂ] 1 := by
  cases i <;> simp [weightedRootPolynomialBlock,LabelledWeightedRing,appendWeightedRoots,firstWeightedInclusion]

@[simp] theorem weightedRootPolynomialBlock_X_second (q₁ q₂ r₁ r₂ : ℕ)
    (i : Fin q₂ ⊕ Fin r₂) :
    weightedRootPolynomialBlock q₁ q₂ r₁ r₂
      (MvPolynomial.X (secondWeightedInclusion q₁ q₂ r₁ r₂ i)) =
        1 ⊗ₜ[ℂ] (MvPolynomial.X i : LabelledWeightedRing q₂ r₂) := by
  cases i <;> simp [weightedRootPolynomialBlock,LabelledWeightedRing,appendWeightedRoots,secondWeightedInclusion]

/-- Restriction on the odd alphabet is the ordinary literal root restriction. -/
theorem weightedRootPolynomialBlock_odd (q₁ q₂ r₁ r₂ : ℕ)
    (p : MvPolynomial (Fin (q₁+q₂)) ℂ) :
    weightedRootPolynomialBlock q₁ q₂ r₁ r₂ (MvPolynomial.rename Sum.inl p) =
      Algebra.TensorProduct.map
        (MvPolynomial.rename Sum.inl : _ →ₐ[ℂ] LabelledWeightedRing q₁ r₁)
        (MvPolynomial.rename Sum.inl : _ →ₐ[ℂ] LabelledWeightedRing q₂ r₂)
        (rootPolynomialBlock q₁ q₂ p) := by
  have h : (weightedRootPolynomialBlock q₁ q₂ r₁ r₂).comp (MvPolynomial.rename Sum.inl) =
      (Algebra.TensorProduct.map
        (MvPolynomial.rename Sum.inl : _ →ₐ[ℂ] LabelledWeightedRing q₁ r₁)
        (MvPolynomial.rename Sum.inl : _ →ₐ[ℂ] LabelledWeightedRing q₂ r₂)).comp
          (rootPolynomialBlock q₁ q₂) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [weightedRootPolynomialBlock,appendWeightedRoots,rootPolynomialBlock,LabelledWeightedRing,AlgHom.comp_apply]
  exact AlgHom.congr_fun h p

/-- Restriction on the even alphabet is the ordinary literal root restriction. -/
theorem weightedRootPolynomialBlock_even (q₁ q₂ r₁ r₂ : ℕ)
    (p : MvPolynomial (Fin (r₁+r₂)) ℂ) :
    weightedRootPolynomialBlock q₁ q₂ r₁ r₂ (MvPolynomial.rename Sum.inr p) =
      Algebra.TensorProduct.map
        (MvPolynomial.rename Sum.inr : _ →ₐ[ℂ] LabelledWeightedRing q₁ r₁)
        (MvPolynomial.rename Sum.inr : _ →ₐ[ℂ] LabelledWeightedRing q₂ r₂)
        (rootPolynomialBlock r₁ r₂ p) := by
  have h : (weightedRootPolynomialBlock q₁ q₂ r₁ r₂).comp (MvPolynomial.rename Sum.inr) =
      (Algebra.TensorProduct.map
        (MvPolynomial.rename Sum.inr : _ →ₐ[ℂ] LabelledWeightedRing q₁ r₁)
        (MvPolynomial.rename Sum.inr : _ →ₐ[ℂ] LabelledWeightedRing q₂ r₂)).comp
          (rootPolynomialBlock r₁ r₂) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [weightedRootPolynomialBlock,appendWeightedRoots,rootPolynomialBlock,LabelledWeightedRing,AlgHom.comp_apply]
  exact AlgHom.congr_fun h p

/-- Recombine separately restricted odd and even alphabets, preserving the factor order. -/
def weightedRootBlockReorder (q₁ q₂ r₁ r₂ : ℕ) :
    (MvPolynomial (Fin q₁) ℂ ⊗[ℂ] MvPolynomial (Fin q₂) ℂ) ⊗[ℂ]
      (MvPolynomial (Fin r₁) ℂ ⊗[ℂ] MvPolynomial (Fin r₂) ℂ) →ₗ[ℂ]
        LabelledWeightedRing q₁ r₁ ⊗[ℂ] LabelledWeightedRing q₂ r₂ :=
  (TensorProduct.map (rawTensorEquiv q₁ r₁).toLinearMap
    (rawTensorEquiv q₂ r₂).toLinearMap).comp
    (TensorProduct.tensorTensorTensorComm ℂ _ _ _ _).toLinearMap

theorem weightedRootBlockReorder_tmul (q₁ q₂ r₁ r₂ : ℕ)
    (u : MvPolynomial (Fin q₁) ℂ ⊗[ℂ] MvPolynomial (Fin q₂) ℂ)
    (v : MvPolynomial (Fin r₁) ℂ ⊗[ℂ] MvPolynomial (Fin r₂) ℂ) :
    weightedRootBlockReorder q₁ q₂ r₁ r₂ (u ⊗ₜ[ℂ] v) =
      Algebra.TensorProduct.map
        (MvPolynomial.rename Sum.inl : _ →ₐ[ℂ] LabelledWeightedRing q₁ r₁)
        (MvPolynomial.rename Sum.inl : _ →ₐ[ℂ] LabelledWeightedRing q₂ r₂) u *
      Algebra.TensorProduct.map
        (MvPolynomial.rename Sum.inr : _ →ₐ[ℂ] LabelledWeightedRing q₁ r₁)
        (MvPolynomial.rename Sum.inr : _ →ₐ[ℂ] LabelledWeightedRing q₂ r₂) v := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [TensorProduct.add_tmul,map_add,ha,hb,add_mul]
  | tmul a b =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd => simp only [TensorProduct.tmul_add,map_add,hc,hd,mul_add]
    | tmul c d =>
      simp [weightedRootBlockReorder,Algebra.TensorProduct.tmul_mul_tmul]

/-- The separate odd/even block maps are exactly the literal weighted-root restriction. -/
theorem weightedRootPolynomialBlock_product (q₁ q₂ r₁ r₂ : ℕ)
    (p : MvPolynomial (Fin (q₁+q₂)) ℂ) (t : MvPolynomial (Fin (r₁+r₂)) ℂ) :
    weightedRootPolynomialBlock q₁ q₂ r₁ r₂
      ((MvPolynomial.rename Sum.inl p : LabelledWeightedRing (q₁+q₂) (r₁+r₂)) *
        MvPolynomial.rename Sum.inr t) =
      weightedRootBlockReorder q₁ q₂ r₁ r₂
        (rootPolynomialBlock q₁ q₂ p ⊗ₜ[ℂ] rootPolynomialBlock r₁ r₂ t) := by
  rw [map_mul,weightedRootPolynomialBlock_odd,weightedRootPolynomialBlock_even,
    weightedRootBlockReorder_tmul]

end KhanSL2.Macdonald


