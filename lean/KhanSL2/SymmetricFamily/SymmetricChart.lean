module

public import KhanSL2.SymmetricFamily.ColoredBlockTensor

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! The original symmetric coefficient family on a coprime chart is isomorphic
to the tensor product of its two original factor specializations. The map is
actual first-block root restriction, followed by the normalized invariant sections. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Macdonald Factorization
open scoped FactorRootScalars

/-- Fixed vectors are unchanged when a group-indexed family is reindexed by inversion. -/
def fixedOperatorsInverseEquiv {R M G : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Group G] (ρ : G → Module.End R M) :
    fixedOperators ρ ≃ₗ[R] FiberTransport.fixedVectors (fun g => ρ g⁻¹) where
  toFun x := ⟨x.val,fun g => x.property g⁻¹⟩
  invFun x := ⟨x.val,fun g => by simpa only [inv_inv] using x.property g⁻¹⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB (r+s)) A]

/-- Exact first-block restriction identifies original coefficient sections with the
product-group invariant subspace of the two colored factor tensors. -/
def symmetricChartFixedEquiv (c : Collision.ChartData (r+s) r s A) :
    CoefficientBaseChange (Depth.RB (r+s)) (symmetricPower (r+s)) A ≃ₗ[A]
      FiberTransport.fixedVectors (R:=A) (V:=FactorColors r c.f₁ ⊗[A] FactorColors s c.f₂) (fun g =>
        FiberTransport.tensorAction (factorLabelledRepresentation r c.f₁)
          (factorLabelledRepresentation s c.f₂) g) :=
  (((symmetricBaseChangedLabelledEquiv (r+s) A).trans
    (fixedOperatorsInverseEquiv (baseLabelledPermute (r+s) A))).trans
      (coloredAssignmentStabilizerEquiv (r+s) A c (firstBlock r s))).trans
    (FiberTransport.stabilizerFixedCongr (V:=FactorColors r c.f₁ ⊗[A] FactorColors s c.f₂) (coloredAssignmentTransport (r+s) A c) (firstBlock r s)
      (blockPermutationHom r s) (blockPermutation_firstBlock r s)
      (fun σ hσ => by
        obtain ⟨g,hg⟩ := (blockStabilizerEquiv r s).surjective ⟨σ,hσ⟩
        exact ⟨g,congrArg Subtype.val hg⟩)
      (fun g => FiberTransport.tensorAction (factorLabelledRepresentation r c.f₁)
        (factorLabelledRepresentation s c.f₂) g)
      (coloredBlockTensorEquiv c) (coloredBlockTensorEquiv_permute c))

/-- Independent normalized averaging on the two factor permutation groups. -/
def factorTensorFixedEquiv (c : Collision.ChartData (r+s) r s A) :
    (FiberTransport.fixedVectors (fun σ => factorLabelledRepresentation r c.f₁ σ) ⊗[A]
      FiberTransport.fixedVectors (fun σ => factorLabelledRepresentation s c.f₂ σ)) ≃ₗ[A]
      FiberTransport.fixedVectors (R:=A) (V:=FactorColors r c.f₁ ⊗[A] FactorColors s c.f₂) (fun g =>
        FiberTransport.tensorAction (factorLabelledRepresentation r c.f₁)
          (factorLabelledRepresentation s c.f₂) g) :=
  FiberTransport.tensorFixedEquiv (factorLabelledRepresentation r c.f₁)
    (factorLabelledRepresentation s c.f₂)
    (algebraMap ℂ A ((Fintype.card (Equiv.Perm (Fin r)) : ℂ)⁻¹))
    (algebraMap ℂ A ((Fintype.card (Equiv.Perm (Fin s)) : ℂ)⁻¹))
    (permutationCard_inverse r) (permutationCard_inverse s)

/-- The actual coprime-chart splitting of the original symmetric coefficient family. -/
def symmetricChartEquiv (c : Collision.ChartData (r+s) r s A) :
    CoefficientBaseChange (Depth.RB (r+s)) (symmetricPower (r+s)) A ≃ₗ[A]
      FactorSymmetric r c.f₁ ⊗[A] FactorSymmetric s c.f₂ :=
  ((symmetricChartFixedEquiv c).trans (factorTensorFixedEquiv c).symm).trans
    (TensorProduct.congr (factorSymmetricFixedEquiv r c.f₁).symm
      (factorSymmetricFixedEquiv s c.f₂).symm)

/-- The defining chart map is literally quotient restriction in root coordinates. -/
theorem symmetricChartFixedEquiv_apply (c : Collision.ChartData (r+s) r s A)
    (x : CoefficientBaseChange (Depth.RB (r+s)) (symmetricPower (r+s)) A) :
    (symmetricChartFixedEquiv c x).val = coloredBlockTensorEquiv c
      (coloredAssignmentSplitting (r+s) A c (symmetricCoefficientRootInclusion (r+s) A x)
        (firstBlock r s)) := rfl

end KhanSL2.SymmetricFamily
