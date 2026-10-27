module

public import KhanSL2.SymmetricFamily.SymmetricChart
public import KhanSL2.SymmetricFamily.FactorExterior
public import KhanSL2.SymmetricFamily.SignedTensorAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-! Signed orbit descent of the original exterior coefficient family on an
actual coprime chart. The block sign is exactly the product of the two factor signs. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Factorization
open scoped FactorRootScalars

variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB (r+s)) A]

/-- Actual colored quotient transport with the original exterior sign character. -/
def coloredSignedAssignmentTransport (c : Collision.ChartData (r+s) r s A) :
    FiberTransport (R:=A) (G:=Equiv.Perm (Fin (r+s))) (ColoredAssignment (r+s) A c) :=
  (coloredAssignmentTransport (r+s) A c).twist (permutationSign (r+s) A)

/-- The same actual quotient decomposition intertwines the signed root action. -/
theorem coloredSignedAssignmentSplitting_equivariant (c : Collision.ChartData (r+s) r s A)
    (σ : Equiv.Perm (Fin (r+s))) (S T : Assignment (r+s) r) (h : σ • S = T)
    (x : BaseLabelled (r+s) A) :
    (coloredSignedAssignmentTransport c).move σ S T h
      (coloredAssignmentSplitting (r+s) A c x S) =
      coloredAssignmentSplitting (r+s) A c (baseSignedLabelledPermute (r+s) A σ.symm x) T := by
  rw [coloredSignedAssignmentTransport,FiberTransport.twist_move,coloredAssignmentSplitting_equivariant]
  change (σ.sign:A) • coloredAssignmentSplitting (r+s) A c
      (baseLabelledPermute (r+s) A σ.symm x) T =
    coloredAssignmentSplitting (r+s) A c
      ((Equiv.Perm.sign σ.symm:A) • baseLabelledPermute (r+s) A σ.symm x) T
  rw [map_smul]
  simp only [Pi.smul_apply,Equiv.Perm.sign_symm]

/-- The exact signed stabilizer representation in the split colored coordinates. -/
theorem coloredSignedBlockTensorEquiv_permute (c : Collision.ChartData (r+s) r s A)
    (g : Equiv.Perm (Fin r) × Equiv.Perm (Fin s))
    (x : ColoredAssignment (r+s) A c (firstBlock r s)) :
    coloredBlockTensorEquiv c
      ((coloredSignedAssignmentTransport c).move (blockPermutationHom r s g)
        (firstBlock r s) (firstBlock r s) (blockPermutation_firstBlock r s g) x) =
      FiberTransport.tensorAction (factorSignedLabelledRepresentation r c.f₁)
        (factorSignedLabelledRepresentation s c.f₂) g (coloredBlockTensorEquiv c x) := by
  rw [coloredSignedAssignmentTransport,FiberTransport.twist_move,map_smul,coloredBlockTensorEquiv_permute]
  change ((blockPermutationHom r s g).sign:A) • _ =
    FiberTransport.tensorAction
      (scalarTwistRepresentation (permutationSign r A) (factorLabelledRepresentation r c.f₁))
      (scalarTwistRepresentation (permutationSign s A) (factorLabelledRepresentation s c.f₂)) g _
  rw [tensorAction_scalarTwist,permutationSign_val,permutationSign_val,blockPermutation_sign]
  simp only [Units.val_mul,Int.cast_mul]

/-- Original exterior sections identify with the actual two-factor signed invariant subspace. -/
def exteriorChartFixedEquiv (c : Collision.ChartData (r+s) r s A) :
    CoefficientBaseChange (Depth.RB (r+s)) (⋀[ℂ]^(r+s) BGG.Current) A ≃ₗ[A]
      FiberTransport.fixedVectors (R:=A) (V:=FactorColors r c.f₁ ⊗[A] FactorColors s c.f₂) (fun g =>
        FiberTransport.tensorAction (factorSignedLabelledRepresentation r c.f₁)
          (factorSignedLabelledRepresentation s c.f₂) g) :=
  (((exteriorBaseChangedLabelledEquiv (r+s) A).trans
    (fixedOperatorsInverseEquiv (baseSignedLabelledPermute (r+s) A))).trans
      (FiberTransport.fixedVectorsEquivStabilizer (coloredSignedAssignmentTransport c)
        (fun σ => baseSignedLabelledPermute (r+s) A σ.symm)
        (coloredAssignmentSplitting (r+s) A c) (coloredSignedAssignmentSplitting_equivariant c)
        (firstBlock r s) (fun S => assignment_transitive (firstBlock r s) S))).trans
    (FiberTransport.stabilizerFixedCongr (V:=FactorColors r c.f₁ ⊗[A] FactorColors s c.f₂) (coloredSignedAssignmentTransport c) (firstBlock r s)
      (blockPermutationHom r s) (blockPermutation_firstBlock r s)
      (fun σ hσ => by
        obtain ⟨g,hg⟩ := (blockStabilizerEquiv r s).surjective ⟨σ,hσ⟩
        exact ⟨g,congrArg Subtype.val hg⟩)
      (fun g => FiberTransport.tensorAction (factorSignedLabelledRepresentation r c.f₁)
        (factorSignedLabelledRepresentation s c.f₂) g)
      (coloredBlockTensorEquiv c) (coloredSignedBlockTensorEquiv_permute c))

/-- Actual signed averaging identifies the product-group invariants with the tensor of factor invariants. -/
def exteriorFactorTensorFixedEquiv (c : Collision.ChartData (r+s) r s A) :
    (FiberTransport.fixedVectors (fun σ => factorSignedLabelledRepresentation r c.f₁ σ) ⊗[A]
      FiberTransport.fixedVectors (fun σ => factorSignedLabelledRepresentation s c.f₂ σ)) ≃ₗ[A]
      FiberTransport.fixedVectors (R:=A) (V:=FactorColors r c.f₁ ⊗[A] FactorColors s c.f₂) (fun g =>
        FiberTransport.tensorAction (factorSignedLabelledRepresentation r c.f₁)
          (factorSignedLabelledRepresentation s c.f₂) g) :=
  FiberTransport.tensorFixedEquiv (factorSignedLabelledRepresentation r c.f₁)
    (factorSignedLabelledRepresentation s c.f₂)
    (algebraMap ℂ A ((Fintype.card (Equiv.Perm (Fin r)) : ℂ)⁻¹))
    (algebraMap ℂ A ((Fintype.card (Equiv.Perm (Fin s)) : ℂ)⁻¹))
    (permutationCard_inverse r) (permutationCard_inverse s)

/-- The actual signed exterior coefficient family splits on the coprime chart. -/
def exteriorChartEquiv (c : Collision.ChartData (r+s) r s A) :
    CoefficientBaseChange (Depth.RB (r+s)) (⋀[ℂ]^(r+s) BGG.Current) A ≃ₗ[A]
      FactorExterior r c.f₁ ⊗[A] FactorExterior s c.f₂ :=
  ((exteriorChartFixedEquiv c).trans (exteriorFactorTensorFixedEquiv c).symm).trans
    (TensorProduct.congr (factorExteriorFixedEquiv r c.f₁).symm
      (factorExteriorFixedEquiv s c.f₂).symm)

end KhanSL2.SymmetricFamily
