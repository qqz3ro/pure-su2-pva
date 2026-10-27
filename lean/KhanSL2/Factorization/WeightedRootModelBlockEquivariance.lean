module

public import KhanSL2.Factorization.WeightedRootModelBlockTensor
public import KhanSL2.Factorization.WeightedRootModelBlockGroup
public import KhanSL2.Factorization.WeightedRootModelFactorAction
public import KhanSL2.Factorization.OrbitStabilizerFixedCongr
public import KhanSL2.Factorization.OrbitStabilizerTensorInvariants

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open Polynomial
open scoped TensorProduct
namespace KhanSL2.Factorization.WeightedRootModel
open WeightedRoots

variable {q₁ q₂ r₁ r₂ : ℕ} {A : Type} [CommRing A]
variable [Algebra (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) A] [Algebra ℂ A]
variable (c : Collision.ChartData ((q₁+q₂)+2*(r₁+r₂)) (q₁+2*r₁) (q₂+2*r₂) A)

omit [Algebra ℂ A] in
theorem blockAssignmentIdeal_eq :
    assignmentIdeal (q₁+q₂) (r₁+r₂) A c (firstWeightedAssignment q₁ q₂ r₁ r₂) =
      factorIdeal (c.f₁.map (algebraMap A (WeightedBase (q₁+q₂) (r₁+r₂) A)))
        (c.f₂.map (algebraMap A (WeightedBase (q₁+q₂) (r₁+r₂) A)))
        (baseRoot (q₁+q₂) (r₁+r₂) A) (rootWeight (q₁+q₂) (r₁+r₂))
        (firstWeightedSet q₁ q₂ r₁ r₂) := by
  unfold assignmentIdeal
  rw [selected_firstWeightedAssignment]

def blockAssignmentEquiv :
    AssignmentRing (q₁+q₂) (r₁+r₂) A c (firstWeightedAssignment q₁ q₂ r₁ r₂) ≃ₐ[A]
      BlockFactor c := Ideal.quotientEquivAlgOfEq A (blockAssignmentIdeal_eq c)

def blockAssignmentTensorEquiv :
    AssignmentRing (q₁+q₂) (r₁+r₂) A c (firstWeightedAssignment q₁ q₂ r₁ r₂) ≃ₐ[A]
      BlockRootTensor c := (blockAssignmentEquiv c).trans (blockFactorTensorEquiv c)

/-- The literal restriction from the original labelled roots to the two smaller root algebras. -/
def blockRestriction : WeightedBase (q₁+q₂) (r₁+r₂) A →ₐ[A] BlockRootTensor c :=
  (blockFactorToTensor c).comp (Ideal.Quotient.mkₐ A _)

@[simp] theorem blockAssignmentTensorEquiv_mk (z : WeightedBase (q₁+q₂) (r₁+r₂) A) :
    blockAssignmentTensorEquiv c (Ideal.Quotient.mk
      (assignmentIdeal (q₁+q₂) (r₁+r₂) A c (firstWeightedAssignment q₁ q₂ r₁ r₂)) z) =
        blockRestriction c z := rfl

@[simp] theorem blockRestriction_firstRoot (i : Fin q₁ ⊕ Fin r₁) :
    blockRestriction c (baseRoot (q₁+q₂) (r₁+r₂) A (firstWeightedInclusion q₁ q₂ r₁ r₂ i)) =
      blockTensorFirstRoot c i := blockFactorToTensor_firstRoot c i

@[simp] theorem blockRestriction_secondRoot (i : Fin q₂ ⊕ Fin r₂) :
    blockRestriction c (baseRoot (q₁+q₂) (r₁+r₂) A (secondWeightedInclusion q₁ q₂ r₁ r₂ i)) =
      blockTensorSecondRoot c i := blockFactorToTensor_secondRoot c i

def blockTensorAutomorphism (g : BlockGroup q₁ r₁ × BlockGroup q₂ r₂) :
    BlockRootTensor c ≃ₐ[A] BlockRootTensor c :=
  Algebra.TensorProduct.congr (factorRootAutomorphism q₁ r₁ c.f₁ g.1)
    (factorRootAutomorphism q₂ r₂ c.f₂ g.2)

@[simp] theorem blockTensorAutomorphism_firstRoot
    (g : BlockGroup q₁ r₁ × BlockGroup q₂ r₂) (i : Fin q₁ ⊕ Fin r₁) :
    blockTensorAutomorphism c g (blockTensorFirstRoot c i) =
      blockTensorFirstRoot c (blockPermutation g.1 i) := by
  simp [blockTensorAutomorphism,blockTensorFirstRoot]

@[simp] theorem blockTensorAutomorphism_secondRoot
    (g : BlockGroup q₁ r₁ × BlockGroup q₂ r₂) (i : Fin q₂ ⊕ Fin r₂) :
    blockTensorAutomorphism c g (blockTensorSecondRoot c i) =
      blockTensorSecondRoot c (blockPermutation g.2 i) := by
  simp [blockTensorAutomorphism,blockTensorSecondRoot]

theorem blockRestriction_permute (g : BlockGroup q₁ r₁ × BlockGroup q₂ r₂)
    (z : WeightedBase (q₁+q₂) (r₁+r₂) A) :
    blockRestriction c (baseBlockAutomorphism (q₁+q₂) (r₁+r₂) A
      (weightedBlockHom q₁ q₂ r₁ r₂ g) z) = blockTensorAutomorphism c g (blockRestriction c z) := by
  have he : (blockRestriction c).comp (baseBlockAutomorphism (q₁+q₂) (r₁+r₂) A
      (weightedBlockHom q₁ q₂ r₁ r₂ g)).toAlgHom =
      (blockTensorAutomorphism c g).toAlgHom.comp (blockRestriction c) := by
    apply rootBaseAlgHom_ext
    intro i
    have h₁ (j : Fin q₁ ⊕ Fin r₁) :
        blockRestriction c (baseBlockAutomorphism (q₁+q₂) (r₁+r₂) A
          (weightedBlockHom q₁ q₂ r₁ r₂ g)
          (baseRoot (q₁+q₂) (r₁+r₂) A (firstWeightedInclusion q₁ q₂ r₁ r₂ j))) =
        blockTensorAutomorphism c g (blockRestriction c
          (baseRoot (q₁+q₂) (r₁+r₂) A (firstWeightedInclusion q₁ q₂ r₁ r₂ j))) := by
      rw [baseBlockAutomorphism_root,weightedBlockHom_first,blockRestriction_firstRoot,
        blockRestriction_firstRoot,blockTensorAutomorphism_firstRoot]
    have h₂ (j : Fin q₂ ⊕ Fin r₂) :
        blockRestriction c (baseBlockAutomorphism (q₁+q₂) (r₁+r₂) A
          (weightedBlockHom q₁ q₂ r₁ r₂ g)
          (baseRoot (q₁+q₂) (r₁+r₂) A (secondWeightedInclusion q₁ q₂ r₁ r₂ j))) =
        blockTensorAutomorphism c g (blockRestriction c
          (baseRoot (q₁+q₂) (r₁+r₂) A (secondWeightedInclusion q₁ q₂ r₁ r₂ j))) := by
      rw [baseBlockAutomorphism_root,weightedBlockHom_second,blockRestriction_secondRoot,
        blockRestriction_secondRoot,blockTensorAutomorphism_secondRoot]
    cases i with
    | inl i => exact Fin.addCases (fun j => h₁ (.inl j)) (fun j => h₂ (.inl j)) i
    | inr i => exact Fin.addCases (fun j => h₁ (.inr j)) (fun j => h₂ (.inr j)) i
  exact AlgHom.congr_fun he z

theorem factorTensorSigned_apply (g : BlockGroup q₁ r₁ × BlockGroup q₂ r₂)
    (z : BlockRootTensor c) :
    FiberTransport.tensorAction (factorSignedAction q₁ r₁ c.f₁)
      (factorSignedAction q₂ r₂ c.f₂) g z =
      (((g.1.1.sign : ℤˣ) : ℤ) * ((g.2.1.sign : ℤˣ) : ℤ) : A) • blockTensorAutomorphism c g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw,smul_add]
  | tmul x y =>
    change factorSignedAction q₁ r₁ c.f₁ g.1 x ⊗ₜ[A] factorSignedAction q₂ r₂ c.f₂ g.2 y = _
    rw [factorSignedAction_apply,factorSignedAction_apply,TensorProduct.smul_tmul_smul]
    rfl

/-- The literal component restriction intertwines the full signed stabilizer
with the two independently signed weighted-root factors. -/
theorem blockAssignmentTensorEquiv_move (g : BlockGroup q₁ r₁ × BlockGroup q₂ r₂)
    (z : AssignmentRing (q₁+q₂) (r₁+r₂) A c (firstWeightedAssignment q₁ q₂ r₁ r₂)) :
    blockAssignmentTensorEquiv c
      ((signedAssignmentTransport (q₁+q₂) (r₁+r₂) A c).move
        (weightedBlockHom q₁ q₂ r₁ r₂ g) _ _ (weightedBlockHom_fixes q₁ q₂ r₁ r₂ g) z) =
      FiberTransport.tensorAction (factorSignedAction q₁ r₁ c.f₁)
        (factorSignedAction q₂ r₂ c.f₂) g (blockAssignmentTensorEquiv c z) := by
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective z
  change blockAssignmentTensorEquiv c ((baseBlockSign (q₁+q₂) (r₁+r₂) A
      (weightedBlockHom q₁ q₂ r₁ r₂ g) : A) •
      Ideal.Quotient.mk (assignmentIdeal (q₁+q₂) (r₁+r₂) A c (firstWeightedAssignment q₁ q₂ r₁ r₂))
        (baseBlockAutomorphism (q₁+q₂) (r₁+r₂) A (weightedBlockHom q₁ q₂ r₁ r₂ g) z)) =
    FiberTransport.tensorAction (factorSignedAction q₁ r₁ c.f₁)
      (factorSignedAction q₂ r₂ c.f₂) g (blockRestriction c z)
  rw [map_smul,blockAssignmentTensorEquiv_mk,
    blockRestriction_permute,factorTensorSigned_apply,baseBlockSign_val,weightedBlockHom_sign,
    Units.val_mul,Int.cast_mul]

/-- The precise stabilizer summand is the tensor product of the two smaller
signed invariant coefficient families, with no flatness or reducedness assumption. -/
def blockSignedFactorEquiv :
    (signedAssignmentTransport (q₁+q₂) (r₁+r₂) A c).stabilizerFixed
      (firstWeightedAssignment q₁ q₂ r₁ r₂) ≃ₗ[A]
      FactorSignedModule q₁ r₁ c.f₁ ⊗[A] FactorSignedModule q₂ r₂ c.f₂ :=
  (FiberTransport.stabilizerFixedCongr (signedAssignmentTransport (q₁+q₂) (r₁+r₂) A c)
    (firstWeightedAssignment q₁ q₂ r₁ r₂) (weightedBlockHom q₁ q₂ r₁ r₂)
    (weightedBlockHom_fixes q₁ q₂ r₁ r₂) (weightedBlockHom_covers q₁ q₂ r₁ r₂)
    (FiberTransport.tensorAction (factorSignedAction q₁ r₁ c.f₁) (factorSignedAction q₂ r₂ c.f₂))
    (blockAssignmentTensorEquiv c).toLinearEquiv (blockAssignmentTensorEquiv_move c)).trans
    ((FiberTransport.tensorFixedEquiv (factorSignedAction q₁ r₁ c.f₁)
      (factorSignedAction q₂ r₂ c.f₂) (factorNormalization q₁ r₁) (factorNormalization q₂ r₂)
      (factorNormalization_mul_card q₁ r₁) (factorNormalization_mul_card q₂ r₂)).symm.trans
        (TensorProduct.congr (factorSignedEquiv q₁ r₁ c.f₁).symm (factorSignedEquiv q₂ r₂ c.f₂).symm))

end KhanSL2.Factorization.WeightedRootModel



