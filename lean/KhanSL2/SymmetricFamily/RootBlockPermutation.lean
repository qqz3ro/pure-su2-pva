module

public import KhanSL2.SymmetricFamily.RootBlockTensor
public import KhanSL2.SymmetricFamily.FactorRootScalars
public import KhanSL2.SymmetricFamily.BlockStabilizer

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-! The first-block algebra splitting intertwines the original stabilizer action
with the independent permutations of the two actual factor root algebras. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily

variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A] [Algebra ℂ A]

omit [Algebra ℂ A] in
/-- The literal first-block factor ideal is preserved by every block permutation. -/
theorem blockFactorIdeal_permutation (c : Collision.ChartData (r+s) r s A)
    (g : Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) :
    Ideal.map (baseRootPermutation (r+s) A (blockPermutationHom r s g)).toRingHom
      (assignmentFactorIdeal (r+s) A c (firstBlock r s)) =
        assignmentFactorIdeal (r+s) A c (firstBlock r s) := by
  have h := baseRootPermutation_factorIdeal (r+s) A c (blockPermutationHom r s g) (firstBlock r s).val
  have hs : (firstBlock r s).val.map (blockPermutationHom r s g).toEmbedding =
      (firstBlock r s).val := congrArg Subtype.val (blockPermutation_firstBlock r s g)
  rw [hs] at h
  exact h

/-- The actual first-block quotient automorphism induced by a block permutation. -/
def blockFactorPermutation (c : Collision.ChartData (r+s) r s A)
    (g : Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) : BlockFactor c ≃ₐ[A] BlockFactor c :=
  Ideal.quotientEquivAlg _ _ (baseRootPermutation (r+s) A (blockPermutationHom r s g))
    (blockFactorIdeal_permutation c g).symm
omit [Algebra ℂ A] in
@[simp] theorem blockFactorPermutation_mk (c : Collision.ChartData (r+s) r s A)
    (g : Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) (q : RootBase (r+s) A) :
    blockFactorPermutation c g (Ideal.Quotient.mk _ q) =
      Ideal.Quotient.mk _ (baseRootPermutation (r+s) A (blockPermutationHom r s g) q) := rfl

omit [Algebra ℂ A] in
@[simp] theorem blockFactorPermutation_root (c : Collision.ChartData (r+s) r s A)
    (g : Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) (i : Fin (r+s)) :
    blockFactorPermutation c g (blockRoot c i) = blockRoot c (blockPermutationHom r s g i) := by
  rw [blockRoot,blockFactorPermutation_mk,baseRootPermutation_baseRoot]
  rfl

omit [Algebra ℂ A] in
/-- The original quotient transport is this actual root algebra automorphism. -/
theorem rootAssignmentTransport_block (c : Collision.ChartData (r+s) r s A)
    (g : Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) (q : BlockFactor c) :
    (rootAssignmentTransport (r+s) A c).move (blockPermutationHom r s g)
      (firstBlock r s) (firstBlock r s) (blockPermutation_firstBlock r s g) q =
        blockFactorPermutation c g q := rfl

/-- Exact equivariance of the root factorization, with the literal independent slot maps. -/
theorem blockFactorTensorEquiv_permute (c : Collision.ChartData (r+s) r s A)
    (g : Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) (q : BlockFactor c) :
    blockFactorTensorEquiv c (blockFactorPermutation c g q) =
      Algebra.TensorProduct.map (factorRootPermutation r c.f₁ g.1).toAlgHom
        (factorRootPermutation s c.f₂ g.2).toAlgHom (blockFactorTensorEquiv c q) := by
  have he : (blockFactorTensorEquiv c).toAlgHom.comp (blockFactorPermutation c g).toAlgHom =
      (Algebra.TensorProduct.map (factorRootPermutation r c.f₁ g.1).toAlgHom
        (factorRootPermutation s c.f₂ g.2).toAlgHom).comp (blockFactorTensorEquiv c).toAlgHom := by
    apply blockFactorAlgHom_ext
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · change blockFactorToTensor c (blockFactorPermutation c g (blockRoot c (Fin.castAdd s j))) =
        Algebra.TensorProduct.map _ _ (blockFactorToTensor c (blockRoot c (Fin.castAdd s j)))
      rw [blockFactorPermutation_root,blockPermutation_castAdd,
        blockFactorToTensor_leftRoot,blockFactorToTensor_leftRoot]
      simp only [blockTensorLeftRoot,Algebra.TensorProduct.map_tmul,AlgEquiv.coe_algHom,
        factorRootPermutation_root,map_one]
    · change blockFactorToTensor c (blockFactorPermutation c g (blockRoot c (Fin.natAdd r j))) =
        Algebra.TensorProduct.map _ _ (blockFactorToTensor c (blockRoot c (Fin.natAdd r j)))
      rw [blockFactorPermutation_root,blockPermutation_natAdd,
        blockFactorToTensor_rightRoot,blockFactorToTensor_rightRoot]
      simp only [blockTensorRightRoot,Algebra.TensorProduct.map_tmul,AlgEquiv.coe_algHom,
        factorRootPermutation_root,map_one]
  exact AlgHom.congr_fun he q

end KhanSL2.SymmetricFamily
