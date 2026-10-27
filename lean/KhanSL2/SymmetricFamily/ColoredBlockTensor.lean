module

public import KhanSL2.SymmetricFamily.ColoredAssignmentSplit
public import KhanSL2.SymmetricFamily.ColorBlocks
public import KhanSL2.SymmetricFamily.RootBlockPermutation
public import KhanSL2.SymmetricFamily.FactorPermutation
public import KhanSL2.Factorization.OrbitStabilizerFixedCongr

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-! The distinguished actual colored root assignment is the tensor product of
the two smaller root/color factors, with precisely their independent slot actions. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Factorization
open scoped FactorRootScalars

variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB (r+s)) A]

/-- The literal block root and color splitting, followed by the tensor interchange. -/
def coloredBlockTensorEquiv (c : Collision.ChartData (r+s) r s A) :
    ColoredAssignment (r+s) A c (firstBlock r s) ≃ₗ[A]
      FactorColors r c.f₁ ⊗[A] FactorColors s c.f₂ :=
  (TensorProduct.AlgebraTensorModule.congr (blockFactorTensorEquiv c).toLinearEquiv
    (colorBlockEquiv r s)).trans
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm ℂ ℂ A A
        (FactorRoots r c.f₁) (Color r) (FactorRoots s c.f₂) (Color s)).symm

@[simp] theorem coloredBlockTensorEquiv_symm_tmul
    (c : Collision.ChartData (r+s) r s A)
    (p : FactorRoots r c.f₁) (u : Color r) (q : FactorRoots s c.f₂) (v : Color s) :
    (coloredBlockTensorEquiv c).symm ((p ⊗ₜ[ℂ] u) ⊗ₜ[A] (q ⊗ₜ[ℂ] v)) =
      (blockFactorTensorEquiv c).symm (p ⊗ₜ[A] q) ⊗ₜ[ℂ]
        (colorBlockEquiv r s).symm (u ⊗ₜ[ℂ] v) := rfl

omit [IsScalarTower ℂ (Depth.RB (r+s)) A] in
/-- The inverse block root map has the same exact independent permutation behavior. -/
theorem blockFactorTensorEquiv_symm_permute (c : Collision.ChartData (r+s) r s A)
    (g : Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) (q : BlockRootTensor c) :
    blockFactorPermutation c g ((blockFactorTensorEquiv c).symm q) =
      (blockFactorTensorEquiv c).symm
        (Algebra.TensorProduct.map (factorRootPermutation r c.f₁ g.1).toAlgHom
          (factorRootPermutation s c.f₂ g.2).toAlgHom q) := by
  apply (blockFactorTensorEquiv c).injective
  rw [blockFactorTensorEquiv_permute,AlgEquiv.apply_symm_apply,AlgEquiv.apply_symm_apply]

/-- The inverse color map intertwines the same two literal block permutations. -/
theorem colorBlockEquiv_symm_permute
    (g : Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) (v : Color r ⊗[ℂ] Color s) :
    colorPermutationEquiv (blockPermutationHom r s g) ((colorBlockEquiv r s).symm v) =
      (colorBlockEquiv r s).symm
        (TensorProduct.map (colorPermutationEquiv g.1).toLinearMap
          (colorPermutationEquiv g.2).toLinearMap v) := by
  apply (colorBlockEquiv r s).injective
  rw [colorBlockEquiv_permute,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]

/-- The original colored transport on the distinguished assignment has a literal tensor formula. -/
theorem coloredAssignmentTransport_block_tmul (c : Collision.ChartData (r+s) r s A)
    (g : Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) (q : BlockFactor c) (v : Color (r+s)) :
    (coloredAssignmentTransport (r+s) A c).move (blockPermutationHom r s g)
      (firstBlock r s) (firstBlock r s) (blockPermutation_firstBlock r s g) (q ⊗ₜ[ℂ] v) =
        blockFactorPermutation c g q ⊗ₜ[ℂ] colorPermutationEquiv (blockPermutationHom r s g) v := rfl

/-- The exact stabilizer representation in the split colored coordinates. -/
theorem coloredBlockTensorEquiv_symm_permute (c : Collision.ChartData (r+s) r s A)
    (g : Equiv.Perm (Fin r) × Equiv.Perm (Fin s))
    (x : FactorColors r c.f₁ ⊗[A] FactorColors s c.f₂) :
    (coloredAssignmentTransport (r+s) A c).move (blockPermutationHom r s g)
      (firstBlock r s) (firstBlock r s) (blockPermutation_firstBlock r s g)
        ((coloredBlockTensorEquiv c).symm x) =
      (coloredBlockTensorEquiv c).symm
        (FiberTransport.tensorAction (factorLabelledRepresentation r c.f₁)
          (factorLabelledRepresentation s c.f₂) g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x z hx hz => simp only [TensorProduct.add_tmul,map_add,hx,hz]
    | tmul p u =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz => simp only [TensorProduct.tmul_add,map_add,hy,hz]
      | tmul q v =>
        rw [coloredBlockTensorEquiv_symm_tmul,coloredAssignmentTransport_block_tmul,
          blockFactorTensorEquiv_symm_permute,colorBlockEquiv_symm_permute]
        change _ = (coloredBlockTensorEquiv c).symm
          ((factorRootPermutation r c.f₁ g.1 p ⊗ₜ[ℂ] colorPermutationEquiv g.1 u) ⊗ₜ[A]
            (factorRootPermutation s c.f₂ g.2 q ⊗ₜ[ℂ] colorPermutationEquiv g.2 v))
        rw [coloredBlockTensorEquiv_symm_tmul]
        rfl

/-- The forward factor map intertwines the original stabilizer with independent factor actions. -/
theorem coloredBlockTensorEquiv_permute (c : Collision.ChartData (r+s) r s A)
    (g : Equiv.Perm (Fin r) × Equiv.Perm (Fin s))
    (x : ColoredAssignment (r+s) A c (firstBlock r s)) :
    coloredBlockTensorEquiv c
      ((coloredAssignmentTransport (r+s) A c).move (blockPermutationHom r s g)
        (firstBlock r s) (firstBlock r s) (blockPermutation_firstBlock r s g) x) =
      FiberTransport.tensorAction (factorLabelledRepresentation r c.f₁)
        (factorLabelledRepresentation s c.f₂) g (coloredBlockTensorEquiv c x) := by
  obtain ⟨x,rfl⟩ := (coloredBlockTensorEquiv c).symm.surjective x
  rw [coloredBlockTensorEquiv_symm_permute,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]

end KhanSL2.SymmetricFamily
