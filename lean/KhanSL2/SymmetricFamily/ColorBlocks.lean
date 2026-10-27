module

public import KhanSL2.SymmetricFamily.ColorPermutation
public import KhanSL2.SymmetricFamily.BlockStabilizer

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The actual finite color tensor decomposition along two labelled blocks,
including the literal stabilizer permutation action. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG

/-- Restrict a color word to the literal first and second labelled blocks. -/
def colorWordBlockEquiv (r s : ℕ) :
    (Fin (r+s) → Fin 3) ≃ (Fin r → Fin 3) × (Fin s → Fin 3) where
  toFun c := (fun i => c (Fin.castAdd s i),fun i => c (Fin.natAdd r i))
  invFun c := Fin.addCases c.1 c.2
  left_inv c := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  right_inv c := by
    apply Prod.ext <;> funext i <;> simp

/-- The actual color basis identifies block colors with their tensor product. -/
def colorBlockEquiv (r s : ℕ) : Color (r+s) ≃ₗ[ℂ] Color r ⊗[ℂ] Color s :=
  (Pi.basisFun ℂ (Fin (r+s) → Fin 3)).equiv
    ((Pi.basisFun ℂ (Fin r → Fin 3)).tensorProduct (Pi.basisFun ℂ (Fin s → Fin 3)))
    (colorWordBlockEquiv r s)

@[simp] theorem colorBlockEquiv_basis (r s : ℕ) (c : Fin (r+s) → Fin 3) :
    colorBlockEquiv r s (Pi.basisFun ℂ (Fin (r+s) → Fin 3) c) =
      Pi.basisFun ℂ (Fin r → Fin 3) (fun i => c (Fin.castAdd s i)) ⊗ₜ[ℂ]
        Pi.basisFun ℂ (Fin s → Fin 3) (fun i => c (Fin.natAdd r i)) := by
  rw [colorBlockEquiv,Module.Basis.equiv_apply,Module.Basis.tensorProduct_apply]
  rfl

/-- The actual stabilizer action is exactly independent color permutation in the two factors. -/
theorem colorBlockEquiv_permute (r s : ℕ)
    (g : Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) (v : Color (r+s)) :
    colorBlockEquiv r s (colorPermutationEquiv (blockPermutationHom r s g) v) =
      TensorProduct.map (colorPermutationEquiv g.1).toLinearMap
        (colorPermutationEquiv g.2).toLinearMap (colorBlockEquiv r s v) := by
  have he : (colorBlockEquiv r s).toLinearMap.comp
      (colorPermutationEquiv (blockPermutationHom r s g)).toLinearMap =
      (TensorProduct.map (colorPermutationEquiv g.1).toLinearMap
        (colorPermutationEquiv g.2).toLinearMap).comp (colorBlockEquiv r s).toLinearMap := by
    apply (Pi.basisFun ℂ (Fin (r+s) → Fin 3)).ext
    intro c
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,colorPermutationEquiv_basis,
      colorBlockEquiv_basis,TensorProduct.map_tmul]
    have hinv : (blockPermutationHom r s g).symm = blockPermutationHom r s g⁻¹ :=
      ((blockPermutationHom r s).map_inv g).symm
    rw [hinv]
    simp only [Function.comp_def,blockPermutation_castAdd,blockPermutation_natAdd,Prod.fst_inv,Prod.snd_inv]
    rfl
  exact LinearMap.congr_fun he v

end KhanSL2.SymmetricFamily
