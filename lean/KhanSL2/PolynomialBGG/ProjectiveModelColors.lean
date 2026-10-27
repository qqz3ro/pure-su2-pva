module

public import KhanSL2.PolynomialBGG.ProjectiveModel
public import KhanSL2.PolynomialBGG.ProjectiveModelRetract

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Coinvariants of a finite color action after polynomial scalar extension.
The relation space is proved equal to the extension of the color relations,
so no semisimplicity or exactness is assumed in this identification. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.PolynomialBGG

variable {R P C I : Type*} [CommRing R] [Algebra ℂ R]
  [AddCommGroup P] [Module ℂ P] [Module R P] [IsScalarTower ℂ R P]
  [AddCommGroup C] [Module ℂ C]

/-- Constant actions on the color factor generate exactly the scalar-extended
color relation space. -/
theorem tensorActionRelations_eq (a : I → Module.End ℂ C) :
    actionRelations (fun x => TensorProduct.AlgebraTensorModule.lTensor R P (a x)) =
      extendedColorRelations (R := R) (P := P) (actionRelations a) := by
  apply le_antisymm
  · refine iSup_le fun x => ?_
    rintro _ ⟨u, rfl⟩
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simpa only [map_add] using Submodule.add_mem _ hu hv
    | tmul f c =>
      refine ⟨f ⊗ₜ[ℂ] (⟨a x c, ?_⟩ : actionRelations a), rfl⟩
      exact Submodule.mem_iSup_of_mem x ⟨c, rfl⟩
  · rintro _ ⟨u, rfl⟩
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simpa only [map_add] using Submodule.add_mem _ hu hv
    | tmul f c =>
      let W := actionRelations (fun x => TensorProduct.AlgebraTensorModule.lTensor R P (a x))
      have hc : actionRelations a ≤
          (W.restrictScalars ℂ).comap (TensorProduct.mk ℂ P C f) := by
        refine iSup_le fun x => ?_
        rintro _ ⟨z, rfl⟩
        exact Submodule.mem_iSup_of_mem x ⟨f ⊗ₜ[ℂ] z, rfl⟩
      exact hc c.property

/-- Polynomial-valued color coinvariants are free whenever the polynomial
coefficient module is free over the coefficient ring. -/
theorem tensorActionCoinvariants_free [Module.Free R P] (a : I → Module.End ℂ C) :
    Module.Free R ((P ⊗[ℂ] C) ⧸
      actionRelations (fun x => TensorProduct.AlgebraTensorModule.lTensor R P (a x))) := by
  rw [tensorActionRelations_eq]
  exact colorQuotient_free (actionRelations a)

/-- The analogous projectivity statement does not require freeness. -/
theorem tensorActionCoinvariants_projective [Module.Projective R P]
    (a : I → Module.End ℂ C) :
    Module.Projective R ((P ⊗[ℂ] C) ⧸
      actionRelations (fun x => TensorProduct.AlgebraTensorModule.lTensor R P (a x))) := by
  rw [tensorActionRelations_eq]
  exact colorQuotient_projective (actionRelations a)

end KhanSL2.PolynomialBGG
