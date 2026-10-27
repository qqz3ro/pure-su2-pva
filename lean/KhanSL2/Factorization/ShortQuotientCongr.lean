module

public import KhanSL2.Factorization.FlatScalarHomology

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open CategoryTheory
namespace KhanSL2.Factorization
variable {R : Type} [CommRing R]
variable (C D : ShortComplex (ModuleCat R))
variable (e₁ : C.X₁ ≃ₗ[R] D.X₁) (e₂ : C.X₂ ≃ₗ[R] D.X₂) (e₃ : C.X₃ ≃ₗ[R] D.X₃)
variable (hf : ∀ x, e₂ (C.f x) = D.f (e₁ x))
variable (hg : ∀ x, e₃ (C.g x) = D.g (e₂ x))

/-- An actual chain isomorphism restricts to its actual cycle isomorphism. -/
def shortCycleCongr : LinearMap.ker C.g.hom ≃ₗ[R] LinearMap.ker D.g.hom where
  toFun z := ⟨e₂ z.val, by
    change D.g (e₂ z.val) = 0
    rw [← hg,z.property,map_zero]⟩
  invFun z := ⟨e₂.symm z.val, by
    apply e₃.injective
    rw [hg,LinearEquiv.apply_symm_apply,z.property,map_zero]⟩
  left_inv z := Subtype.ext (e₂.symm_apply_apply z.val)
  right_inv z := Subtype.ext (e₂.apply_symm_apply z.val)
  map_add' z w := Subtype.ext (e₂.map_add z.val w.val)
  map_smul' a z := Subtype.ext (e₂.map_smul a z.val)

include e₁ hf in
theorem shortCycleCongr_range :
    (LinearMap.range C.moduleCatToCycles).map (shortCycleCongr C D e₂ e₃ hg).toLinearMap =
      LinearMap.range D.moduleCatToCycles := by
  ext z
  constructor
  · rintro ⟨_,⟨x,rfl⟩,rfl⟩
    exact ⟨e₁ x,Subtype.ext (hf x).symm⟩
  · rintro ⟨y,rfl⟩
    refine ⟨C.moduleCatToCycles (e₁.symm y),⟨_,rfl⟩,?_⟩
    apply Subtype.ext
    exact (hf (e₁.symm y)).trans (congrArg D.f (e₁.apply_symm_apply y))

/-- Transport of literal cycles modulo boundaries along the actual three chain maps. -/
def shortQuotientCongr : C.moduleCatLeftHomologyData.H ≃ₗ[R] D.moduleCatLeftHomologyData.H :=
  Submodule.Quotient.equiv _ _ (shortCycleCongr C D e₂ e₃ hg)
    (shortCycleCongr_range C D e₁ e₂ e₃ hf hg)

@[simp] theorem shortQuotientCongr_mk (z : LinearMap.ker C.g.hom) :
    shortQuotientCongr C D e₁ e₂ e₃ hf hg (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (shortCycleCongr C D e₂ e₃ hg z) := rfl

end KhanSL2.Factorization
