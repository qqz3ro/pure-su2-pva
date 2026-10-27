module

public import KhanSL2.SymmetricFamily.SymmetricBlockWords

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The original primitive polynomial coproduct is natural for renaming its variables. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
variable {α β : Type*}

theorem polynomialPrimitive_rename (f : α → β) (p : MvPolynomial α ℂ) :
    polynomialPrimitive (MvPolynomial.rename f p) =
      Algebra.TensorProduct.map (MvPolynomial.rename f) (MvPolynomial.rename f)
        (polynomialPrimitive p) := by
  have h : polynomialPrimitive.comp (MvPolynomial.rename f) =
      (Algebra.TensorProduct.map (MvPolynomial.rename f) (MvPolynomial.rename f)).comp
        polynomialPrimitive := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [AlgHom.comp_apply,MvPolynomial.rename_X,polynomialPrimitive_X,map_add,
      Algebra.TensorProduct.map_tmul,map_one]
  exact AlgHom.congr_fun h p

end KhanSL2.SymmetricFamily
