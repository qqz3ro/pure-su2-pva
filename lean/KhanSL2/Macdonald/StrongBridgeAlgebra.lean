module

public import KhanSL2.Macdonald.Basic
public import KhanSL2.StrongMacdonald.Algebra
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The explicit coordinate algebra equivalence needed to use the proved
strong Macdonald calculation for the actual symmetric-coefficient chains.
It changes only the representation of polynomial coordinates and preserves
every even and odd generator, including the even zero mode. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald

/-- The two even-mode label types have identical physical indices and colors. -/
def strongModeEquiv : StrongMacdonald.SMode ≃ Mode where
  toFun g := ⟨g.index, g.color⟩
  invFun g := ⟨g.index, g.color⟩
  left_inv g := by cases g; rfl
  right_inv g := by cases g; rfl

/-- Relabel even exponent vectors without changing their multiplicities. -/
def strongExponentEquiv : StrongMacdonald.Exp ≃+ Exponent :=
  Finsupp.domCongr strongModeEquiv

@[simp] theorem strongExponentEquiv_single (g : StrongMacdonald.SMode) (n : ℕ) :
    strongExponentEquiv (Finsupp.single g n) = Finsupp.single (strongModeEquiv g) n := by
  simp [strongExponentEquiv]

/-- Exterior-valued polynomials and polynomial/exterior tensors have the same
finite monomial coordinates. -/
def strongModel : StrongMacdonald.W ≃ₗ[ℂ] W :=
  (AddMonoidAlgebra.coeffLinearEquiv ℂ).trans
    ((Finsupp.domLCongr strongExponentEquiv.toEquiv).trans
      ((TensorProduct.finsuppScalarLeft ℂ Exterior Exponent).symm.trans
        (TensorProduct.congr (MvPolynomial.basisMonomials Mode ℂ).repr.symm
          (LinearEquiv.refl ℂ Exterior))))

@[simp] theorem strongModel_single (e : StrongMacdonald.Exp) (ω : Exterior) :
    strongModel (AddMonoidAlgebra.single e ω) =
      MvPolynomial.monomial (strongExponentEquiv e) 1 ⊗ₜ[ℂ] ω := by
  simp [strongModel]

@[simp] theorem strongModel_mono (e : StrongMacdonald.Exp) (t : Finset Mode) :
    strongModel (StrongMacdonald.mono e t) = basis (strongExponentEquiv e, t) := by
  rw [StrongMacdonald.mono, strongModel_single, basis_apply]

@[simp] theorem strongModel_one : strongModel 1 = 1 := by
  change strongModel (AddMonoidAlgebra.single 0 (1 : Exterior)) = 1
  simp [Algebra.TensorProduct.one_def]

theorem strongModel_mul (u v : StrongMacdonald.W) :
    strongModel (u * v) = strongModel u * strongModel v := by
  induction u using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add u w hu hw => simp only [add_mul, map_add, hu, hw]
  | single e ω =>
    induction v using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [mul_add, map_add, hv, hw]
    | single f η =>
      simp only [AddMonoidAlgebra.single_mul_single, strongModel_single, map_add,
        Algebra.TensorProduct.tmul_mul_tmul, MvPolynomial.monomial_mul_monomial, one_mul]

/-- The coordinate identification is an algebra equivalence, not just an
unspecified vector-space isomorphism. -/
def strongModelAlg : StrongMacdonald.W ≃ₐ[ℂ] W :=
  AlgEquiv.ofLinearEquiv strongModel strongModel_one strongModel_mul

@[simp] theorem strongModelAlg_apply (u : StrongMacdonald.W) : strongModelAlg u = strongModel u := rfl

@[simp] theorem strongModel_sig (g : StrongMacdonald.SMode) :
    strongModel (StrongMacdonald.sig g) = sigma g.color g.index := by
  rw [StrongMacdonald.sig, strongModel_single, strongExponentEquiv_single]
  rfl

@[simp] theorem strongModel_psi (g : Mode) :
    strongModel (StrongMacdonald.psi g) = psi g.color g.index := by
  rw [StrongMacdonald.psi, strongModel_single]
  simp only [map_zero, MvPolynomial.monomial_zero, map_one]
  rfl

@[simp] theorem strongModel_ofExt (ω : Exterior) :
    strongModel (StrongMacdonald.ofExt ω) = (1 : Poly) ⊗ₜ[ℂ] ω := by
  rw [StrongMacdonald.ofExt_apply, strongModel_single]
  simp

end KhanSL2.Macdonald
