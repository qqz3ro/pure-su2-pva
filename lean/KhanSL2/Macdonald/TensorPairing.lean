module

public import KhanSL2.Macdonald.PolynomialPairing

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The monomial factorial pairing is exactly the tensor product of the
symmetric polynomial pairing and the exterior coefficient pairing. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald

private def tensorPairing : W →ₗ[ℂ] W →ₗ[ℂ] ℂ :=
  (TensorProduct.map₂ polynomialPairing
    (FiniteExterior.coefficientPairing : Exterior →ₗ[ℂ] Exterior →ₗ[ℂ] ℂ)).compr₂
      (TensorProduct.lid ℂ ℂ).toLinearMap

private theorem tensorPairing_tmul (p q : Poly) (ω η : Exterior) :
    tensorPairing (p ⊗ₜ[ℂ] ω) (q ⊗ₜ[ℂ] η) =
      polynomialPairing p q * FiniteExterior.coefficientPairing ω η := by
  simp [tensorPairing, TensorProduct.map₂, smul_eq_mul]

private theorem pairing_eq_tensorPairing : pairing = tensorPairing := by
  apply basis.ext
  rintro ⟨d,t⟩
  apply basis.ext
  rintro ⟨e,v⟩
  rw [pairing_basis, basis_apply, basis_apply, tensorPairing_tmul]
  by_cases hd : d = e <;> by_cases ht : t = v <;>
    simp [hd, ht, FiniteExterior.monomial, Finsupp.single_apply, eq_comm]

/-- Evaluation on pure tensors has the symmetric factorial and exterior sign conventions. -/
theorem pairing_tmul (p q : Poly) (ω η : Exterior) :
    pairing (p ⊗ₜ[ℂ] ω) (q ⊗ₜ[ℂ] η) =
      polynomialPairing p q * FiniteExterior.coefficientPairing ω η := by
  rw [pairing_eq_tensorPairing]
  exact tensorPairing_tmul p q ω η

/-- Transpose identities on the two factors give the actual tensor transpose. -/
theorem pairing_tensor_map (A A' : Module.End ℂ Poly) (B B' : Module.End ℂ Exterior)
    (hA : ∀ p q, polynomialPairing (A p) q = polynomialPairing p (A' q))
    (hB : ∀ ω η, FiniteExterior.coefficientPairing (B ω) η =
      FiniteExterior.coefficientPairing ω (B' η)) (u v : W) :
    pairing (TensorProduct.map A B u) v = pairing u (TensorProduct.map A' B' v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw]
  | tmul p ω =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v w hv hw => simp only [map_add, hv, hw]
    | tmul q η => simp only [TensorProduct.map_tmul, pairing_tmul, hA, hB]

end KhanSL2.Macdonald
