module

public import KhanSL2.Macdonald.PolynomialCoproductPairing
public import KhanSL2.Macdonald.ExteriorCoproductPairing

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Multiplication of the actual mixed cochains is transpose to their
primitive polynomial / signed exterior coproduct, with no hidden rescaling. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald

def mixedCoproductReorder :
    (Poly ⊗[ℂ] Poly) ⊗[ℂ] (Exterior ⊗[ℂ] Exterior) ≃ₗ[ℂ] W ⊗[ℂ] W :=
  TensorProduct.tensorTensorTensorComm ℂ Poly Poly Exterior Exterior

@[simp] theorem mixedCoproductReorder_tmul (p q : Poly) (ω η : Exterior) :
    mixedCoproductReorder ((p ⊗ₜ[ℂ] q) ⊗ₜ[ℂ] (ω ⊗ₜ[ℂ] η)) =
      (p ⊗ₜ[ℂ] ω) ⊗ₜ[ℂ] (q ⊗ₜ[ℂ] η) := rfl

def mixedCoproduct : W →ₗ[ℂ] W ⊗[ℂ] W :=
  mixedCoproductReorder.toLinearMap.comp
    (TensorProduct.map symmetricCoproductAlg.toLinearMap exteriorCoproduct)

@[simp] theorem mixedCoproduct_tmul (p : Poly) (ω : Exterior) :
    mixedCoproduct (p ⊗ₜ[ℂ] ω) =
      mixedCoproductReorder (symmetricCoproductAlg p ⊗ₜ[ℂ] exteriorCoproduct ω) := rfl

/-- Product of the original factorial pairings on the two actual chain factors. -/
def tensorSquarePairing : (W ⊗[ℂ] W) →ₗ[ℂ] (W ⊗[ℂ] W) →ₗ[ℂ] ℂ :=
  (TensorProduct.map₂ pairing pairing).compr₂ (TensorProduct.lid ℂ ℂ).toLinearMap

@[simp] theorem tensorSquarePairing_tmul (u v a b : W) :
    tensorSquarePairing (u ⊗ₜ[ℂ] v) (a ⊗ₜ[ℂ] b) = pairing u a * pairing v b := by
  simp [tensorSquarePairing, TensorProduct.map₂, smul_eq_mul]

theorem tensorSquarePairing_reorder (p q : Poly) (ω η : Exterior)
    (a : Poly ⊗[ℂ] Poly) (b : Exterior ⊗[ℂ] Exterior) :
    tensorSquarePairing ((p ⊗ₜ[ℂ] ω) ⊗ₜ[ℂ] (q ⊗ₜ[ℂ] η))
      (mixedCoproductReorder (a ⊗ₜ[ℂ] b)) =
        polynomialTensorPairing p q a * exteriorTensorPairing ω η b := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a a' ha ha' =>
    simp only [TensorProduct.add_tmul, map_add, ha, ha', add_mul]
  | tmul r s =>
    induction b using TensorProduct.induction_on with
    | zero => simp
    | add b b' hb hb' =>
      simp only [TensorProduct.tmul_add, map_add, hb, hb', mul_add]
    | tmul γ δ =>
      rw [mixedCoproductReorder_tmul, tensorSquarePairing_tmul, pairing_tmul,
        pairing_tmul, polynomialTensorPairing_tmul, exteriorTensorPairing_tmul]
      ring

/-- Exact multiplication-coproduct duality for the full actual mixed algebra. -/
theorem pairing_mul_mixedCoproduct (u v w : W) :
    pairing (u*v) w = tensorSquarePairing (u ⊗ₜ[ℂ] v) (mixedCoproduct w) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u u' hu hu' =>
    simp only [add_mul, map_add, LinearMap.add_apply, TensorProduct.add_tmul, hu, hu']
  | tmul p ω =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v v' hv hv' =>
      simp only [mul_add, map_add, LinearMap.add_apply, TensorProduct.tmul_add, hv, hv']
    | tmul q η =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w w' hw hw' => simp only [map_add, hw, hw']
      | tmul r γ =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, pairing_tmul, mixedCoproduct_tmul,
          tensorSquarePairing_reorder, polynomialPairing_mul_coproduct,
          coefficientPairing_mul_coproduct]

end KhanSL2.Macdonald
