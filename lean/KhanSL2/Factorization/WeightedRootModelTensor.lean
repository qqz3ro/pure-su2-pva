module

public import KhanSL2.Factorization.WeightedRootModelPolynomialActions
public import KhanSL2.Factorization.OrbitStabilizerCongr

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace KhanSL2.Factorization.WeightedRootModel
open MvPolynomial FiberTransport

/-- The coefficient-linear sign is precisely the original complex sign character. -/
theorem signedBlockOperator_apply {q r : ℕ} (g : BlockGroup q r) (p : LabelledWeightedRing q r) :
    signedBlockOperator g p = (g.1.sign : ℂ) •
      rename (blockPermutation g) (show MvPolynomial (Fin q ⊕ Fin r) ℂ from p) := by
  change ((g.1.sign : ℤ) : Depth.RB (q+2*r)) •
    (show LabelledWeightedRing q r from rename (blockPermutation g) p) =
      ((g.1.sign : ℤ) : ℂ) • (show LabelledWeightedRing q r from rename (blockPermutation g) p)
  rw [Int.cast_smul_eq_zsmul,Int.cast_smul_eq_zsmul]

theorem rename_inl_block {q r : ℕ} (g : BlockGroup q r) (p : MvPolynomial (Fin q) ℂ) :
    rename Sum.inl (rename g.1 p) =
      rename (blockPermutation g) (rename Sum.inl p) := by
  rw [rename_rename,rename_rename]
  rfl

theorem rename_inr_block {q r : ℕ} (g : BlockGroup q r) (p : MvPolynomial (Fin r) ℂ) :
    rename Sum.inr (rename g.2 p) =
      rename (blockPermutation g) (rename Sum.inr p) := by
  rw [rename_rename,rename_rename]
  rfl

/-- The actual polynomial product identifies the independent sign/symmetry action
with the prescribed signed block action. -/
theorem rawTensorEquiv_signed_action (q r : ℕ) (g : BlockGroup q r)
    (x : MvPolynomial (Fin q) ℂ ⊗[ℂ] MvPolynomial (Fin r) ℂ) :
    rawTensorEquiv q r (tensorAction (alternatingPolynomialAction q) (polynomialAction r) g x) =
      signedBlockOperator g (rawTensorEquiv q r x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p t =>
    change rawTensorEquiv q r (((g.1.sign : ℂ) • rename g.1 p) ⊗ₜ[ℂ] rename g.2 t) = _
    rw [← TensorProduct.smul_tmul',map_smul,rawTensorEquiv_tmul,
      rawTensorEquiv_tmul,signedBlockOperator_apply]
    congr 1
    rw [map_mul,← rename_inl_block,← rename_inr_block]
  | add x y hx hy => simp only [map_add,hx,hy]

/-- The specified alternating/symmetric polynomial model is exactly the signed
weighted-invariant module, via the ordinary product of its two alphabets. -/
def rootHomologyModelEquiv (q r : ℕ) :
    Macdonald.RootHomologyModel q r ≃ₗ[ℂ] signedInvariantComplexModule q r := by
  let e₁ := TensorProduct.congr (alternatingFixedEquiv q) (symmetricFixedEquiv r)
  let e₂ := tensorFixedEquiv (alternatingPolynomialAction q) (polynomialAction r)
    ((Fintype.card (Equiv.Perm (Fin q)) : ℂ)⁻¹)
    ((Fintype.card (Equiv.Perm (Fin r)) : ℂ)⁻¹)
    (inv_mul_cancel₀ (SymmetricFamily.permutationCard_ne_zero q))
    (inv_mul_cancel₀ (SymmetricFamily.permutationCard_ne_zero r))
  let e₃ := fixedVectorsCongr
    (fun g => tensorAction (alternatingPolynomialAction q) (polynomialAction r) g)
    (fun g : BlockGroup q r => (signedBlockOperator g).restrictScalars ℂ)
    (rawTensorEquiv q r).toLinearEquiv (rawTensorEquiv_signed_action q r)
  exact e₁.trans (e₂.trans e₃)

/-- Exact pure-tensor formula, retaining both the alternating and symmetric normalization. -/
@[simp] theorem rootHomologyModelEquiv_tmul (q r : ℕ)
    (p : SymmetricFamily.alternatingRootPolynomials q) (t : MvPolynomial.symmetricSubalgebra (Fin r) ℂ) :
    (rootHomologyModelEquiv q r (p ⊗ₜ[ℂ] t)).val =
      (rename Sum.inl p.val : LabelledWeightedRing q r) *
        (rename Sum.inr t.val : LabelledWeightedRing q r) := by
  change rawTensorEquiv q r (p.val ⊗ₜ[ℂ] t.val) = _
  exact rawTensorEquiv_tmul q r p.val t.val

end KhanSL2.Factorization.WeightedRootModel

