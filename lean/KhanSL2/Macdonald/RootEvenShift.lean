module

public import KhanSL2.Macdonald.RootEvenAlgebra

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The actual one-color symmetric raising operator becomes multiplication by
root power sums under the normalized polynomial comparison. -/
noncomputable section
open scoped BigOperators TensorProduct
namespace KhanSL2.Macdonald
open SymmetricFamily PolynomialBGG

/-- Normalized tensor symmetrization of actual even homogeneous polynomials. -/
def rootEvenToTensor (r : ℕ) : RootEvenPower r →ₗ[ℂ] (⨂[ℂ]^r (Polynomial ℂ)) :=
  (polynomialWordBasis r).repr.symm.toLinearMap.comp
    ((relabel r).comp (rootEvenExponentEquiv r).toLinearMap)

@[simp] theorem rootTensorToEven_rootEvenToTensor (r : ℕ) (p : RootEvenPower r) :
    rootTensorToEven r (rootEvenToTensor r p) = p := by
  apply (rootEvenExponentEquiv r).injective
  simp only [rootTensorToEven,rootEvenToTensor,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply,unlabel_relabel]

theorem rootEvenTensorProduct_shift (m r : ℕ) (x : ⨂[ℂ]^r (Polynomial ℂ)) :
    rootEvenTensorProduct r (tensorDeriv r
      (LinearMap.mulLeft ℂ ((Polynomial.X : Polynomial ℂ)^m)) x) =
        rootEvenShift m (rootEvenTensorProduct r x) := by
  have h : (rootEvenTensorProduct r).comp (tensorDeriv r
      (LinearMap.mulLeft ℂ ((Polynomial.X : Polynomial ℂ)^m))) =
        (rootEvenShift m).toLinearMap.comp (rootEvenTensorProduct r) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,
      tensorDeriv_tprod,map_sum,rootEvenTensorProduct_tprod,Derivation.coeFn_coe]
    rw [derivation_prod_update]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j _
    by_cases hji : j = i
    · subst j
      simp [rootEvenShift_variable]
    · simp [Function.update_of_ne hji]
  exact LinearMap.congr_fun h x

theorem rootEvenShift_mem (m r : ℕ) (p : RootEvenPower r) :
    rootEvenShift m p.val ∈ RootEvenPower r := by
  have h : rootEvenShift m p.val =
      (rootTensorToEven r (tensorDeriv r
        (LinearMap.mulLeft ℂ ((Polynomial.X : Polynomial ℂ)^m)) (rootEvenToTensor r p))).val := by
    rw [rootTensorToEven_coe, rootEvenTensorProduct_shift,
      ← rootTensorToEven_coe,rootTensorToEven_rootEvenToTensor]
  rw [h]
  exact Subtype.property _

/-- Restriction of the actual polynomial raising derivation, not a transported action. -/
def rootEvenShiftEnd (m r : ℕ) : Module.End ℂ (RootEvenPower r) :=
  (rootEvenShift m).toLinearMap.restrict (fun p hp => rootEvenShift_mem m r ⟨p,hp⟩)

@[simp] theorem rootEvenShiftEnd_val (m r : ℕ) (p : RootEvenPower r) :
    (rootEvenShiftEnd m r p).val = rootEvenShift m p.val := rfl

theorem rootTensorToEven_shift (m r : ℕ) (x : ⨂[ℂ]^r (Polynomial ℂ)) :
    rootTensorToEven r (tensorDeriv r
      (LinearMap.mulLeft ℂ ((Polynomial.X : Polynomial ℂ)^m)) x) =
        rootEvenShiftEnd m r (rootTensorToEven r x) := by
  apply Subtype.ext
  simp only [rootTensorToEven_coe,rootEvenShiftEnd_val,rootEvenTensorProduct_shift]

theorem rootEvenToTensor_invariant (r : ℕ) (p : RootEvenPower r)
    (σ : Equiv.Perm (Fin r)) :
    slotPermute (Polynomial ℂ) σ (rootEvenToTensor r p) = rootEvenToTensor r p := by
  apply (polynomialWordBasis r).repr.injective
  rw [polynomialWordBasis_repr_permute]
  simp only [rootEvenToTensor,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  exact relabel_mem r _ σ

theorem rootEvenToTensor_rootTensorToEven (r : ℕ) (x : ⨂[ℂ]^r (Polynomial ℂ))
    (hx : ∀ σ : Equiv.Perm (Fin r), slotPermute (Polynomial ℂ) σ x = x) :
    rootEvenToTensor r (rootTensorToEven r x) = x := by
  apply (polynomialWordBasis r).repr.injective
  simp only [rootTensorToEven,rootEvenToTensor,LinearMap.comp_apply,
    LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,relabel_unlabel]
  apply wordAverage_eq_self
  intro σ
  rw [← polynomialWordBasis_repr_permute,hx σ]

theorem rootSlotPermute_tensorDeriv (r : ℕ) (σ : Equiv.Perm (Fin r))
    (D : Module.End ℂ (Polynomial ℂ)) (x : ⨂[ℂ]^r (Polynomial ℂ)) :
    slotPermute (Polynomial ℂ) σ (tensorDeriv r D x) =
      tensorDeriv r D (slotPermute (Polynomial ℂ) σ x) := by
  have h : (slotPermute (Polynomial ℂ) σ).toLinearMap.comp (tensorDeriv r D) =
      (tensorDeriv r D).comp (slotPermute (Polynomial ℂ) σ).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,LinearEquiv.coe_coe,
      tensorDeriv_tprod,map_sum,slotPermute_tprod]
    rw [← Equiv.sum_comp σ]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact Function.update_comp_eq_of_injective v σ.injective i (D (v (σ i)))
  exact LinearMap.congr_fun h x

theorem rootEvenToTensor_shift (m r : ℕ) (p : RootEvenPower r) :
    rootEvenToTensor r (rootEvenShiftEnd m r p) =
      tensorDeriv r (LinearMap.mulLeft ℂ ((Polynomial.X : Polynomial ℂ)^m))
        (rootEvenToTensor r p) := by
  rw [← rootTensorToEven_rootEvenToTensor r p, ← rootTensorToEven_shift,
    rootTensorToEven_rootEvenToTensor]
  apply rootEvenToTensor_rootTensorToEven
  intro σ
  rw [rootSlotPermute_tensorDeriv,rootEvenToTensor_invariant]

/-- The specified root-polynomial equivalence has the actual tensor formula. -/
theorem rootEvenPolynomialEquiv_tensor (r : ℕ) (p : RootEvenPower r) :
    (rootEvenPolynomialEquiv r p).val = polynomialTensorEquiv r (rootEvenToTensor r p) := by
  change wordPolynomialEquiv r (relabel r (rootEvenExponentEquiv r p)) =
    wordPolynomialEquiv r ((polynomialWordBasis r).repr
      ((polynomialWordBasis r).repr.symm (relabel r (rootEvenExponentEquiv r p))))
  rw [LinearEquiv.apply_symm_apply]

/-- The actual even raising derivation is precisely multiplication by a root power sum. -/
theorem rootEvenPolynomialEquiv_shift (m r : ℕ) (p : RootEvenPower r) :
    (rootEvenPolynomialEquiv r (rootEvenShiftEnd m r p)).val =
      MvPolynomial.psum (Fin r) ℂ m * (rootEvenPolynomialEquiv r p).val := by
  rw [rootEvenPolynomialEquiv_tensor,rootEvenToTensor_shift,polynomialTensorEquiv_shift,
    rootEvenPolynomialEquiv_tensor]

end KhanSL2.Macdonald
