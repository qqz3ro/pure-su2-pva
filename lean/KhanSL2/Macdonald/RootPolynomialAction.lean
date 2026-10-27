module

public import KhanSL2.Macdonald.RootFreeCoordinates

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The actual root-polynomial power-sum operators and their exact relation to
the one-color exterior/symmetric model. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald
open SymmetricFamily PolynomialBGG

/-- Multiplication by the odd-root power sum preserves alternating polynomials. -/
theorem alternating_psum_mul_mem (m q : ℕ) (p : alternatingRootPolynomials q) :
    MvPolynomial.psum (Fin q) ℂ m * p.val ∈ alternatingRootPolynomials q := by
  obtain ⟨x,rfl⟩ := (exteriorPolynomialEquiv q).surjective p
  rw [← exteriorPolynomialEquiv_shift]
  exact Subtype.property _

/-- Actual odd-root power-sum multiplication. -/
def rootOddPowerSumEnd (m q : ℕ) : Module.End ℂ (alternatingRootPolynomials q) :=
  (LinearMap.mulLeft ℂ (MvPolynomial.psum (Fin q) ℂ m)).restrict
    (fun p hp => alternating_psum_mul_mem m q ⟨p,hp⟩)

/-- Multiplication by an even-root power sum preserves the symmetric root ring. -/
theorem symmetric_psum_mul_mem (m r : ℕ)
    (p : MvPolynomial.symmetricSubalgebra (Fin r) ℂ) :
    MvPolynomial.psum (Fin r) ℂ m * p.val ∈ MvPolynomial.symmetricSubalgebra (Fin r) ℂ := by
  obtain ⟨x,rfl⟩ := (rootEvenPolynomialEquiv r).surjective p
  rw [← rootEvenPolynomialEquiv_shift]
  exact Subtype.property _

/-- Actual even-root power-sum multiplication, before its weight-two coefficient. -/
def rootEvenPowerSumEnd (m r : ℕ) :
    Module.End ℂ (MvPolynomial.symmetricSubalgebra (Fin r) ℂ) where
  toFun p := ⟨MvPolynomial.psum (Fin r) ℂ m * p.val,symmetric_psum_mul_mem m r p⟩
  map_add' _p _q := Subtype.ext (mul_add _ _ _)
  map_smul' _c _p := Subtype.ext (mul_smul_comm _ _ _)

@[simp] theorem rootOddPowerSumEnd_val (m q : ℕ) (p : alternatingRootPolynomials q) :
    (rootOddPowerSumEnd m q p).val = MvPolynomial.psum (Fin q) ℂ m * p.val := rfl

@[simp] theorem rootEvenPowerSumEnd_val (m r : ℕ)
    (p : MvPolynomial.symmetricSubalgebra (Fin r) ℂ) :
    (rootEvenPowerSumEnd m r p).val = MvPolynomial.psum (Fin r) ℂ m * p.val := rfl

/-- The root action has weights one on odd roots and two on even roots. -/
def rootHomologyPowerSumEnd (m q r : ℕ) : Module.End ℂ (RootHomologyModel q r) :=
  TensorProduct.map (rootOddPowerSumEnd m q) LinearMap.id +
    (2 : ℂ) • TensorProduct.map LinearMap.id (rootEvenPowerSumEnd m r)

/-- The actual exterior/symmetric tensor model and root-polynomial tensor model. -/
def rootFreeToRootEquiv (q r : ℕ) : RootFreeBidegree q r ≃ₗ[ℂ] RootHomologyModel q r :=
  TensorProduct.congr (exteriorPolynomialEquiv q) (rootEvenPolynomialEquiv r)

/-- Both sides use the same specified normalized exterior and symmetric bases. -/
theorem rootFreeToRootEquiv_source (q r : ℕ) (x : FreeBidegreeIndex q r →₀ ℂ) :
    rootFreeToRootEquiv q r (freeBidegreeSourceEquiv q r x) = freeBidegreeRootEquiv q r x := by
  have h : (rootFreeToRootEquiv q r).toLinearMap.comp (freeBidegreeSourceEquiv q r).toLinearMap =
      (freeBidegreeRootEquiv q r).toLinearMap := by
    apply Finsupp.lhom_ext
    intro b c
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,freeBidegreeSourceEquiv,
      freeBidegreeRootEquiv,LinearEquiv.trans_apply,Finsupp.domLCongr_single,
      Module.Basis.repr_symm_single,map_smul,Module.Basis.tensorProduct_apply',
      rootFreeToRootEquiv,TensorProduct.congr_tmul]
    congr 2
    change rootEvenPolynomialEquiv r
      ((rootEvenExponentEquiv r).symm (Finsupp.single (freeBidegreeIndexEquiv q r b).2 1)) = _
    simp only [rootEvenPolynomialEquiv,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
    rfl
  exact LinearMap.congr_fun h x

/-- Exact root-power-sum compatibility of the actual bidegree tensor model. -/
theorem rootFreeToRootEquiv_shift (m q r : ℕ) (x : RootFreeBidegree q r) :
    rootFreeToRootEquiv q r (rootFreeBidegreeShift m q r x) =
      rootHomologyPowerSumEnd m q r (rootFreeToRootEquiv q r x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul u p =>
    have ho : exteriorPolynomialEquiv q (exteriorDeriv q
        (LinearMap.mulLeft ℂ ((Polynomial.X : Polynomial ℂ)^m)) u) =
          rootOddPowerSumEnd m q (exteriorPolynomialEquiv q u) :=
      Subtype.ext (exteriorPolynomialEquiv_shift m q u)
    have he : rootEvenPolynomialEquiv r (rootEvenShiftEnd m r p) =
        rootEvenPowerSumEnd m r (rootEvenPolynomialEquiv r p) :=
      Subtype.ext (rootEvenPolynomialEquiv_shift m r p)
    simp only [rootFreeToRootEquiv,rootFreeBidegreeShift,rootHomologyPowerSumEnd,
      LinearMap.add_apply,LinearMap.smul_apply,TensorProduct.map_tmul,
      LinearMap.id_apply,map_add,map_smul,TensorProduct.congr_tmul,ho,he]

end KhanSL2.Macdonald
