module

public import KhanSL2.Factorization.WeightedRootModelTensor
public import KhanSL2.Macdonald.RootPolynomialAction

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace KhanSL2.Factorization.WeightedRootModel
open MvPolynomial Macdonald

/-- The exact tensor-model power-sum operator becomes multiplication by the
weighted root power sum, with odd weight one and even weight two. -/
theorem rootHomologyModelEquiv_powerSum (m q r : ℕ) (x : RootHomologyModel q r) :
    (rootHomologyModelEquiv q r (rootHomologyPowerSumEnd m q r x)).val =
      weightedPowerSum q r m * (rootHomologyModelEquiv q r x).val := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p t =>
    simp only [rootHomologyPowerSumEnd,LinearMap.add_apply,LinearMap.smul_apply,
      TensorProduct.map_tmul,LinearMap.id_apply,map_add,map_smul,
      Submodule.coe_add,Submodule.coe_smul,rootHomologyModelEquiv_tmul,
      rootOddPowerSumEnd_val,rootEvenPowerSumEnd_val]
    change (rename Sum.inl (psum (Fin q) ℂ m * p.val) : MvPolynomial (Fin q ⊕ Fin r) ℂ) *
        rename Sum.inr t.val + (2 : ℂ) •
        (rename Sum.inl p.val * rename Sum.inr (psum (Fin r) ℂ m * t.val)) = _
    simp only [map_mul,weightedPowerSum]
    norm_num only [Algebra.smul_def,map_ofNat]
    ring
  | add x y hx hy =>
    simp only [map_add,Submodule.coe_add,hx,hy,mul_add]

/-- The actual root-homology power sum is precisely the original R_B scalar,
not an action chosen only up to a change of coordinates. -/
theorem rootHomologyModelEquiv_powerSum_scalar (m q r : ℕ) (x : RootHomologyModel q r) :
    rootHomologyModelEquiv q r (rootHomologyPowerSumEnd m q r x) =
      (Modules.elementaryAlgEquiv (q+2*r)).symm (Modules.powerSum (q+2*r) m) •
        rootHomologyModelEquiv q r x := by
  apply Subtype.ext
  rw [signedInvariant_smul_val,weightedRootMap_powerSum]
  exact rootHomologyModelEquiv_powerSum m q r x

end KhanSL2.Factorization.WeightedRootModel
