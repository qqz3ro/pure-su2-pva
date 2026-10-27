module

public import KhanSL2.SymmetricFamily.CoefficientAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! In the labelled-root family, a mode-z^n current acts in slot i by its
color action multiplied by the actual labelled root t_i^n. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily
open Macdonald PolynomialBGG BGG Current

/-- A color endomorphism in one specified labelled slot. -/
def colorSlot (k : ℕ) (i : Fin k) (D : Module.End ℂ BGG.G) : Module.End ℂ (Color k) :=
  (Pi.basisFun ℂ (Fin k → Fin 3)).constr ℂ fun c =>
    ∑ b : Fin 3, rootBasis.repr (D (rootBasis (c i))) b •
      Pi.basisFun ℂ (Fin k → Fin 3) (Function.update c i b)

@[simp] theorem colorSlot_basis (k : ℕ) (i : Fin k) (D : Module.End ℂ BGG.G)
    (c : Fin k → Fin 3) :
    colorSlot k i D (Pi.basisFun ℂ (Fin k → Fin 3) c) =
      ∑ b : Fin 3, rootBasis.repr (D (rootBasis (c i))) b •
        Pi.basisFun ℂ (Fin k → Fin 3) (Function.update c i b) :=
  Module.Basis.constr_basis _ _ _ _

/-- Apply a color map and multiply the current mode by z^n. -/
def modeColorEnd (n : ℕ) (D : Module.End ℂ BGG.G) : Module.End ℂ BGG.Current :=
  (Modules.coefficientShift n).comp (LinearMap.lTensor (Polynomial ℂ) D)

/-- The explicit polynomial evaluation action on all labelled slots. -/
def labelledModeEnd (k n : ℕ) (D : Module.End ℂ BGG.G) : Module.End ℂ (Labelled k) :=
  ∑ i : Fin k, TensorProduct.map
    (LinearMap.mulLeft ℂ (show RootPolynomial k from MvPolynomial.X i ^ n)) (colorSlot k i D)

theorem modeColorEnd_basis (n : ℕ) (D : Module.End ℂ BGG.G) (a : ℕ) (c : Fin 3) :
    modeColorEnd n D (currentBasis (a,c)) =
      ∑ b : Fin 3, rootBasis.repr (D (rootBasis c)) b • currentBasis (a+n,b) := by
  rw [modeColorEnd, LinearMap.comp_apply, currentColorMap_basis, map_sum]
  simp only [map_smul, BGGBridge.TopAlternants.coefficientShift_currentBasis, Nat.add_comm n a]

/-- Expand the actual mode-color derivation on a labelled current word. -/
theorem tensorModeEnd_word (k n : ℕ) (D : Module.End ℂ BGG.G)
    (a : Fin k → ℕ) (c : Fin k → Fin 3) :
    tensorDeriv k (modeColorEnd n D)
      (PiTensorProduct.tprod ℂ (fun i => currentBasis (a i,c i))) =
        ∑ i : Fin k, ∑ b : Fin 3, rootBasis.repr (D (rootBasis (c i))) b •
          PiTensorProduct.tprod ℂ
            (fun j => currentBasis (Function.update a i (a i+n) j, Function.update c i b j)) := by
  classical
  rw [tensorDeriv_tprod]
  apply Finset.sum_congr rfl
  intro i _
  rw [modeColorEnd_basis, (PiTensorProduct.tprod ℂ).map_update_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [(PiTensorProduct.tprod ℂ).map_update_smul]
  congr 1
  congr 1
  funext j
  by_cases hji : j = i
  · subst j; simp
  · simp [Function.update_of_ne hji]

/-- The actual tensor derivation is the explicit sum of root-valued color actions. -/
theorem rootTensorEquiv_modeColorEnd (k n : ℕ) (D : Module.End ℂ BGG.G)
    (x : ⨂[ℂ]^k BGG.Current) :
    rootTensorEquiv k (tensorDeriv k (modeColorEnd n D) x) =
      labelledModeEnd k n D (rootTensorEquiv k x) := by
  have h : (rootTensorEquiv k).toLinearMap.comp (tensorDeriv k (modeColorEnd n D)) =
      (labelledModeEnd k n D).comp (rootTensorEquiv k).toLinearMap := by
    apply (tensorCurrentBasis k).ext
    intro q
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, tensorCurrentBasis_apply]
    rw [tensorModeEnd_word k n D (fun i => (q i).1) (fun i => (q i).2), map_sum]
    simp only [map_sum, map_smul, rootTensorEquiv_word, rootTensorEquiv_tprod,
      labelledModeEnd, LinearMap.sum_apply, TensorProduct.map_tmul, LinearMap.mulLeft_apply,
      colorSlot_basis, TensorProduct.tmul_sum, TensorProduct.tmul_smul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro b _
    congr 2
    change (MvPolynomial.monomial
      (Finsupp.equivFunOnFinite.symm (Function.update (fun j => (q j).1) i ((q i).1+n))) 1 :
      RootPolynomial k) = MvPolynomial.X i ^ n *
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun j => (q j).1)) 1
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]
    have hd : Finsupp.equivFunOnFinite.symm
        (Function.update (fun j => (q j).1) i ((q i).1+n)) =
        Finsupp.single i n + Finsupp.equivFunOnFinite.symm (fun j => (q j).1) := by
      ext j
      by_cases hji : j = i
      · subst j; simp [Nat.add_comm]
      · simp [hji, Ne.symm hji, Function.update_of_ne hji]
    exact congrArg (fun d => (MvPolynomial.monomial d 1 : RootPolynomial k)) hd
  exact LinearMap.congr_fun h x

/-- A mode current's adjoint endomorphism is the corresponding shifted color action. -/
theorem ad_mode_eq_modeColorEnd (n : ℕ) (x : BGG.G) :
    LieAlgebra.ad ℂ BGG.Current (BGG.mode n x) =
      modeColorEnd n (LieAlgebra.ad ℂ BGG.G x) := by
  apply currentBasis.ext
  rintro ⟨a,c⟩
  simp only [LieAlgebra.ad_apply, currentBasis_apply, BGG.mode_lie, modeColorEnd,
    LinearMap.comp_apply, BGG.mode_apply, LinearMap.lTensor_tmul,
    Modules.coefficientShift_tmul, pow_add]
  rfl

/-- The symmetric/labelled-root comparison intertwines the full actual current action on every mode. -/
theorem symmetricLabelledEquiv_mode_lie (k n : ℕ) (x : BGG.G) (p : symmetricPower k) :
    (symmetricLabelledEquiv k ⁅BGG.mode n x,p⁆).val =
      labelledModeEnd k n (LieAlgebra.ad ℂ BGG.G x) (symmetricLabelledEquiv k p).val := by
  change rootTensorEquiv k (symmetricToTensor k
    (symmetricDegreeDeriv k (LieAlgebra.ad ℂ BGG.Current (BGG.mode n x)) p)) = _
  rw [symmetricToTensor_symmetricDegreeDeriv, ad_mode_eq_modeColorEnd,
    rootTensorEquiv_modeColorEnd]
  rfl

end KhanSL2.SymmetricFamily
