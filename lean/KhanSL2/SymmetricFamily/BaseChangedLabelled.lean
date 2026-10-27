module

public import KhanSL2.SymmetricFamily.TensorBaseChange
public import KhanSL2.SymmetricFamily.RootPermutation

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! The original coefficient tensor family after base change, in explicit root
and color coordinates. This comparison retains the actual permutation maps. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Conditional

variable (k : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB k) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB k) A]

/-- Labelled roots and finite color tensors over the actual coefficient algebra. -/
abbrev BaseLabelled := RootBase k A ⊗[ℂ] Color k

/-- Reassociate the actual root/color tensor equivalence after scalar extension. -/
def baseRootTensorEquiv :
    A ⊗[Depth.RB k] (⨂[ℂ]^k BGG.Current) ≃ₗ[A] BaseLabelled k A :=
  ((rootTensorLinearEquiv k).baseChange (Depth.RB k) A).trans
    (TensorProduct.AlgebraTensorModule.assoc ℂ (Depth.RB k) A A
      (RootPolynomial k) (Color k)).symm

@[simp] theorem baseRootTensorEquiv_tmul (a : A) (u : ⨂[ℂ]^k BGG.Current) :
    baseRootTensorEquiv k A (a ⊗ₜ[Depth.RB k] u) =
      (TensorProduct.AlgebraTensorModule.assoc ℂ (Depth.RB k) A A
        (RootPolynomial k) (Color k)).symm (a ⊗ₜ[Depth.RB k] rootTensorEquiv k u) := rfl

@[simp] theorem baseRootTensorEquiv_symm_root_tmul (a : A) (p : RootPolynomial k) (c : Color k) :
    baseRootTensorEquiv k A
      (a ⊗ₜ[Depth.RB k] (rootTensorEquiv k).symm (p ⊗ₜ[ℂ] c)) =
        (a ⊗ₜ[Depth.RB k] p) ⊗ₜ[ℂ] c := by
  rw [baseRootTensorEquiv_tmul, LinearEquiv.apply_symm_apply]
  rfl

/-- Simultaneously permute actual base-changed roots and their color slots. -/
def baseLabelledPermute (σ : Equiv.Perm (Fin k)) : Module.End A (BaseLabelled k A) :=
  TensorProduct.AlgebraTensorModule.map
    (baseRootPermutation k A σ.symm).toLinearMap (colorPermute σ)

@[simp] theorem baseLabelledPermute_tmul (σ : Equiv.Perm (Fin k))
    (p : RootBase k A) (c : Color k) :
    baseLabelledPermute k A σ (p ⊗ₜ[ℂ] c) =
      baseRootPermutation k A σ.symm p ⊗ₜ[ℂ] colorPermute σ c := rfl

/-- The actual slot action becomes simultaneous root/color permutation after every base change. -/
theorem baseRootTensorEquiv_permute (σ : Equiv.Perm (Fin k))
    (x : A ⊗[Depth.RB k] (⨂[ℂ]^k BGG.Current)) :
    baseRootTensorEquiv k A ((tensorPermutationLinear k σ).baseChange A x) =
      baseLabelledPermute k A σ (baseRootTensorEquiv k A x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a u =>
    obtain ⟨q,rfl⟩ := (rootTensorEquiv k).symm.surjective u
    induction q using TensorProduct.induction_on with
    | zero => simp
    | add q z hq hz => simp only [map_add, TensorProduct.tmul_add, hq, hz]
    | tmul p c =>
      rw [LinearMap.baseChange_tmul, baseRootTensorEquiv_tmul]
      change (TensorProduct.AlgebraTensorModule.assoc ℂ (Depth.RB k) A A
        (RootPolynomial k) (Color k)).symm
          (a ⊗ₜ[Depth.RB k] rootTensorEquiv k
            (tensorPermute σ ((rootTensorEquiv k).symm (p ⊗ₜ[ℂ] c)))) = _
      rw [rootTensorEquiv_permute, LinearEquiv.apply_symm_apply]
      simp only [labelledPermute, TensorProduct.map_tmul,
        TensorProduct.AlgebraTensorModule.assoc_symm_tmul,
        baseRootTensorEquiv_symm_root_tmul, baseLabelledPermute_tmul,
        baseRootPermutation_tmul]
      rfl

/-- An actual intertwining equivalence restricts to the simultaneous fixed modules. -/
def fixedOperatorsEquiv {R : Type*} [CommRing R]
    {M N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    {ι : Type*} (ρ : ι → Module.End R M) (τ : ι → Module.End R N)
    (e : M ≃ₗ[R] N) (he : ∀ i x, e (ρ i x) = τ i (e x)) :
    fixedOperators ρ ≃ₗ[R] fixedOperators τ where
  toFun x := ⟨e x.val, fun i => (he i x.val).symm.trans (congrArg e (x.property i))⟩
  invFun y := ⟨e.symm y.val, fun i => by
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, y.property i]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (e.map_add x.val y.val)
  map_smul' r x := Subtype.ext (e.map_smul r x.val)

/-- Actual symmetric coefficients over A are exactly the explicit simultaneous
root/color invariants. The map is the original normalized tensor section. -/
def symmetricBaseChangedLabelledEquiv :
    A ⊗[Depth.RB k] Macdonald.symmetricPower k ≃ₗ[A]
      fixedOperators (baseLabelledPermute k A) :=
  (symmetricBaseChangeTensorEquiv k A).trans
    (fixedOperatorsEquiv _ _ (baseRootTensorEquiv k A) (baseRootTensorEquiv_permute k A))

end KhanSL2.SymmetricFamily
