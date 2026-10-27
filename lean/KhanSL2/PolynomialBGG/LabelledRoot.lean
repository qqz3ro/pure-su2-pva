module

public import KhanSL2.PolynomialBGG.ProjectiveModelLinear
public import KhanSL2.PolynomialBGG.ProjectiveModelColors

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped TensorProduct
namespace KhanSL2.PolynomialBGG
open BGG BGGBridge Current Conditional

/-- The finite color and harmonic factor of a labelled BGG tensor. -/
abbrev HarmonicColor (B p : ℕ) := Color B ⊗[ℂ] TauCeti.Sl2Std ℂ (2*p)

/-- The constant Lie action on the finite factor. -/
def harmonicColorAct (B p : ℕ) (x : G) : Module.End ℂ (HarmonicColor B p) :=
  diag (colorDeriv B (LieModule.toEnd ℂ G G x))
    (LieModule.toEnd ℂ G (TauCeti.Sl2Std ℂ (2*p)) x)

/-- Reassociate the actual labelled tensor model, retaining coefficient linearity. -/
def labelledRootEquiv (B p : ℕ) : LabelledModel B p ≃ₗ[CoefficientRing B]
    RootPolynomial B ⊗[ℂ] HarmonicColor B p :=
  (TensorProduct.AlgebraTensorModule.congr (rootTensorLinearEquiv B)
    (LinearEquiv.refl ℂ (TauCeti.Sl2Std ℂ (2*p)))).trans
      (TensorProduct.AlgebraTensorModule.assoc ℂ ℂ (CoefficientRing B)
        (RootPolynomial B) (Color B) (TauCeti.Sl2Std ℂ (2*p)))

@[simp] theorem labelledRootEquiv_tmul (B p : ℕ) (u : ⨂[ℂ]^B Cur)
    (v : TauCeti.Sl2Std ℂ (2*p)) :
    labelledRootEquiv B p (u ⊗ₜ[ℂ] v) =
      TensorProduct.AlgebraTensorModule.assoc ℂ ℂ (CoefficientRing B)
        (RootPolynomial B) (Color B) (TauCeti.Sl2Std ℂ (2*p))
        (rootTensorEquiv B u ⊗ₜ[ℂ] v) := rfl

@[simp] theorem labelledRootEquiv_symm_tmul (B p : ℕ) (f : RootPolynomial B)
    (c : Color B) (v : TauCeti.Sl2Std ℂ (2*p)) :
    labelledRootEquiv B p ((rootTensorEquiv B).symm (f ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] v) =
      f ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] v) := by
  rw [labelledRootEquiv_tmul, LinearEquiv.apply_symm_apply]
  rfl

/-- The diagonal Lie action acts only on the finite factor in root coordinates. -/
theorem labelledRootEquiv_act (B p : ℕ) (x : G) (u : LabelledModel B p) :
    labelledRootEquiv B p (labelledActLinear B p x u) =
      TensorProduct.AlgebraTensorModule.lTensor (CoefficientRing B) (RootPolynomial B)
        (harmonicColorAct B p x) (labelledRootEquiv B p u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul u v =>
    obtain ⟨w, rfl⟩ := (rootTensorEquiv B).symm.surjective u
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz =>
      simp only [map_add, TensorProduct.add_tmul, hy, hz]
    | tmul f c =>
      have hd : tensorDeriv B (adCur (constant x)) ((rootTensorEquiv B).symm (f ⊗ₜ[ℂ] c)) =
          (rootTensorEquiv B).symm (f ⊗ₜ[ℂ] colorDeriv B (LieModule.toEnd ℂ G G x) c) := by
        apply (rootTensorEquiv B).injective
        rw [rootTensorEquiv_constantLie, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply, LinearMap.lTensor_tmul]
      change labelledRootEquiv B p (labelledAct B p x
          ((rootTensorEquiv B).symm (f ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] v)) = _
      rw [labelledAct, diag_tmul, map_add, hd, labelledRootEquiv_symm_tmul,
        labelledRootEquiv_symm_tmul, labelledRootEquiv_symm_tmul]
      simp only [TensorProduct.AlgebraTensorModule.lTensor_tmul, harmonicColorAct,
        diag_tmul, TensorProduct.tmul_add]

/-- Linear equivalences intertwining a family identify its relation submodules. -/
theorem actionRelations_map_equiv {R M N I : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (a : I → Module.End R M) (b : I → Module.End R N) (e : M ≃ₗ[R] N)
    (h : ∀ x u, e (a x u) = b x (e u)) :
    (actionRelations a).map e.toLinearMap = actionRelations b := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply actionRelations_le_comap a b e.toLinearMap
    intro x
    exact LinearMap.ext (h x)
  · have hs : actionRelations b ≤ (actionRelations a).comap e.symm.toLinearMap := by
      apply actionRelations_le_comap b a e.symm.toLinearMap
      intro x
      apply LinearMap.ext
      intro u
      apply e.injective
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
        using (h x (e.symm u)).symm
    intro u hu
    exact ⟨e.symm u, hs hu, e.apply_symm_apply u⟩

/-- The actual labelled relation space becomes precisely the polynomial-valued color relations. -/
theorem labelledRelations_map_root (B p : ℕ) :
    (labelledRelationsLinear B p).map (labelledRootEquiv B p).toLinearMap =
      actionRelations (fun x : G => TensorProduct.AlgebraTensorModule.lTensor
        (CoefficientRing B) (RootPolynomial B) (harmonicColorAct B p x)) :=
  actionRelations_map_equiv (labelledActLinear B p) _ (labelledRootEquiv B p)
    (labelledRootEquiv_act B p)

/-- A coefficient-linear identification of actual labelled coinvariants with color coinvariants. -/
def labelledCoinvariantsRootEquiv (B p : ℕ) :
    (LabelledModel B p ⧸ labelledRelationsLinear B p) ≃ₗ[CoefficientRing B]
      (RootPolynomial B ⊗[ℂ] HarmonicColor B p) ⧸
        actionRelations (fun x : G => TensorProduct.AlgebraTensorModule.lTensor
          (CoefficientRing B) (RootPolynomial B) (harmonicColorAct B p x)) :=
  Submodule.Quotient.equiv _ _ (labelledRootEquiv B p) (labelledRelations_map_root B p)

/-- No additional assumption on the color coinvariants is required for projectivity. -/
theorem labelledCoinvariants_projective (B p : ℕ)
    [Module.Projective (CoefficientRing B) (RootPolynomial B)] :
    Module.Projective (CoefficientRing B)
      (LabelledModel B p ⧸ labelledRelationsLinear B p) := by
  have := tensorActionCoinvariants_projective (R := CoefficientRing B)
    (P := RootPolynomial B) (harmonicColorAct B p)
  exact Module.Projective.of_equiv' (labelledCoinvariantsRootEquiv B p).symm

end KhanSL2.PolynomialBGG
