module

public import KhanSL2.BGGBridge.BoundaryCompare
public import KhanSL2.BGG.FreeCESupport
public import KhanSL2.BGG.ColorRootEquivariance
public import KhanSL2.BGG.FreeCEBasis

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# M2's relative chains are the base-changed free CE chains

`J : Λ𝔩₊ ⊗ Λ(ε𝔩) ≃ PositiveCE.Cochain ⊗ Λ(ε𝔩)` is `exteriorEquiv ⊗ id`. It intertwines:
* the M2 boundary `LieChains.boundary` with the BGG free CE differential base-changed to the
  coefficients `Λ(ε𝔩)` (`J_boundary`);
* the M2 `𝔤`-action `relTheta` with the diagonal constant action (`J_relTheta`), so it matches
  the coinvariant relations (`map_J_genRelations`).

So `J` descends to an isomorphism of the relative complexes (`Jq`).
-/

noncomputable section

open scoped TensorProduct

namespace KhanSL2.BGGBridge

open KhanSL2.BGG KhanSL2.Current KhanSL2.FiniteExterior

/-- The two models of `Λ𝔩₊ ⊗ Λ(ε𝔩)`. -/
def J : GenChains ≃ₗ[ℂ] ChainN NB :=
  TensorProduct.congr exteriorEquiv.toLinearEquiv (LinearEquiv.refl ℂ NB)

@[simp] theorem J_tmul (ξ : ExteriorAlgebra ℂ plus) (ν : NB) : J (ξ ⊗ₜ ν) = exteriorEquiv ξ ⊗ₜ ν :=
  rfl

/-- The adjoint action of `y ∈ 𝔩₊` on the BGG model of `Λ𝔩₊`. -/
def adE (y : plus) : Module.End ℂ PositiveCE.Cochain :=
  exteriorEquiv.toLinearMap ∘ₗ LieChains.derivExt (LieModule.toEnd ℂ plus plus y) ∘ₗ
    exteriorEquiv.symm.toLinearMap

theorem adE_apply_exteriorEquiv (y : plus) (ξ : ExteriorAlgebra ℂ plus) :
    adE y (exteriorEquiv ξ) = exteriorEquiv (LieChains.derivExt (LieModule.toEnd ℂ plus plus y) ξ) := by
  simp only [adE, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply]

/-- The action `θ_y` in the BGG model. -/
def thetaE (y : plus) : Module.End ℂ (ChainN NB) :=
  diag (adE y) (LieModule.toEnd ℂ Current NB (y : Current))

theorem toEnd_plus_NB (y : plus) (ν : NB) :
    LieModule.toEnd ℂ plus NB y ν = LieModule.toEnd ℂ Current NB (y : Current) ν := rfl

set_option maxHeartbeats 1000000 in
theorem J_theta (y : plus) (ξ : GenChains) : J (LieChains.theta NB y ξ) = thetaE y (J ξ) := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul x ν =>
    have h1 : LieChains.theta NB y (x ⊗ₜ ν) =
        LieChains.derivExt (LieModule.toEnd ℂ plus plus y) x ⊗ₜ ν +
          x ⊗ₜ LieModule.toEnd ℂ plus NB y ν := rfl
    have h2 : thetaE y (exteriorEquiv x ⊗ₜ ν) =
        adE y (exteriorEquiv x) ⊗ₜ ν + exteriorEquiv x ⊗ₜ LieModule.toEnd ℂ Current NB (y : Current) ν :=
      rfl
    rw [h1, map_add, J_tmul, J_tmul, J_tmul, h2, adE_apply_exteriorEquiv, toEnd_plus_NB]
  | add ξ η hξ hη => rw [map_add, map_add, hξ, hη, map_add, map_add]

/-- Left multiplication by `ι y`, in the BGG model. -/
def wedgeE : plus →ₗ[ℂ] Module.End ℂ (ChainN NB) :=
  LinearMap.rTensorHom NB ∘ₗ LinearMap.mul ℂ PositiveCE.Cochain ∘ₗ exteriorEquiv.toLinearMap ∘ₗ
    ExteriorAlgebra.ι ℂ

theorem wedgeE_tmul (y : plus) (ω : PositiveCE.Cochain) (ν : NB) :
    wedgeE y (ω ⊗ₜ ν) = (exteriorEquiv (ExteriorAlgebra.ι ℂ y) * ω) ⊗ₜ ν := rfl

set_option maxHeartbeats 1000000 in
theorem J_wedgeLeft (y : plus) (ξ : GenChains) :
    J (LieChains.wedgeLeft NB y ξ) = wedgeE y (J ξ) := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul x ν =>
    rw [LieChains.wedgeLeft_tmul, J_tmul, J_tmul, wedgeE_tmul, map_mul]
  | add ξ η hξ hη => rw [map_add, map_add, hξ, hη, map_add, map_add]

/-! ## The base-changed differential, explicitly -/

theorem lieGenerator_coe (m : PositiveCE.Mode) :
    ((FreeCE.lieGenerator m : positive) : Current) = ((plusModeBasis m : plus) : Cur) := by
  rw [plusModeBasis_apply]
  rfl

theorem dC_tmul (S : Finset PositiveCE.Mode) (ω : PositiveCE.Cochain)
    (hω : supportModes ω ⊆ S) (ν : NB) :
    dC NB (ω ⊗ₜ ν) = PositiveCE.boundary ω ⊗ₜ ν -
      ∑ k ∈ S, PositiveCE.contract k ω ⊗ₜ ⁅((plusModeBasis k : plus) : Cur), ν⁆ := by
  rw [dC, base_tmul, FreeCE.differential_tmul_finite S 1 ω hω, TensorProduct.add_tmul,
    map_add, TensorProduct.sum_tmul, map_sum, ev_tmul_tmul, ract_one, Module.End.one_apply]
  simp only [ev_tmul_tmul, one_mul, FreeCE.ueGenerator, ract_ι, lieGenerator_coe,
    TensorProduct.tmul_neg, Finset.sum_neg_distrib]
  abel

theorem dC_one_tmul (ν : NB) : dC NB ((1 : PositiveCE.Cochain) ⊗ₜ ν) = 0 := by
  rw [dC, base_tmul, FreeCE.differential_tmul_one, TensorProduct.zero_tmul, map_zero]

theorem E_mul (a b : ExteriorAlgebra ℂ plus) :
    exteriorEquiv (a * b) = exteriorEquiv a * exteriorEquiv b := map_mul exteriorEquiv a b

theorem E_sub (a b : ExteriorAlgebra ℂ plus) :
    exteriorEquiv (a - b) = exteriorEquiv a - exteriorEquiv b := map_sub exteriorEquiv a b

theorem E_neg (a : ExteriorAlgebra ℂ plus) : exteriorEquiv (-a) = -exteriorEquiv a :=
  map_neg exteriorEquiv a

/-- Cartan's recursion for the BGG boundary of `Λ𝔩₊`, at a basis generator. -/
theorem bd_generator_mul (m : PositiveCE.Mode) (ω : PositiveCE.Cochain) :
    PositiveCE.boundary (FiniteExterior.generator m * ω) =
      -adE (plusModeBasis m) ω - FiniteExterior.generator m * PositiveCE.boundary ω := by
  obtain ⟨ξ, rfl⟩ := exteriorEquiv.surjective ω
  have hg : FiniteExterior.generator m = exteriorEquiv (ExteriorAlgebra.ι ℂ (plusModeBasis m)) :=
    (toE_ι_basis m).symm
  calc PositiveCE.boundary (FiniteExterior.generator m * exteriorEquiv ξ)
      = PositiveCE.boundary (exteriorEquiv (ExteriorAlgebra.ι ℂ (plusModeBasis m) * ξ)) := by
        rw [hg, ← E_mul]
    _ = exteriorEquiv (bdLambda (ExteriorAlgebra.ι ℂ (plusModeBasis m) * ξ)) :=
        (exteriorEquiv_bdLambda _).symm
    _ = exteriorEquiv (-LieChains.derivExt (LieModule.toEnd ℂ plus plus (plusModeBasis m)) ξ -
          ExteriorAlgebra.ι ℂ (plusModeBasis m) * bdLambda ξ) := by rw [bdLambda_ι_mul]
    _ = -adE (plusModeBasis m) (exteriorEquiv ξ) -
          FiniteExterior.generator m * PositiveCE.boundary (exteriorEquiv ξ) := by
        rw [E_sub, E_neg, E_mul, exteriorEquiv_bdLambda, adE_apply_exteriorEquiv, hg]

theorem contract_generator_mul (k m : PositiveCE.Mode) (ω : PositiveCE.Cochain) :
    PositiveCE.contract k (FiniteExterior.generator m * ω) =
      (if k = m then ω else 0) - FiniteExterior.generator m * PositiveCE.contract k ω := by
  exact contraction_generator_wedge PositiveCE.Mode.code PositiveCE.Mode.code_injective k m ω

theorem supportModes_generator_mul {S : Finset PositiveCE.Mode} (m : PositiveCE.Mode)
    {ω : PositiveCE.Cochain} (hω : supportModes ω ⊆ S) :
    supportModes (FiniteExterior.generator m * ω) ⊆ insert m S := by
  apply (FreeCE.supportModes_subset_iff _ _).mpr
  apply mul_mem_generatorsIn
  · exact generator_mem_generatorsIn _ m (by simp)
  · exact (FreeCE.supportModes_subset_iff _ _).mp (hω.trans (Finset.subset_insert m S))

theorem sum_ite_tmul {S : Finset PositiveCE.Mode} (m : PositiveCE.Mode) (hm : m ∈ S)
    (ω : PositiveCE.Cochain) (f : PositiveCE.Mode → NB) :
    ∑ k ∈ S, (if k = m then ω else 0) ⊗ₜ[ℂ] f k = ω ⊗ₜ[ℂ] f m := by
  rw [Finset.sum_eq_single m]
  · rw [if_pos rfl]
  · intro k _ hk
    rw [if_neg hk, TensorProduct.zero_tmul]
  · intro h
    exact absurd hm h

set_option maxHeartbeats 1000000 in
/-- **Cartan's recursion for the base-changed differential**, at a basis generator. -/
theorem dC_generator_mul (m : PositiveCE.Mode) (ω : PositiveCE.Cochain) (ν : NB) :
    dC NB ((FiniteExterior.generator m * ω) ⊗ₜ ν) =
      -thetaE (plusModeBasis m) (ω ⊗ₜ ν) -
        LinearMap.rTensor NB (LinearMap.mulLeft ℂ (FiniteExterior.generator m)) (dC NB (ω ⊗ₜ ν)) := by
  have hω : supportModes ω ⊆ insert m (supportModes ω) := Finset.subset_insert m _
  have hgω : supportModes (FiniteExterior.generator m * ω) ⊆ insert m (supportModes ω) :=
    supportModes_generator_mul m (subset_refl _)
  have hm : m ∈ insert m (supportModes ω) := Finset.mem_insert_self m _
  rw [dC_tmul _ _ hgω, dC_tmul _ ω hω, bd_generator_mul]
  simp only [contract_generator_mul, TensorProduct.sub_tmul, Finset.sum_sub_distrib,
    sum_ite_tmul m hm, thetaE, diag_tmul, map_sub, map_sum,
    LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, LieModule.toEnd_apply_apply,
    TensorProduct.neg_tmul]
  abel

/-- `θ` in the BGG model, linear in `y`. -/
def thetaEₗ : plus →ₗ[ℂ] Module.End ℂ (ChainN NB) :=
  LinearMap.rTensorHom NB ∘ₗ exteriorEquiv.toLinearEquiv.conj.toLinearMap ∘ₗ
      LieChains.derivExtₗ ∘ₗ (LieModule.toEnd ℂ plus plus : plus →ₗ[ℂ] Module.End ℂ plus) +
    LinearMap.lTensorHom PositiveCE.Cochain ∘ₗ
      (LieModule.toEnd ℂ Current NB : Current →ₗ[ℂ] Module.End ℂ NB) ∘ₗ
        (plus.incl : plus →ₗ⁅ℂ⁆ Cur).toLinearMap

theorem thetaEₗ_apply (y : plus) (z : ChainN NB) : thetaEₗ y z = thetaE y z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul ω ν => rfl
  | add z w hz hw => rw [map_add, map_add, hz, hw]

theorem dC_wedgeE_basis (m : PositiveCE.Mode) (z : ChainN NB) :
    dC NB (wedgeE (plusModeBasis m) z) + wedgeE (plusModeBasis m) (dC NB z) +
      thetaEₗ (plusModeBasis m) z = 0 := by
  have hg : exteriorEquiv (ExteriorAlgebra.ι ℂ (plusModeBasis m)) =
      FiniteExterior.generator m := toE_ι_basis m
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul ω ν =>
    have hw : ∀ z : ChainN NB, wedgeE (plusModeBasis m) z =
        LinearMap.rTensor NB (LinearMap.mulLeft ℂ (FiniteExterior.generator m)) z := by
      intro z
      rw [← hg]
      rfl
    rw [hw, hw, LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, dC_generator_mul,
      thetaEₗ_apply]
    abel
  | add z w hz hw =>
    have e : ∀ a b c a' b' c' : ChainN NB,
        (a + a') + (b + b') + (c + c') = (a + b + c) + (a' + b' + c') := by
      intros; abel
    simp only [map_add]
    rw [e, hz, hw, add_zero]

/-- **Cartan's recursion for the base-changed differential**, for every `y ∈ 𝔩₊`. -/
theorem dC_wedgeE (y : plus) (z : ChainN NB) :
    dC NB (wedgeE y z) = -thetaE y z - wedgeE y (dC NB z) := by
  have key : ∀ z : ChainN NB, dC NB (wedgeE y z) + wedgeE y (dC NB z) + thetaEₗ y z = 0 := by
    have hy : y ∈ Submodule.span ℂ (Set.range plusModeBasis) := by
      rw [plusModeBasis.span_eq]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, rfl⟩ := hy
      exact dC_wedgeE_basis m
    | zero => intro z; simp
    | add y y' _ _ h h' =>
      intro z
      have e := congrArg₂ (· + ·) (h z) (h' z)
      simp only [add_zero] at e
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, LinearMap.add_apply,
        map_add, ← e]
      abel
    | smul c y _ h =>
      intro z
      rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
        map_smul, ← smul_add, ← smul_add, h z, smul_zero]
  have h := key z
  rw [thetaEₗ_apply] at h
  rw [← sub_eq_zero, ← h]
  abel

set_option maxHeartbeats 4000000 in
/-- **`J` is a chain map.** -/
theorem J_boundary (ξ : GenChains) : J (LieChains.boundary NB ξ) = dC NB (J ξ) := by
  refine LieChains.chains_induction (k := ℂ) (L := plus) (M := NB)
    (P := fun ξ => J (LieChains.boundary NB ξ) = dC NB (J ξ)) ?_ ?_ ?_ ?_ ξ
  · simp
  · intro ν
    rw [LieChains.boundary_one_tmul, map_zero, J_tmul, map_one, dC_one_tmul]
  · intro ξ η hξ hη
    rw [(LieChains.boundary NB).map_add, J.map_add, J.map_add, hξ, hη, (dC NB).map_add]
  · intro y ξ hξ
    rw [LieChains.boundary_wedgeLeft, map_sub, map_neg, J_theta, J_wedgeLeft, J_wedgeLeft, hξ,
      dC_wedgeE]

/-! ## The `𝔤`-action and the relations -/

theorem colorAction_exteriorEquiv (a : Fin 3) (ξ : ExteriorAlgebra ℂ plus) :
    PositiveCE.colorAction a (exteriorEquiv ξ) =
      exteriorEquiv (LieChains.derivExt (relD a) ξ) := by
  have hgen : (PositiveCE.colorAction a).comp (exteriorEquiv.toLinearMap ∘ₗ ExteriorAlgebra.ι ℂ) =
      exteriorEquiv.toLinearMap ∘ₗ ExteriorAlgebra.ι ℂ ∘ₗ relD a := by
    apply plusBasis.ext
    rintro ⟨j, b⟩
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, plusBasis_apply,
      relD_plusCur, map_sum, map_smul, exteriorEquiv_ι_plusCur, PositiveCE.colorAction_generator]
  induction ξ using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [AlgEquiv.commutes, LieChains.derivExt_algebraMap, map_zero, Algebra.algebraMap_eq_smul_one,
      map_smul, PositiveCE.colorAction_one, smul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | ι_mul x y hx =>
    have h1 := LinearMap.congr_fun hgen y
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply] at h1
    change PositiveCE.colorAction a (exteriorEquiv (ExteriorAlgebra.ι ℂ y * x)) = _
    rw [map_mul, PositiveCE.colorAction_mul, h1, hx, LieChains.derivExt_ι_mul, map_add, map_mul,
      map_mul]

set_option maxHeartbeats 1000000 in
theorem J_relTheta (a : Fin 3) (ξ : GenChains) :
    J (relTheta a ξ) = actC NB (MatrixSL2.color a) (J ξ) := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul x ν =>
    rw [relTheta, LieChains.lieDeriv_tmul, map_add, J_tmul, J_tmul, J_tmul, actC, diag_tmul,
      ColorRoot.positiveAction_color, colorAction_exteriorEquiv]
    rfl
  | add ξ η hξ hη => rw [map_add, map_add, hξ, hη, map_add, map_add]

theorem actC_add (x x' : G) (z : ChainN NB) :
    actC NB (x + x') z = actC NB x z + actC NB x' z := by
  simp only [actC, diag, map_add, LinearMap.rTensor_add, LinearMap.lTensor_add,
    LinearMap.add_apply]
  abel

theorem actC_smul (c : ℂ) (x : G) (z : ChainN NB) :
    actC NB (c • x) z = c • actC NB x z := by
  simp only [actC, diag, map_smul, LinearMap.rTensor_smul, LinearMap.lTensor_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_add]

theorem actC_sum (x : G) (z : ChainN NB) :
    actC NB x z = ∑ a : Fin 3, FreeCE.colorBasis.repr x a • actC NB (MatrixSL2.color a) z := by
  conv_lhs => rw [← FreeCE.colorBasis.sum_repr x]
  induction (Finset.univ : Finset (Fin 3)) using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h := actC_smul (0 : ℂ) 0 z
    rwa [zero_smul, zero_smul] at h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, actC_add, actC_smul, ih,
      FreeCE.colorBasis_apply]

/-- **`J` matches the coinvariant relations.** -/
theorem map_J_genRelations : genRelations.map J.toLinearMap = relC NB := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply iSup_le
    rintro a _ ⟨ξ, rfl⟩
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, J_relTheta]
    exact Submodule.mem_iSup_of_mem (MatrixSL2.color a) ⟨J ξ, rfl⟩
  · apply iSup_le
    rintro x _ ⟨z, rfl⟩
    rw [actC_sum]
    apply Submodule.sum_mem
    intro a _
    apply Submodule.smul_mem
    refine ⟨relTheta a (J.symm z), Submodule.mem_iSup_of_mem a ⟨J.symm z, rfl⟩, ?_⟩
    rw [LinearEquiv.coe_coe, J_relTheta, LinearEquiv.apply_symm_apply]

/-- `J` on the relative chains. -/
def Jq : RelChains ≃ₗ[ℂ] ChainN NB ⧸ relC NB :=
  Submodule.Quotient.equiv genRelations (relC NB) J map_J_genRelations

theorem Jq_mk (ξ : GenChains) :
    Jq (Submodule.Quotient.mk ξ) = Submodule.Quotient.mk (J ξ) := rfl

theorem dCq_Jq (x : RelChains) : dCq NB (Jq x) = Jq (relBoundary x) := by
  induction x using Submodule.Quotient.induction_on with
  | H ξ =>
    have h1 : relBoundary (Submodule.Quotient.mk ξ) =
        (Submodule.Quotient.mk (LieChains.boundary NB ξ) : RelChains) := rfl
    have h2 : dCq NB (Submodule.Quotient.mk (J ξ)) = Submodule.Quotient.mk (dC NB (J ξ)) := rfl
    rw [h1, Jq_mk, Jq_mk, h2, J_boundary]

end KhanSL2.BGGBridge
