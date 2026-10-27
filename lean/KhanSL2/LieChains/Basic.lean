module

public import KhanSL2.LieChains.DerivExt
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.TensorProduct.Basic

@[expose] public section

/-!
# Chevalley–Eilenberg chains in all degrees

For a Lie algebra `L` over `k` and an `L`-module `M`, the chains are
`ΛL ⊗[k] M`. Write `ε y` for left multiplication by `ι y` on the first factor
and `θ y` for the action of `y` (the adjoint derivation on `ΛL`, the module
action on `M`). The CE boundary is the unique operator with

* `d (1 ⊗ m) = 0`,
* `d (ε y ξ) = - θ y ξ - ε y (d ξ)`,

defined by `CliffordAlgebra.foldr'`. These are Cartan's identities for chains.
The square-zero property follows by induction from them, after showing that
every Lie derivative `θ` commutes with `d`.
-/

noncomputable section

namespace KhanSL2.LieChains

open ExteriorAlgebra TensorProduct

variable (k : Type*) [CommRing k]
variable (L : Type*) [LieRing L] [LieAlgebra k L]
variable (M : Type*) [AddCommGroup M] [Module k M]

/-- CE chains of `L` with coefficients in `M`, all degrees together. -/
abbrev Chains := ExteriorAlgebra k L ⊗[k] M

variable {k L M}

/-- The Lie derivative attached to an endomorphism `D` of `L` and `S` of `M`. -/
def lieDeriv (D : Module.End k L) (S : Module.End k M) : Module.End k (Chains k L M) :=
  LinearMap.rTensor M (derivExt D) + LinearMap.lTensor (ExteriorAlgebra k L) S

@[simp] theorem lieDeriv_tmul (D : Module.End k L) (S : Module.End k M)
    (x : ExteriorAlgebra k L) (m : M) :
    lieDeriv D S (x ⊗ₜ m) = derivExt D x ⊗ₜ m + x ⊗ₜ S m := rfl

variable (k L M) in
/-- The Lie derivative, linear in the pair of endomorphisms. -/
def lieDerivₗ : (Module.End k L × Module.End k M) →ₗ[k] Module.End k (Chains k L M) :=
  (LinearMap.rTensorHom M ∘ₗ derivExtₗ ∘ₗ LinearMap.fst k _ _) +
    (LinearMap.lTensorHom (ExteriorAlgebra k L) ∘ₗ LinearMap.snd k _ _)

theorem lieDerivₗ_apply (p : Module.End k L × Module.End k M) :
    lieDerivₗ k L M p = lieDeriv p.1 p.2 := rfl

variable (M) in
/-- Left exterior multiplication by `y` on chains. -/
def wedgeLeft (y : L) : Module.End k (Chains k L M) :=
  LinearMap.rTensor M (LinearMap.mulLeft k (ι k y))

@[simp] theorem wedgeLeft_tmul (y : L) (x : ExteriorAlgebra k L) (m : M) :
    wedgeLeft M y (x ⊗ₜ m) = (ι k y * x) ⊗ₜ m := rfl

variable (k L M) in
/-- `wedgeLeft`, linear in `y`. -/
def wedgeLeftₗ : L →ₗ[k] Module.End k (Chains k L M) :=
  LinearMap.rTensorHom M ∘ₗ LinearMap.mul k (ExteriorAlgebra k L) ∘ₗ ι k

theorem wedgeLeftₗ_apply (y : L) : wedgeLeftₗ k L M y = wedgeLeft M y := rfl

theorem wedgeLeft_wedgeLeft (y : L) (ξ : Chains k L M) :
    wedgeLeft M y (wedgeLeft M y ξ) = 0 := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul x m => simp [← mul_assoc, ι_sq_zero]
  | add ξ η hξ hη => simp only [map_add, hξ, hη, add_zero]

/-- `[θ(D,S), ε y] = ε (D y)`. -/
theorem lieDeriv_wedgeLeft (D : Module.End k L) (S : Module.End k M) (y : L)
    (ξ : Chains k L M) :
    lieDeriv D S (wedgeLeft M y ξ) = wedgeLeft M y (lieDeriv D S ξ) + wedgeLeft M (D y) ξ := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul x m =>
    simp only [wedgeLeft_tmul, lieDeriv_tmul, derivExt_ι_mul, map_add, add_tmul]
    abel
  | add ξ η hξ hη => simp only [map_add, hξ, hη]; abel

/-- Lie derivatives compose like their endomorphisms. -/
theorem lieDeriv_commutator (D D' : Module.End k L) (S S' : Module.End k M)
    (ξ : Chains k L M) :
    lieDeriv D S (lieDeriv D' S' ξ) - lieDeriv D' S' (lieDeriv D S ξ) =
      lieDeriv (D * D' - D' * D) (S * S' - S' * S) ξ := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul x m =>
    simp only [lieDeriv_tmul, map_add, add_tmul, tmul_add, ← derivExt_commutator,
      LinearMap.sub_apply, Module.End.mul_apply, sub_tmul, tmul_sub]
    abel
  | add ξ η hξ hη => simp only [map_add, ← hξ, ← hη]; abel

variable [LieRingModule L M] [LieModule k L M]

variable (M) in
/-- The action of `y : L` on chains. -/
def theta (y : L) : Module.End k (Chains k L M) :=
  lieDeriv (LieModule.toEnd k L L y) (LieModule.toEnd k L M y)

variable (k L M) in
/-- `theta`, linear in `y`. -/
def thetaₗ : L →ₗ[k] Module.End k (Chains k L M) :=
  lieDerivₗ k L M ∘ₗ
    ((LieModule.toEnd k L L : L →ₗ[k] Module.End k L).prod
      (LieModule.toEnd k L M : L →ₗ[k] Module.End k M))

theorem thetaₗ_apply (y : L) : thetaₗ k L M y = theta M y := rfl

/-! ## The boundary -/

/-- One step of the boundary recursion: `(x, Dx) ↦ (m ↦ -θ y (x ⊗ m) - ε y (Dx m))`. -/
def bdStep : L →ₗ[k] (ExteriorAlgebra k L × (M →ₗ[k] Chains k L M)) →ₗ[k]
    (M →ₗ[k] Chains k L M) :=
  LinearMap.mk₂ k
    (fun y p => -(theta M y ∘ₗ TensorProduct.mk k (ExteriorAlgebra k L) M p.1) -
      wedgeLeft M y ∘ₗ p.2)
    (fun y y' p => by
      ext m
      simp only [← thetaₗ_apply, ← wedgeLeftₗ_apply, map_add]
      simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.comp_apply,
        LinearMap.add_apply]
      abel)
    (fun c y p => by
      ext m
      simp only [← thetaₗ_apply, ← wedgeLeftₗ_apply, map_smul]
      simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.comp_apply,
        LinearMap.smul_apply, smul_sub, smul_neg])
    (fun y p p' => by
      ext m
      simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.sub_apply,
        LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.add_apply, TensorProduct.mk_apply,
        add_tmul]
      abel)
    (fun c y p => by
      ext m
      simp only [Prod.smul_fst, Prod.smul_snd, LinearMap.sub_apply,
        LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.smul_apply,
        TensorProduct.mk_apply, ← smul_tmul', map_smul, smul_sub, smul_neg])

theorem bdStep_apply (y : L) (x : ExteriorAlgebra k L) (F : M →ₗ[k] Chains k L M) (m : M) :
    bdStep y (x, F) m = -theta M y (x ⊗ₜ m) - wedgeLeft M y (F m) := rfl

theorem theta_wedgeLeft_self (y : L) (ξ : Chains k L M) :
    theta M y (wedgeLeft M y ξ) = wedgeLeft M y (theta M y ξ) := by
  rw [theta, lieDeriv_wedgeLeft]
  simp [wedgeLeft]

theorem bdStep_cond (y : L) (x : ExteriorAlgebra k L) (F : M →ₗ[k] Chains k L M) :
    bdStep y (ι k y * x, bdStep y (x, F)) = 0 := by
  ext m
  rw [LinearMap.zero_apply, bdStep_apply, bdStep_apply]
  have h1 : (ι k y * x) ⊗ₜ[k] m = wedgeLeft M y (x ⊗ₜ m) := rfl
  rw [h1, theta_wedgeLeft_self, map_sub, map_neg, wedgeLeft_wedgeLeft]
  abel

/-- The recursion, before tensoring with the coefficient. -/
def bdAux : ExteriorAlgebra k L →ₗ[k] (M →ₗ[k] Chains k L M) :=
  CliffordAlgebra.foldr' (N := M →ₗ[k] Chains k L M) (0 : QuadraticForm k L) bdStep
    (fun y x F => by rw [QuadraticMap.zero_apply, zero_smul]; exact bdStep_cond y x F) 0

variable (M) in
/-- The Chevalley–Eilenberg boundary on chains. -/
def boundary : Module.End k (Chains k L M) := TensorProduct.lift bdAux

@[simp] theorem boundary_algebraMap_tmul (r : k) (m : M) :
    boundary M (algebraMap k (ExteriorAlgebra k L) r ⊗ₜ m) = 0 := by
  rw [boundary, lift.tmul, bdAux, CliffordAlgebra.foldr'_algebraMap, smul_zero]
  rfl

theorem boundary_one_tmul (m : M) : boundary M ((1 : ExteriorAlgebra k L) ⊗ₜ m) = 0 := by
  simpa using boundary_algebraMap_tmul (L := L) (1 : k) m

/-- Cartan's identity for chains: `d ε y + ε y d = - θ y`. -/
theorem boundary_wedgeLeft (y : L) (ξ : Chains k L M) :
    boundary M (wedgeLeft M y ξ) = -theta M y ξ - wedgeLeft M y (boundary M ξ) := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul x m =>
    rw [wedgeLeft_tmul, boundary, lift.tmul, bdAux, CliffordAlgebra.foldr'_ι_mul]
    rfl
  | add ξ η hξ hη => simp only [map_add, hξ, hη]; abel

omit [LieRingModule L M] [LieModule k L M] in
/-- Induction over chains: generated from `1 ⊗ m` by addition and `ε y`. -/
@[elab_as_elim]
theorem chains_induction {P : Chains k L M → Prop} (zero : P 0)
    (one : ∀ m : M, P ((1 : ExteriorAlgebra k L) ⊗ₜ m))
    (add : ∀ ξ η, P ξ → P η → P (ξ + η))
    (wedge : ∀ y ξ, P ξ → P (wedgeLeft M y ξ)) (ξ : Chains k L M) : P ξ := by
  induction ξ using TensorProduct.induction_on with
  | zero => exact zero
  | add ξ η hξ hη => exact add ξ η hξ hη
  | tmul x m =>
    induction x using CliffordAlgebra.left_induction generalizing m with
    | algebraMap r =>
      have : algebraMap k (ExteriorAlgebra k L) r ⊗ₜ[k] m = (1 : ExteriorAlgebra k L) ⊗ₜ (r • m) := by
        rw [Algebra.algebraMap_eq_smul_one, smul_tmul]
      rw [this]; exact one _
    | add x x' hx hx' => rw [add_tmul]; exact add _ _ (hx m) (hx' m)
    | ι_mul x y hx => exact wedge y _ (hx m)

/-- A derivation `D` of `L` with a compatible endomorphism `S` of `M`. -/
structure IsCompatibleDerivation (D : Module.End k L) (S : Module.End k M) : Prop where
  derivation : ∀ y z : L, D ⁅y, z⁆ = ⁅D y, z⁆ + ⁅y, D z⁆
  compatible : ∀ (y : L) (m : M), S ⁅y, m⁆ = ⁅D y, m⁆ + ⁅y, S m⁆

theorem lieDeriv_theta_commutator {D : Module.End k L} {S : Module.End k M}
    (h : IsCompatibleDerivation D S) (y : L) (ξ : Chains k L M) :
    lieDeriv D S (theta M y ξ) - theta M y (lieDeriv D S ξ) = theta M (D y) ξ := by
  rw [theta, theta, lieDeriv_commutator]
  have h1 : D * LieModule.toEnd k L L y - LieModule.toEnd k L L y * D =
      LieModule.toEnd k L L (D y) := by
    ext z
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LieModule.toEnd_apply_apply,
      h.derivation]
    abel
  have h2 : S * LieModule.toEnd k L M y - LieModule.toEnd k L M y * S =
      LieModule.toEnd k L M (D y) := by
    ext m
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LieModule.toEnd_apply_apply,
      h.compatible]
    abel
  rw [h1, h2]

/-- Lie derivatives by compatible derivations commute with the boundary. -/
theorem boundary_lieDeriv {D : Module.End k L} {S : Module.End k M}
    (h : IsCompatibleDerivation D S) (ξ : Chains k L M) :
    boundary M (lieDeriv D S ξ) = lieDeriv D S (boundary M ξ) := by
  induction ξ using chains_induction with
  | zero => simp
  | one m => simp [boundary_one_tmul]
  | add ξ η hξ hη => simp only [map_add, hξ, hη]
  | wedge y ξ hξ =>
    rw [lieDeriv_wedgeLeft, map_add, boundary_wedgeLeft, boundary_wedgeLeft,
      boundary_wedgeLeft, hξ, map_sub, map_neg, lieDeriv_wedgeLeft]
    have hc := lieDeriv_theta_commutator h y ξ
    rw [sub_eq_iff_eq_add] at hc
    rw [hc]
    abel

theorem isCompatibleDerivation_ad (y : L) :
    IsCompatibleDerivation (LieModule.toEnd k L L y) (LieModule.toEnd k L M y) where
  derivation z w := by
    simp only [LieModule.toEnd_apply_apply]
    rw [leibniz_lie]
  compatible z m := by
    simp only [LieModule.toEnd_apply_apply]
    rw [leibniz_lie]

theorem boundary_theta (y : L) (ξ : Chains k L M) :
    boundary M (theta M y ξ) = theta M y (boundary M ξ) :=
  boundary_lieDeriv (isCompatibleDerivation_ad y) ξ

/-- **The CE boundary squares to zero.** -/
theorem boundary_boundary (ξ : Chains k L M) : boundary M (boundary M ξ) = 0 := by
  induction ξ using chains_induction with
  | zero => simp
  | one m => simp [boundary_one_tmul]
  | add ξ η hξ hη => simp only [map_add, hξ, hη, add_zero]
  | wedge y ξ hξ =>
    rw [boundary_wedgeLeft, map_sub, map_neg, boundary_wedgeLeft, boundary_theta, hξ, map_zero]
    abel

end KhanSL2.LieChains
