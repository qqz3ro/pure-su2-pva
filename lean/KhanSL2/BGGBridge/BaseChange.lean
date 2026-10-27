module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.Algebra.Homology.Contraction.Linear

@[expose] public section

/-!
# Base change of free-module maps along a right action

Let `U` be a `ℂ`-algebra and `N` a right `U`-module, given as an algebra map
`ρ : U → (End N)ᵐᵒᵖ`. A `U`-linear map `f : U ⊗ A → U ⊗ A'` between free left `U`-modules
induces `base ρ f : A ⊗ N → A' ⊗ N`. This is `N ⊗_U f` under `N ⊗_U (U ⊗ A) ≅ A ⊗ N`. The
construction needs no tensor product over the noncommutative ring `U`:
`base ρ f (a ⊗ n) = ev (f (1 ⊗ a) ⊗ n)`, where `ev ((u ⊗ a) ⊗ n) = a ⊗ n·u`.

`base` is additive and functorial, so it carries special contractions to special contractions.
It also transports three kinds of compatibility:
* commuting with derivation-type operators, such as a Lie algebra action;
* commuting with multiplicative operators, such as dilations;
* preserving degree submodules.
-/

noncomputable section

open scoped TensorProduct
open MulOpposite

namespace KhanSL2.BGGBridge

variable {U : Type*} [Ring U] [Algebra ℂ U]
variable {N : Type*} [AddCommGroup N] [Module ℂ N]
variable (ρ : U →ₐ[ℂ] (Module.End ℂ N)ᵐᵒᵖ)

/-- The right action of `u` on `N`. -/
def ract (u : U) : Module.End ℂ N := unop (ρ u)

@[simp] theorem ract_one : ract ρ 1 = 1 := by
  simp [ract]

theorem ract_mul_apply (u v : U) (n : N) : ract ρ (u * v) n = ract ρ v (ract ρ u n) := by
  simp [ract]

theorem ract_add (u v : U) : ract ρ (u + v) = ract ρ u + ract ρ v := by
  simp [ract]

theorem ract_smul (c : ℂ) (u : U) : ract ρ (c • u) = c • ract ρ u := by
  simp [ract]

theorem ract_zero : ract ρ (0 : U) = 0 := by
  simp [ract]

/-- `u ↦ ract ρ u` as a linear map. -/
def ractL : U →ₗ[ℂ] Module.End ℂ N where
  toFun := ract ρ
  map_add' := ract_add ρ
  map_smul' := ract_smul ρ

@[simp] theorem ractL_apply (u : U) : ractL ρ u = ract ρ u := rfl

section Ev

variable (A : Type*) [AddCommGroup A] [Module ℂ A]

/-- Evaluation `(u ⊗ a) ⊗ n ↦ a ⊗ n·u`. -/
def ev : ((U ⊗[ℂ] A) ⊗[ℂ] N) →ₗ[ℂ] A ⊗[ℂ] N :=
  TensorProduct.lift (TensorProduct.lift
    ((LinearMap.llcomp ℂ N N (A ⊗[ℂ] N) ∘ₗ TensorProduct.mk ℂ A N).flip ∘ₗ ractL ρ))

@[simp] theorem ev_tmul_tmul (u : U) (a : A) (n : N) :
    ev ρ A ((u ⊗ₜ[ℂ] a) ⊗ₜ[ℂ] n) = a ⊗ₜ[ℂ] ract ρ u n := rfl

/-- The defining property of the tensor product over `U`. -/
theorem ev_smul (u : U) (t : U ⊗[ℂ] A) (n : N) :
    ev ρ A ((u • t) ⊗ₜ[ℂ] n) = ev ρ A (t ⊗ₜ[ℂ] ract ρ u n) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul v a =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, ev_tmul_tmul, ev_tmul_tmul, ract_mul_apply]
  | add s t hs ht =>
    rw [smul_add, TensorProduct.add_tmul, map_add, hs, ht, TensorProduct.add_tmul, map_add]

theorem tmul_eq_smul_one (u : U) (a : A) : u ⊗ₜ[ℂ] a = u • ((1 : U) ⊗ₜ[ℂ] a) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end Ev

section Base

variable {A A' A'' : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
  [AddCommGroup A''] [Module ℂ A'']

/-- Base change of a `U`-linear map of free modules along the right action `ρ`. -/
def base (f : U ⊗[ℂ] A →ₗ[U] U ⊗[ℂ] A') : A ⊗[ℂ] N →ₗ[ℂ] A' ⊗[ℂ] N :=
  ev ρ A' ∘ₗ LinearMap.rTensor N ((f.restrictScalars ℂ) ∘ₗ TensorProduct.mk ℂ U A 1)

theorem base_tmul (f : U ⊗[ℂ] A →ₗ[U] U ⊗[ℂ] A') (a : A) (n : N) :
    base ρ f (a ⊗ₜ[ℂ] n) = ev ρ A' (f ((1 : U) ⊗ₜ[ℂ] a) ⊗ₜ[ℂ] n) := rfl

/-- Naturality of evaluation. -/
theorem ev_map (f : U ⊗[ℂ] A →ₗ[U] U ⊗[ℂ] A') (t : U ⊗[ℂ] A) (n : N) :
    ev ρ A' (f t ⊗ₜ[ℂ] n) = base ρ f (ev ρ A (t ⊗ₜ[ℂ] n)) := by
  induction t using TensorProduct.induction_on generalizing n with
  | zero => simp
  | tmul u a =>
    rw [tmul_eq_smul_one A u a, map_smul, ev_smul, ev_smul, ev_tmul_tmul, ract_one,
      Module.End.one_apply, base_tmul]
  | add s t hs ht =>
    rw [map_add, TensorProduct.add_tmul, map_add, hs, ht, TensorProduct.add_tmul, map_add,
      map_add]

theorem base_comp (f : U ⊗[ℂ] A →ₗ[U] U ⊗[ℂ] A') (g : U ⊗[ℂ] A' →ₗ[U] U ⊗[ℂ] A'') :
    base ρ (g ∘ₗ f) = base ρ g ∘ₗ base ρ f := by
  apply TensorProduct.ext'
  intro a n
  rw [LinearMap.comp_apply, base_tmul, base_tmul, LinearMap.comp_apply, ev_map]

theorem base_id : base ρ (LinearMap.id : U ⊗[ℂ] A →ₗ[U] U ⊗[ℂ] A) = LinearMap.id := by
  apply TensorProduct.ext'
  intro a n
  rw [base_tmul, LinearMap.id_apply, ev_tmul_tmul, ract_one, Module.End.one_apply,
    LinearMap.id_apply]

theorem base_add (f g : U ⊗[ℂ] A →ₗ[U] U ⊗[ℂ] A') :
    base ρ (f + g) = base ρ f + base ρ g := by
  apply TensorProduct.ext'
  intro a n
  rw [base_tmul, LinearMap.add_apply, TensorProduct.add_tmul, map_add, LinearMap.add_apply,
    base_tmul, base_tmul]

theorem base_zero : base ρ (0 : U ⊗[ℂ] A →ₗ[U] U ⊗[ℂ] A') = 0 := by
  apply TensorProduct.ext'
  intro a n
  rw [base_tmul, LinearMap.zero_apply, TensorProduct.zero_tmul, map_zero, LinearMap.zero_apply]

theorem base_sub (f g : U ⊗[ℂ] A →ₗ[U] U ⊗[ℂ] A') :
    base ρ (f - g) = base ρ f - base ρ g := by
  have h : f - g + g = f := sub_add_cancel f g
  rw [eq_sub_iff_add_eq, ← base_add, h]

end Base

/-! ## Contractions -/

section Contraction

variable {A A' : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']

/-- Base change of a special contraction is a special contraction. -/
def baseContraction {dM : Module.End U (U ⊗[ℂ] A)} {dH : Module.End U (U ⊗[ℂ] A')}
    (c : TauCeti.LinearSpecialContraction dM dH) :
    TauCeti.LinearSpecialContraction (base ρ dM) (base ρ dH) where
  incl := base ρ c.incl
  proj := base ρ c.proj
  homotopy := base ρ c.homotopy
  dM_comp_incl := by rw [← base_comp, ← base_comp, c.dM_comp_incl]
  proj_comp_dM := by rw [← base_comp, ← base_comp, c.proj_comp_dM]
  proj_comp_incl := by rw [← base_comp, c.proj_comp_incl, base_id]
  dM_comp_homotopy_add_homotopy_comp_dM := by
    rw [← base_comp, ← base_comp, ← base_add, c.dM_comp_homotopy_add_homotopy_comp_dM,
      base_sub, base_id, base_comp]
  homotopy_comp_incl := by rw [← base_comp, c.homotopy_comp_incl, base_zero]
  proj_comp_homotopy := by rw [← base_comp, c.proj_comp_homotopy, base_zero]
  homotopy_comp_homotopy := by rw [← base_comp, c.homotopy_comp_homotopy, base_zero]

@[simp] theorem baseContraction_incl {dM : Module.End U (U ⊗[ℂ] A)}
    {dH : Module.End U (U ⊗[ℂ] A')} (c : TauCeti.LinearSpecialContraction dM dH) :
    (baseContraction ρ c).incl = base ρ c.incl := rfl

@[simp] theorem baseContraction_proj {dM : Module.End U (U ⊗[ℂ] A)}
    {dH : Module.End U (U ⊗[ℂ] A')} (c : TauCeti.LinearSpecialContraction dM dH) :
    (baseContraction ρ c).proj = base ρ c.proj := rfl

@[simp] theorem baseContraction_homotopy {dM : Module.End U (U ⊗[ℂ] A)}
    {dH : Module.End U (U ⊗[ℂ] A')} (c : TauCeti.LinearSpecialContraction dM dH) :
    (baseContraction ρ c).homotopy = base ρ c.homotopy := rfl

end Contraction

/-! ## Transport of operators -/

section Operators

variable {A A' : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']

/-- The diagonal operator `X ⊗ 1 + 1 ⊗ Y` of derivation type. -/
def diag {P Q : Type*} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q]
    (X : Module.End ℂ P) (Y : Module.End ℂ Q) : Module.End ℂ (P ⊗[ℂ] Q) :=
  LinearMap.rTensor Q X + LinearMap.lTensor P Y

@[simp] theorem diag_tmul {P Q : Type*} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q]
    [Module ℂ Q] (X : Module.End ℂ P) (Y : Module.End ℂ Q) (p : P) (q : Q) :
    diag X Y (p ⊗ₜ[ℂ] q) = X p ⊗ₜ[ℂ] q + p ⊗ₜ[ℂ] Y q := rfl

variable {XU : Module.End ℂ U} {XN : Module.End ℂ N}

theorem ev_diag (hcompat : ∀ u n, XN (ract ρ u n) - ract ρ u (XN n) = ract ρ (XU u) n)
    (XA : Module.End ℂ A) (t : U ⊗[ℂ] A) (n : N) :
    ev ρ A (diag XU XA t ⊗ₜ[ℂ] n) + ev ρ A (t ⊗ₜ[ℂ] XN n) = diag XA XN (ev ρ A (t ⊗ₜ[ℂ] n)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul u a =>
    rw [diag_tmul, TensorProduct.add_tmul, map_add, ev_tmul_tmul, ev_tmul_tmul, ev_tmul_tmul,
      ev_tmul_tmul, diag_tmul, ← hcompat, TensorProduct.tmul_sub]
    abel
  | add s t hs ht =>
    simp only [map_add, TensorProduct.add_tmul]
    rw [← hs, ← ht]
    abel

/-- Base change carries commuting with derivation-type operators to commuting with the
diagonal operators. -/
theorem base_diag (hXU : XU 1 = 0)
    (hcompat : ∀ u n, XN (ract ρ u n) - ract ρ u (XN n) = ract ρ (XU u) n)
    {XA : Module.End ℂ A} {XA' : Module.End ℂ A'} (f : U ⊗[ℂ] A →ₗ[U] U ⊗[ℂ] A')
    (hf : ∀ t, f (diag XU XA t) = diag XU XA' (f t)) (x : A ⊗[ℂ] N) :
    base ρ f (diag XA XN x) = diag XA' XN (base ρ f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a n =>
    have h1 : ((1 : U) ⊗ₜ[ℂ] XA a) = diag XU XA ((1 : U) ⊗ₜ[ℂ] a) := by
      rw [diag_tmul, hXU, TensorProduct.zero_tmul, zero_add]
    rw [diag_tmul, map_add, base_tmul, base_tmul, base_tmul, h1, hf, ev_diag ρ hcompat]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {DU : Module.End ℂ U} {DN : Module.End ℂ N}

theorem ev_map_map (hcompat : ∀ u n, DN (ract ρ u n) = ract ρ (DU u) (DN n))
    (DA : Module.End ℂ A) (t : U ⊗[ℂ] A) (n : N) :
    ev ρ A (TensorProduct.map DU DA t ⊗ₜ[ℂ] DN n) = TensorProduct.map DA DN (ev ρ A (t ⊗ₜ[ℂ] n)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul u a =>
    rw [TensorProduct.map_tmul, ev_tmul_tmul, ev_tmul_tmul, TensorProduct.map_tmul, hcompat]
  | add s t hs ht => simp only [map_add, TensorProduct.add_tmul, hs, ht]

/-- Base change carries commuting with multiplicative operators (dilations) to commuting with
their tensor products. -/
theorem base_map_map (hDU : DU 1 = 1) (hcompat : ∀ u n, DN (ract ρ u n) = ract ρ (DU u) (DN n))
    {DA : Module.End ℂ A} {DA' : Module.End ℂ A'} (f : U ⊗[ℂ] A →ₗ[U] U ⊗[ℂ] A')
    (hf : ∀ t, f (TensorProduct.map DU DA t) = TensorProduct.map DU DA' (f t))
    (x : A ⊗[ℂ] N) :
    base ρ f (TensorProduct.map DA DN x) = TensorProduct.map DA' DN (base ρ f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a n =>
    have h1 : ((1 : U) ⊗ₜ[ℂ] DA a) = TensorProduct.map DU DA ((1 : U) ⊗ₜ[ℂ] a) := by
      rw [TensorProduct.map_tmul, hDU]
    rw [TensorProduct.map_tmul, base_tmul, base_tmul, h1, hf, ev_map_map ρ hcompat]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Base change commutes with operators acting on the coefficients alone, as long as they
commute with the right action. -/
theorem base_lTensor (hcompat : ∀ u n, XN (ract ρ u n) = ract ρ u (XN n))
    (f : U ⊗[ℂ] A →ₗ[U] U ⊗[ℂ] A') (x : A ⊗[ℂ] N) :
    base ρ f (LinearMap.lTensor A XN x) = LinearMap.lTensor A' XN (base ρ f x) := by
  have key : ∀ (t : U ⊗[ℂ] A') (n : N),
      ev ρ A' (t ⊗ₜ[ℂ] XN n) = LinearMap.lTensor A' XN (ev ρ A' (t ⊗ₜ[ℂ] n)) := by
    intro t n
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul u a => rw [ev_tmul_tmul, ev_tmul_tmul, LinearMap.lTensor_tmul, hcompat]
    | add s t hs ht => simp only [map_add, TensorProduct.add_tmul, hs, ht]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a n => rw [LinearMap.lTensor_tmul, base_tmul, base_tmul, key]
  | add x y hx hy => simp only [map_add, hx, hy]

end Operators

/-! ## Degrees -/

section Degree

variable {A A' : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']

/-- `P ⊗ N` inside `A ⊗ N`. -/
def tensorLeft (P : Submodule ℂ A) : Submodule ℂ (A ⊗[ℂ] N) :=
  LinearMap.range (LinearMap.rTensor N P.subtype)

theorem tmul_mem_tensorLeft {P : Submodule ℂ A} {a : A} (ha : a ∈ P) (n : N) :
    a ⊗ₜ[ℂ] n ∈ tensorLeft (N := N) P :=
  ⟨⟨a, ha⟩ ⊗ₜ[ℂ] n, rfl⟩

theorem ev_mem_tensorLeft (P : Submodule ℂ A) {t : U ⊗[ℂ] A} (ht : t ∈ P.baseChange U)
    (n : N) : ev ρ A (t ⊗ₜ[ℂ] n) ∈ tensorLeft P := by
  revert n
  rw [Submodule.baseChange_eq_span] at ht
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨a, ha, rfl⟩ := ht
    intro n
    rw [TensorProduct.mk_apply, ev_tmul_tmul, ract_one, Module.End.one_apply]
    exact tmul_mem_tensorLeft ha n
  | zero => intro n; simp
  | add s t _ _ hs ht =>
    intro n
    rw [TensorProduct.add_tmul, map_add]
    exact Submodule.add_mem _ (hs n) (ht n)
  | smul u t _ ht =>
    intro n
    rw [ev_smul]
    exact ht _

/-- Base change carries degree-preserving maps of free modules to degree-preserving maps. -/
theorem base_mem_tensorLeft {P : Submodule ℂ A} {P' : Submodule ℂ A'}
    (f : U ⊗[ℂ] A →ₗ[U] U ⊗[ℂ] A')
    (hf : ∀ a ∈ P, f ((1 : U) ⊗ₜ[ℂ] a) ∈ P'.baseChange U)
    {x : A ⊗[ℂ] N} (hx : x ∈ tensorLeft P) : base ρ f x ∈ tensorLeft P' := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a n =>
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, base_tmul]
    exact ev_mem_tensorLeft ρ P' (hf a a.property) n
  | add y z hy hz =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hy hz

end Degree

end KhanSL2.BGGBridge
