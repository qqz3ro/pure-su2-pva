module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Algebra.Basic

@[expose] public section

/-!
# Induced modules by generators and balancing relations

The scalar tensor product `A ⊗[R] M` is a left `A`-module even when `A` is
noncommutative. Quotienting by `inc x ⊗ m - 1 ⊗ act x m` imposes the balancing
relations. The universal equivalence below proves the induced-module property.
For Lie induction, `A` is the universal enveloping algebra of the larger Lie
algebra and `inc` includes the smaller Lie algebra into `A`.
-/

noncomputable section

open scoped TensorProduct

namespace KhanSL2.BGG.Induced

variable {R A G M : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M]

def relation (inc : G → A) (act : G → M →ₗ[R] M) (x : G) (m : M) :
    A ⊗[R] M :=
  inc x ⊗ₜ[R] m - (1 : A) ⊗ₜ[R] act x m

def relations (inc : G → A) (act : G → M →ₗ[R] M) :
    Submodule A (A ⊗[R] M) :=
  Submodule.span A (Set.range fun xm : G × M => relation inc act xm.1 xm.2)

abbrev Model (inc : G → A) (act : G → M →ₗ[R] M) :=
  (A ⊗[R] M) ⧸ relations inc act

def mk (inc : G → A) (act : G → M →ₗ[R] M) :
    A ⊗[R] M →ₗ[A] Model inc act :=
  (relations inc act).mkQ

def of (inc : G → A) (act : G → M →ₗ[R] M) : M →ₗ[R] Model inc act :=
  ((mk inc act).restrictScalars R).comp (TensorProduct.mk R A M 1)

@[simp] theorem of_apply (inc : G → A) (act : G → M →ₗ[R] M) (m : M) :
    of inc act m = mk inc act ((1 : A) ⊗ₜ[R] m) := rfl

theorem mk_surjective (inc : G → A) (act : G → M →ₗ[R] M) :
    Function.Surjective (mk inc act) :=
  (relations inc act).mkQ_surjective

theorem relation_mem (inc : G → A) (act : G → M →ₗ[R] M) (x : G) (m : M) :
    relation inc act x m ∈ relations inc act :=
  Submodule.subset_span ⟨(x, m), rfl⟩

theorem mk_relation (inc : G → A) (act : G → M →ₗ[R] M) (x : G) (m : M) :
    mk inc act (relation inc act x m) = 0 :=
  (Submodule.Quotient.mk_eq_zero (relations inc act)).mpr (relation_mem inc act x m)

theorem mk_tmul (inc : G → A) (act : G → M →ₗ[R] M) (a : A) (m : M) :
    mk inc act (a ⊗ₜ[R] m) = a • of inc act m := by
  rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul]
  rfl

theorem inc_smul_of (inc : G → A) (act : G → M →ₗ[R] M) (x : G) (m : M) :
    inc x • of inc act m = of inc act (act x m) := by
  have h := mk_relation inc act x m
  rw [relation, map_sub, mk_tmul, ← of_apply] at h
  exact sub_eq_zero.mp h

/-- Every element is a finite sum of `A`-multiples of coefficient generators. -/
@[elab_as_elim] theorem induction_on
    (inc : G → A) (act : G → M →ₗ[R] M) {P : Model inc act → Prop}
    (q : Model inc act)
    (htmul : ∀ (a : A) (m : M), P (a • of inc act m))
    (hadd : ∀ x y, P x → P y → P (x + y)) : P q := by
  obtain ⟨t, rfl⟩ := mk_surjective inc act q
  refine TensorProduct.inductionOn t ?_ ?_
  · intro a m
    rw [mk_tmul]
    exact htmul a m
  · intro x y hx hy
    rw [map_add]
    exact hadd _ _ hx hy

section UniversalProperty

variable {N : Type*} [AddCommGroup N] [Module R N] [Module A N]
  [IsScalarTower R A N]

def tensorLiftLinear (f : M →ₗ[R] N) : A ⊗[R] M →ₗ[R] N :=
  TensorProduct.lift {
    toFun := fun a => {
      toFun := fun m => a • f m
      map_add' := by intro x y; simp only [map_add, smul_add]
      map_smul' := by intro r m; simp only [map_smul]; exact smul_comm a r (f m) }
    map_add' := by intro a b; ext m; exact add_smul a b (f m)
    map_smul' := by intro r a; ext m; exact smul_assoc r a (f m) }

@[simp] theorem tensorLiftLinear_tmul (f : M →ₗ[R] N) (a : A) (m : M) :
    tensorLiftLinear f (a ⊗ₜ[R] m) = a • f m := rfl

def tensorLift (f : M →ₗ[R] N) : A ⊗[R] M →ₗ[A] N where
  toFun := tensorLiftLinear f
  map_add' := (tensorLiftLinear f).map_add
  map_smul' a t := by
    refine TensorProduct.inductionOn t ?_ ?_
    · intro b m
      rw [TensorProduct.smul_tmul', tensorLiftLinear_tmul, tensorLiftLinear_tmul]
      exact mul_smul a b (f m)
    · intro x y hx hy
      simp only [smul_add, map_add, hx, hy]

@[simp] theorem tensorLift_tmul (f : M →ₗ[R] N) (a : A) (m : M) :
    tensorLift f (a ⊗ₜ[R] m) = a • f m := rfl

theorem relations_le_ker (inc : G → A) (act : G → M →ₗ[R] M)
    (f : M →ₗ[R] N) (hf : ∀ x m, f (act x m) = inc x • f m) :
    relations inc act ≤ LinearMap.ker (tensorLift f) := by
  apply Submodule.span_le.mpr
  rintro t ⟨⟨x, m⟩, rfl⟩
  change tensorLift f (relation inc act x m) = 0
  rw [relation, map_sub, tensorLift_tmul, tensorLift_tmul, one_smul, hf, sub_self]

/-- The induced `A`-linear map with the prescribed coefficient values. -/
def lift (inc : G → A) (act : G → M →ₗ[R] M)
    (f : M →ₗ[R] N) (hf : ∀ x m, f (act x m) = inc x • f m) :
    Model inc act →ₗ[A] N :=
  (relations inc act).liftQ (tensorLift f) (relations_le_ker inc act f hf)

@[simp] theorem lift_mk (inc : G → A) (act : G → M →ₗ[R] M)
    (f : M →ₗ[R] N) (hf : ∀ x m, f (act x m) = inc x • f m)
    (t : A ⊗[R] M) : lift inc act f hf (mk inc act t) = tensorLift f t := rfl

@[simp] theorem lift_of (inc : G → A) (act : G → M →ₗ[R] M)
    (f : M →ₗ[R] N) (hf : ∀ x m, f (act x m) = inc x • f m) (m : M) :
    lift inc act f hf (of inc act m) = f m := by
  rw [of_apply, lift_mk, tensorLift_tmul, one_smul]

omit [Module R N] [IsScalarTower R A N] in
@[ext] theorem hom_ext (inc : G → A) (act : G → M →ₗ[R] M)
    {f g : Model inc act →ₗ[A] N}
    (h : ∀ m, f (of inc act m) = g (of inc act m)) : f = g := by
  apply LinearMap.ext
  intro q
  refine induction_on inc act q ?_ ?_
  · intro a m
    rw [map_smul, map_smul, h]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]

theorem lift_unique (inc : G → A) (act : G → M →ₗ[R] M)
    (f : M →ₗ[R] N) (hf : ∀ x m, f (act x m) = inc x • f m)
    (g : Model inc act →ₗ[A] N) (hg : ∀ m, g (of inc act m) = f m) :
    g = lift inc act f hf := by
  apply hom_ext inc act
  intro m
  rw [hg, lift_of]

/-- The defining universal property of induction. -/
def universalEquiv (inc : G → A) (act : G → M →ₗ[R] M) :
    (Model inc act →ₗ[A] N) ≃
      {f : M →ₗ[R] N // ∀ x m, f (act x m) = inc x • f m} where
  toFun F := ⟨(F.restrictScalars R).comp (of inc act), by
    intro x m
    change F (of inc act (act x m)) = inc x • F (of inc act m)
    rw [← inc_smul_of, map_smul]⟩
  invFun f := lift inc act f.val f.property
  left_inv F := by
    apply hom_ext inc act
    intro m
    rw [lift_of]
    rfl
  right_inv f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro m
    exact lift_of inc act f.val f.property m

end UniversalProperty

end KhanSL2.BGG.Induced
