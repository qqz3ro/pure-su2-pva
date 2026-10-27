module

public import KhanSL2.BGG.Current
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.Algebra.Lie.Basic
public import TauCeti.Algebra.Lie.Sl2.CompleteReducibility

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KhanSL2.BGG

variable {M N : Type*} [AddCommGroup M] [Module ℂ M]
  [LieRingModule G M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule G N]

/-- Projection along complementary Lie submodules commutes with the Lie action. -/
theorem lieSubmodule_projection_lie (P Q : LieSubmodule ℂ G M) (h : IsCompl P Q)
    (x : G) (m : M) :
    P.toSubmodule.projection Q.toSubmodule (LieSubmodule.isCompl_toSubmodule.mpr h) ⁅x,m⁆ =
      ⁅x, P.toSubmodule.projection Q.toSubmodule (LieSubmodule.isCompl_toSubmodule.mpr h) m⁆ := by
  let h' := LieSubmodule.isCompl_toSubmodule.mpr h
  let π := P.toSubmodule.projection Q.toSubmodule h'
  have hp : π m ∈ P := Submodule.projection_apply_mem h' m
  have hq : m - π m ∈ Q := Submodule.sub_projection_mem h' m
  have he : m = π m + (m - π m) := by abel
  change π ⁅x,m⁆ = ⁅x,π m⁆
  calc
    π ⁅x,m⁆ = π (⁅x,π m⁆ + ⁅x,m - π m⁆) := congrArg π (by rw [← lie_add, ← he])
    _ = ⁅x,π m⁆ := by
      rw [map_add, Submodule.projection_apply_of_mem_left h' (P.lie_mem hp),
        Submodule.projection_apply_of_mem_right h' (Q.lie_mem hq), add_zero]

/-- The actual projection onto a Lie summand, bundled as a Lie-module morphism. -/
def lieSubmoduleProjection (P Q : LieSubmodule ℂ G M) (h : IsCompl P Q) : M →ₗ⁅ℂ,G⁆ P where
  toLinearMap := P.toSubmodule.projectionOnto Q.toSubmodule (LieSubmodule.isCompl_toSubmodule.mpr h)
  map_lie' := by
    intro x m
    apply Subtype.ext
    exact lieSubmodule_projection_lie P Q h x m

@[simp] theorem lieSubmoduleProjection_apply_left (P Q : LieSubmodule ℂ G M)
    (h : IsCompl P Q) (m : P) : lieSubmoduleProjection P Q h m = m :=
  Submodule.projectionOnto_apply_left _ m

variable [LieModule ℂ G M] [LieModule ℂ G N]

/-- Every map of finite-dimensional complex sl₂-modules has an equivariant
linear generalized inverse. This is proved from complete reducibility. -/
theorem exists_lie_generalizedInverse [FiniteDimensional ℂ M] [FiniteDimensional ℂ N]
    (f : M →ₗ⁅ℂ,G⁆ N) : ∃ s : N →ₗ⁅ℂ,G⁆ M, ∀ x, f (s (f x)) = f x := by
  obtain ⟨Q,hQ⟩ := TauCeti.exists_isCompl_sl_fin_two f.ker
  obtain ⟨T,hT⟩ := TauCeti.exists_isCompl_sl_fin_two f.range
  let g : Q →ₗ⁅ℂ,G⁆ f.range :=
    (f.comp Q.incl).codRestrict f.range (fun q => ⟨q,rfl⟩)
  have hQ' : IsCompl f.ker.toSubmodule Q.toSubmodule :=
    LieSubmodule.isCompl_toSubmodule.mpr hQ
  have hg : Function.Bijective g := by
    constructor
    · intro q r hqr
      apply Subtype.ext
      apply sub_eq_zero.mp
      apply Submodule.disjoint_def.mp hQ'.disjoint (q.val - r.val)
      · change f (q.val - r.val) = 0
        rw [map_sub, sub_eq_zero]
        exact congrArg Subtype.val hqr
      · exact Q.sub_mem q.property r.property
    · intro y
      obtain ⟨m,hm⟩ := y.property
      let q := lieSubmoduleProjection Q f.ker hQ.symm m
      refine ⟨q, ?_⟩
      apply Subtype.ext
      have hz := Submodule.sub_projection_mem hQ'.symm m
      change f (m - (q : M)) = 0 at hz
      rw [map_sub, sub_eq_zero] at hz
      exact hz.symm.trans hm
  let e := TauCeti.LieModuleEquiv.ofBijective g hg
  let s := Q.incl.comp (e.symm.toLieModuleHom.comp (lieSubmoduleProjection f.range T hT))
  refine ⟨s, fun x => ?_⟩
  let y : f.range := ⟨f x, x, rfl⟩
  have he := congrArg Subtype.val
    ((TauCeti.LieModuleEquiv.ofBijective_apply g hg (e.symm y)).symm.trans
      (e.apply_symm_apply y))
  change f (e.symm y : M) = f x at he
  change f (e.symm (lieSubmoduleProjection f.range T hT (f x)) : M) = f x
  rw [show lieSubmoduleProjection f.range T hT (f x) = y from
    lieSubmoduleProjection_apply_left f.range T hT y]
  exact he

end KhanSL2.BGG