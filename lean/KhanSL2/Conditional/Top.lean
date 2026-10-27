module

public import KhanSL2.Depth.SourceDepth
public import Mathlib.Algebra.Module.Projective

@[expose] public section

/-!
# The rank-one top term

A surjection from the kernel of a map out of a rank-one free module onto the
coefficient ring forces that map to vanish if its target is torsion-free.
The actual polynomial module `Depth.JB B B` is also free of rank one, including
at `B = 0`; its equivalence below uses the prescribed coefficient substitution.
-/

noncomputable section

namespace KhanSL2.Conditional

section RankOne

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Coordinates in a rank-one free module commute with scalar multiplication. -/
theorem rankOne_smul_comm (e : M ≃ₗ[R] R) (x y : M) :
    e x • y = e y • x := by
  apply e.injective
  simp only [map_smul, smul_eq_mul]
  exact mul_comm _ _

/-- A surjection from a submodule of a rank-one free module to the ring is injective. -/
theorem rankOne_submodule_surjective_injective (e : M ≃ₗ[R] R)
    (P : Submodule R M) (f : P →ₗ[R] R) (hf : Function.Surjective f) :
    Function.Injective f := by
  obtain ⟨v, hv⟩ := hf 1
  have hz : ∀ x : P, f x = 0 → x = 0 := by
    intro x hx
    have hs : e (x : M) • v = e (v : M) • x :=
      Subtype.ext (rankOne_smul_comm e (x : M) (v : M))
    have he : e (x : M) = 0 := by
      have hh := congrArg f hs
      simpa only [map_smul, smul_eq_mul, hv, hx, mul_one, mul_zero] using hh
    apply Subtype.ext
    exact e.injective (he.trans (map_zero e).symm)
  intro x y hxy
  exact sub_eq_zero.mp (hz (x - y) (by rw [map_sub, hxy, sub_self]))

/-- A surjection from a rank-one free module to the ring is injective. -/
theorem rankOne_surjective_injective (e : M ≃ₗ[R] R)
    (f : M →ₗ[R] R) (hf : Function.Surjective f) : Function.Injective f := by
  obtain ⟨v, hv⟩ := hf 1
  have hz : ∀ x : M, f x = 0 → x = 0 := by
    intro x hx
    have he : e x = 0 := by
      have hh := congrArg f (rankOne_smul_comm e x v)
      simpa only [map_smul, smul_eq_mul, hv, hx, mul_one, mul_zero] using hh
    exact e.injective (he.trans (map_zero e).symm)
  intro x y hxy
  exact sub_eq_zero.mp (hz (x - y) (by rw [map_sub, hxy, sub_self]))

/-- The top differential vanishes once its kernel surjects onto the ring. -/
theorem top_differential_eq_zero [IsDomain R] [Module.IsTorsionFree R N]
    (e : M ≃ₗ[R] R) (d : M →ₗ[R] N)
    (κ : LinearMap.ker d →ₗ[R] R) (hκ : Function.Surjective κ) : d = 0 := by
  obtain ⟨v, hv⟩ := hκ 1
  have hv0 : (v : M) ≠ 0 := by
    intro h
    have h' : v = 0 := Subtype.ext h
    have : (0 : R) = 1 := (map_zero κ).symm.trans (h' ▸ hv)
    exact zero_ne_one this
  have he : e (v : M) ≠ 0 := by
    intro h
    exact hv0 (e.injective (h.trans (map_zero e).symm))
  apply LinearMap.ext
  intro x
  change d x = 0
  apply (smul_eq_zero_iff_right he).mp
  calc
    e (v : M) • d x = d (e (v : M) • x) := (map_smul d _ _).symm
    _ = d (e x • (v : M)) := congrArg d (rankOne_smul_comm e (v : M) x)
    _ = 0 := by rw [map_smul, v.property, smul_zero]

/-- The surjection on top cycles is already an isomorphism on its underlying sets. -/
theorem top_kernel_map_injective (e : M ≃ₗ[R] R) (d : M →ₗ[R] N)
    (κ : LinearMap.ker d →ₗ[R] R) (hκ : Function.Surjective κ) :
    Function.Injective κ := rankOne_submodule_surjective_injective e _ κ hκ

/-- Projective modules supply the torsion-freeness required by the top argument. -/
theorem projective_isTorsionFree [Module.Projective R N] : Module.IsTorsionFree R N := by
  obtain ⟨i, hi⟩ := (inferInstance : Module.Projective R N).out
  exact hi.injective.moduleIsTorsionFree i (fun r x => i.map_smul r x)

end RankOne

open MvPolynomial

/-- With no triple roots, the weighted coefficient substitution is signed reversal. -/
theorem depthNuTop_X (B : ℕ) (j : Fin B) :
    Depth.nu B 0 (X j) =
      (-1) ^ (j.val + 1) * X (Sum.inl j.rev) := by
  rw [Depth.nu_X]
  have hw : Depth.genW B 0 = 1 := by
    simp [Depth.genW, Depth.monicOf]
  rw [Depth.genF, hw, one_pow, mul_one]
  change (-1 : Depth.Src B 0) ^ (j.val + 1) *
    (Depth.genA B 0).coeff (B - (j.val + 1)) = _
  rw [show B - (j.val + 1) = j.rev.val from rfl, Depth.genA, Depth.coeff_monicOf]

/-- Explicit inverse to the coefficient substitution in the top sector. -/
def depthNuTopInv (B : ℕ) : Depth.Src B 0 →ₐ[ℂ] Depth.RB B :=
  aeval fun v => match v with
    | Sum.inl k => (-1) ^ (B - k.val) * X k.rev
    | Sum.inr k => Fin.elim0 k

@[simp] theorem depthNuTopInv_nu (B : ℕ) :
    (depthNuTopInv B).comp (Depth.nu B 0) = AlgHom.id ℂ (Depth.RB B) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, depthNuTop_X, map_mul, map_pow, map_neg, map_one,
    depthNuTopInv, aeval_X, Fin.rev_rev, Fin.val_rev, AlgHom.id_apply]
  rw [show B - (B - (j.val + 1)) = j.val + 1 by omega]
  rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  rfl

@[simp] theorem depthNu_nuTopInv (B : ℕ) :
    (Depth.nu B 0).comp (depthNuTopInv B) = AlgHom.id ℂ (Depth.Src B 0) := by
  apply MvPolynomial.algHom_ext
  rintro (k | k)
  · simp only [AlgHom.comp_apply, depthNuTopInv, aeval_X, map_mul, map_pow, map_neg,
      map_one, depthNuTop_X, Fin.rev_rev, Fin.val_rev, AlgHom.id_apply]
    rw [depthNuTop_X B k.rev]
    simp only [Fin.rev_rev, Fin.val_rev]
    rw [show B - (k.val + 1) + 1 = B - k.val by omega]
    rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  · exact Fin.elim0 k

/-- The specialized action is definitionally the action already prescribed by `nu`. -/
local instance depthTopCoordAlgebra (B : ℕ) :
    Algebra (Depth.RB B) (Depth.CoordMod B 0) :=
  (Depth.nu B 0).toRingHom.toAlgebra

/-- The prescribed top coefficient map is bijective, with its actual scalar action. -/
def depthTopCoordEquiv (B : ℕ) : Depth.RB B ≃ₗ[Depth.RB B] Depth.CoordMod B 0 := by
  let f : Depth.RB B →ₗ[Depth.RB B] Depth.CoordMod B 0 :=
    { toFun := Depth.nu B 0
      map_add' := map_add _
      map_smul' := fun c a => by
        change Depth.nu B 0 (c * a) = Depth.nu B 0 c * Depth.nu B 0 a
        exact map_mul _ _ _ }
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    have hh := congrArg (depthNuTopInv B) h
    change depthNuTopInv B (Depth.nu B 0 x) = depthNuTopInv B (Depth.nu B 0 y) at hh
    exact (DFunLike.congr_fun (depthNuTopInv_nu B) x).symm.trans
      (hh.trans (DFunLike.congr_fun (depthNuTopInv_nu B) y))
  · intro y
    refine ⟨depthNuTopInv B y, ?_⟩
    exact DFunLike.congr_fun (depthNu_nuTopInv B) y

/-- The actual top polynomial module is free of rank one over `R_B`. -/
def depthJBTopEquiv (B : ℕ) : Depth.JB B B ≃ₗ[Depth.RB B] Depth.RB B := by
  have e1 : Depth.CoordMod B 0 ≃ₗ[Depth.RB B] Depth.J B B 0 := by
    simpa only [Nat.mul_zero, Nat.add_zero] using Depth.srcEquivJ B 0
  have e : Depth.J B B 0 ≃ₗ[Depth.RB B] Depth.RB B :=
    e1.symm.trans (depthTopCoordEquiv B).symm
  let es (s : ℕ) (hs : s = 0) : Depth.J B B s ≃ₗ[Depth.RB B] Depth.RB B := by
    subst s
    exact e
  have hJB : Depth.JB B B = Depth.J B B ((B - B) / 3) :=
    if_pos ⟨le_refl B, by simp⟩
  exact (LinearEquiv.ofEq _ _ hJB).trans (es _ (by omega))

end KhanSL2.Conditional
