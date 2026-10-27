module

public import KhanSL2.BGG.Induced
public import Mathlib.LinearAlgebra.TensorProduct.Map

@[expose] public section

/-! Functoriality in an algebra endomorphism that fixes the inducing subalgebra. -/

noncomputable section
open scoped TensorProduct

namespace KhanSL2.BGG.Induced

variable {R A G M : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/-- Tensoring an algebra endomorphism with the identity is semilinear over that endomorphism. -/
def baseTensorMap (f : A →ₐ[R] A) :
    A ⊗[R] M →ₛₗ[f.toRingHom] A ⊗[R] M where
  toFun := TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[R] M)
  map_add' := (TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[R] M)).map_add
  map_smul' a t := by
    refine TensorProduct.inductionOn t ?_ ?_
    · intro b m
      rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
        TensorProduct.smul_tmul']
      change f (a * b) ⊗ₜ[R] m = (f a * f b) ⊗ₜ[R] m
      rw [map_mul]
    · intro x y hx hy
      simp only [smul_add, map_add, hx, hy]

@[simp] theorem baseTensorMap_tmul (f : A →ₐ[R] A) (a : A) (m : M) :
    baseTensorMap f (a ⊗ₜ[R] m) = f a ⊗ₜ[R] m := rfl

theorem baseTensorMap_relation (inc : G → A) (act : G → M →ₗ[R] M)
    (f : A →ₐ[R] A) (hfix : ∀ x, f (inc x) = inc x) (x : G) (m : M) :
    baseTensorMap f (relation inc act x m) = relation inc act x m := by
  rw [relation, map_sub, baseTensorMap_tmul, baseTensorMap_tmul, hfix, map_one]

theorem relations_le_comap_baseTensorMap (inc : G → A) (act : G → M →ₗ[R] M)
    (f : A →ₐ[R] A) (hfix : ∀ x, f (inc x) = inc x) :
    relations inc act ≤ (relations inc act).comap (baseTensorMap f) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨x, m⟩, rfl⟩
  change baseTensorMap f (relation inc act x m) ∈ relations inc act
  rw [baseTensorMap_relation inc act f hfix]
  exact relation_mem inc act x m

/-- The balancing quotient inherits the semilinear algebra endomorphism. -/
def baseMapSemi (inc : G → A) (act : G → M →ₗ[R] M)
    (f : A →ₐ[R] A) (hfix : ∀ x, f (inc x) = inc x) :
    Model inc act →ₛₗ[f.toRingHom] Model inc act :=
  (relations inc act).mapQ (relations inc act) (baseTensorMap f)
    (relations_le_comap_baseTensorMap inc act f hfix)

/-- The induced endomorphism is linear over the original scalar ring. -/
def baseMap (inc : G → A) (act : G → M →ₗ[R] M)
    (f : A →ₐ[R] A) (hfix : ∀ x, f (inc x) = inc x) :
    Model inc act →ₗ[R] Model inc act where
  toFun := baseMapSemi inc act f hfix
  map_add' := (baseMapSemi inc act f hfix).map_add
  map_smul' r q := by
    rw [← algebraMap_smul A r q, map_smulₛₗ]
    change f (algebraMap R A r) • baseMapSemi inc act f hfix q = _
    rw [f.commutes, algebraMap_smul]
    rfl

@[simp] theorem baseMap_mk_tmul (inc : G → A) (act : G → M →ₗ[R] M)
    (f : A →ₐ[R] A) (hfix : ∀ x, f (inc x) = inc x) (a : A) (m : M) :
    baseMap inc act f hfix (mk inc act (a ⊗ₜ[R] m)) =
      mk inc act (f a ⊗ₜ[R] m) := rfl

@[simp] theorem baseMap_of (inc : G → A) (act : G → M →ₗ[R] M)
    (f : A →ₐ[R] A) (hfix : ∀ x, f (inc x) = inc x) (m : M) :
    baseMap inc act f hfix (of inc act m) = of inc act m := by
  rw [of_apply, baseMap_mk_tmul, map_one]

theorem baseMap_smul (inc : G → A) (act : G → M →ₗ[R] M)
    (f : A →ₐ[R] A) (hfix : ∀ x, f (inc x) = inc x) (a : A) (q : Model inc act) :
    baseMap inc act f hfix (a • q) = f a • baseMap inc act f hfix q :=
  (baseMapSemi inc act f hfix).map_smulₛₗ a q

end KhanSL2.BGG.Induced
