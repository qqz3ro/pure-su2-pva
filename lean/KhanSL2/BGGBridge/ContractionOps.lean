module

public import TauCeti.Algebra.Homology.Contraction.Linear
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

/-!
# Operations on special contractions

* A special contraction descends to quotients by subspaces that all of its maps preserve.
* A special contraction can be pulled back along a linear equivalence of complexes.
-/

noncomputable section

namespace KhanSL2.BGGBridge

variable {R M H : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
  {dM : Module.End R M} {dH : Module.End R H}

/-- A special contraction descends to quotients by subcomplexes preserved by all its maps. -/
def quotContraction (c : TauCeti.LinearSpecialContraction dM dH) (P : Submodule R M)
    (Q : Submodule R H) (hdM : P ≤ P.comap dM) (hdH : Q ≤ Q.comap dH)
    (hi : Q ≤ P.comap c.incl) (hp : P ≤ Q.comap c.proj) (hh : P ≤ P.comap c.homotopy) :
    TauCeti.LinearSpecialContraction (P.mapQ P dM hdM) (Q.mapQ Q dH hdH) where
  incl := Q.mapQ P c.incl hi
  proj := P.mapQ Q c.proj hp
  homotopy := P.mapQ P c.homotopy hh
  dM_comp_incl := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun c.dM_comp_incl x
    simp only [LinearMap.comp_apply] at h
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, h]
  proj_comp_dM := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun c.proj_comp_dM x
    simp only [LinearMap.comp_apply] at h
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, h]
  proj_comp_incl := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun c.proj_comp_incl x
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, h,
      LinearMap.id_apply]
  dM_comp_homotopy_add_homotopy_comp_dM := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun c.dM_comp_homotopy_add_homotopy_comp_dM x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply] at h
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.id_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
    rw [← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_sub, h]
  homotopy_comp_incl := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun c.homotopy_comp_incl x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, h,
      LinearMap.zero_apply, Submodule.Quotient.mk_zero]
  proj_comp_homotopy := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun c.proj_comp_homotopy x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, h,
      LinearMap.zero_apply, Submodule.Quotient.mk_zero]
  homotopy_comp_homotopy := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun c.homotopy_comp_homotopy x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, h,
      LinearMap.zero_apply, Submodule.Quotient.mk_zero]

/-- Pull a special contraction back along an isomorphism of complexes. -/
def equivContraction {M' : Type*} [AddCommGroup M'] [Module R M'] {dM' : Module.End R M'}
    (e : M' ≃ₗ[R] M) (he : ∀ x, dM (e x) = e (dM' x))
    (c : TauCeti.LinearSpecialContraction dM dH) :
    TauCeti.LinearSpecialContraction dM' dH where
  incl := e.symm.toLinearMap ∘ₗ c.incl
  proj := c.proj ∘ₗ e.toLinearMap
  homotopy := e.symm.toLinearMap ∘ₗ c.homotopy ∘ₗ e.toLinearMap
  dM_comp_incl := by
    have hs : ∀ y, dM' (e.symm y) = e.symm (dM y) := by
      intro y
      apply e.injective
      rw [← he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun c.dM_comp_incl x
    simp only [LinearMap.comp_apply] at h
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hs, h]
  proj_comp_dM := by
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun c.proj_comp_dM (e x)
    simp only [LinearMap.comp_apply] at h
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ← he, h]
  proj_comp_incl := by
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun c.proj_comp_incl x
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, h,
      LinearMap.id_apply]
  dM_comp_homotopy_add_homotopy_comp_dM := by
    have hs : ∀ y, dM' (e.symm y) = e.symm (dM y) := by
      intro y
      apply e.injective
      rw [← he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun c.dM_comp_homotopy_add_homotopy_comp_dM (e x)
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply] at h
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, LinearEquiv.coe_coe, hs, ← he]
    rw [← map_add, h, map_sub, LinearEquiv.symm_apply_apply]
  homotopy_comp_incl := by
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun c.homotopy_comp_incl x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, h,
      map_zero, LinearMap.zero_apply]
  proj_comp_homotopy := by
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun c.proj_comp_homotopy (e x)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, h,
      LinearMap.zero_apply]
  homotopy_comp_homotopy := by
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun c.homotopy_comp_homotopy (e x)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, h,
      map_zero, LinearMap.zero_apply]

end KhanSL2.BGGBridge
