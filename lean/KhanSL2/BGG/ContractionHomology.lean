module

public import TauCeti.Algebra.Homology.Contraction.Linear
public import TauCeti.Algebra.Homology.SquareZero

@[expose] public section
noncomputable section
namespace KhanSL2.BGG.Contraction

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  {dM : Module.End R M} {dN : Module.End R N}

/-- A proved contraction induces an equivalence on the actual kernel/image
quotients. Its forward map is induced by the projection and its inverse by the
inclusion. The retract's square-zero identity follows from the contraction. -/
def homologyEquiv (c : TauCeti.LinearSpecialContraction dM dN)
    (hdM : dM.comp dM = 0) :
    dM.homology hdM ≃ₗ[R] dN.homology (c.dN_comp_dN_eq_zero hdM) :=
  { LinearMap.homologyMap c.proj hdM (c.dN_comp_dN_eq_zero hdM) c.proj_comp_dM with
    invFun := LinearMap.homologyMap c.incl (c.dN_comp_dN_eq_zero hdM) hdM
      c.dM_comp_incl.symm
    left_inv := by
      intro q
      change LinearMap.homologyMap c.incl (c.dN_comp_dN_eq_zero hdM) hdM
        c.dM_comp_incl.symm (LinearMap.homologyMap c.proj hdM
          (c.dN_comp_dN_eq_zero hdM) c.proj_comp_dM q) = q
      obtain ⟨z, rfl⟩ := dM.homologyπ_surjective hdM q
      simp only [LinearMap.homologyπ_apply, LinearMap.homologyMap_mk]
      apply (Submodule.Quotient.eq _).mpr
      change c.incl (c.proj z) - (z : M) ∈ LinearMap.range dM
      refine ⟨-c.homotopy z, ?_⟩
      rw [map_neg, c.incl_proj_apply, LinearMap.mem_ker.mp z.2, map_zero, sub_zero]
      abel
    right_inv := by
      intro q
      change LinearMap.homologyMap c.proj hdM (c.dN_comp_dN_eq_zero hdM)
        c.proj_comp_dM (LinearMap.homologyMap c.incl
          (c.dN_comp_dN_eq_zero hdM) hdM c.dM_comp_incl.symm q) = q
      obtain ⟨z, rfl⟩ := dN.homologyπ_surjective (c.dN_comp_dN_eq_zero hdM) q
      simp only [LinearMap.homologyπ_apply, LinearMap.homologyMap_mk]
      congr 1
      exact Subtype.ext (c.proj_incl_apply z) }

@[simp] theorem homologyEquiv_apply (c : TauCeti.LinearSpecialContraction dM dN)
    (hdM : dM.comp dM = 0) (q : dM.homology hdM) :
    homologyEquiv c hdM q =
      LinearMap.homologyMap c.proj hdM (c.dN_comp_dN_eq_zero hdM) c.proj_comp_dM q := rfl

@[simp] theorem homologyEquiv_symm_apply (c : TauCeti.LinearSpecialContraction dM dN)
    (hdM : dM.comp dM = 0) (q : dN.homology (c.dN_comp_dN_eq_zero hdM)) :
    (homologyEquiv c hdM).symm q =
      LinearMap.homologyMap c.incl (c.dN_comp_dN_eq_zero hdM) hdM c.dM_comp_incl.symm q := rfl

/-- On a cycle, the homology equivalence takes its class to the class of its
projection. This specifies the equivalence independently of quotient choices. -/
@[simp] theorem homologyEquiv_mk (c : TauCeti.LinearSpecialContraction dM dN)
    (hdM : dM.comp dM = 0) (z : LinearMap.ker dM) :
    homologyEquiv c hdM (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨c.proj z,
        LinearMap.map_mem_ker_of_comp_eq c.proj c.proj_comp_dM z.2⟩ := by
  simp only [homologyEquiv_apply, LinearMap.homologyMap_mk]

/-- The inverse equivalence takes a retract cycle to the class of its inclusion. -/
@[simp] theorem homologyEquiv_symm_mk (c : TauCeti.LinearSpecialContraction dM dN)
    (hdM : dM.comp dM = 0) (z : LinearMap.ker dN) :
    (homologyEquiv c hdM).symm (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨c.incl z,
        LinearMap.map_mem_ker_of_comp_eq c.incl c.dM_comp_incl.symm z.2⟩ := by
  simp only [homologyEquiv_symm_apply, LinearMap.homologyMap_mk]

end KhanSL2.BGG.Contraction