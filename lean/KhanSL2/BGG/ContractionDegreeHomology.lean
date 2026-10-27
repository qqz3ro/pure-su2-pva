module

public import KhanSL2.BGG.ContractionHomology

@[expose] public section
noncomputable section
namespace KhanSL2.BGG.Contraction

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  {dM : Module.End R M} {dN : Module.End R N}

/-- The two subspaces needed for cohomology in one degree: current cochains and
cochains in the preceding degree. At degree zero, the latter may be `⊥`. -/
structure DegreeWindow (d : Module.End R M) where
  current : Submodule R M
  previous : Submodule R M
  differential_mem : ∀ x ∈ previous, d x ∈ current

namespace DegreeWindow

/-- Cycles in the chosen cohomological degree. -/
def cycles (W : DegreeWindow dM) : Submodule R M := W.current ⊓ LinearMap.ker dM

/-- Boundaries from the preceding degree, viewed inside cycles. Square-zero and
`differential_mem` ensure all images from the preceding degree are cycles. -/
def boundaries (W : DegreeWindow dM) : Submodule R W.cycles :=
  (W.previous.map dM).comap W.cycles.subtype

/-- The actual degreewise quotient of cycles by boundaries. -/
abbrev homology (W : DegreeWindow dM) (_hd : dM.comp dM = 0) : Type _ :=
  W.cycles ⧸ W.boundaries

@[simp] theorem mem_boundaries (W : DegreeWindow dM) (z : W.cycles) :
    z ∈ W.boundaries ↔ ∃ w ∈ W.previous, dM w = (z : M) := Iff.rfl

/-- Every differential of a preceding-degree cochain belongs to the cycles. -/
theorem differential_mem_cycles (W : DegreeWindow dM) (hd : dM.comp dM = 0)
    {w : M} (hw : w ∈ W.previous) : dM w ∈ W.cycles := by
  exact ⟨W.differential_mem w hw, LinearMap.congr_fun hd w⟩

/-- Restriction of a degree-preserving chain map to the cycles. -/
def cyclesMap (W : DegreeWindow dM) (V : DegreeWindow dN) (f : M →ₗ[R] N)
    (hf : f.comp dM = dN.comp f)
    (hc : ∀ x ∈ W.current, f x ∈ V.current) : W.cycles →ₗ[R] V.cycles :=
  f.restrict fun x hx => ⟨hc x hx.1,
    LinearMap.map_mem_ker_of_comp_eq f hf hx.2⟩

/-- The induced map on degreewise quotient cohomology. -/
def homologyMap (W : DegreeWindow dM) (V : DegreeWindow dN) (f : M →ₗ[R] N)
    (hdM : dM.comp dM = 0) (hdN : dN.comp dN = 0)
    (hf : f.comp dM = dN.comp f)
    (hc : ∀ x ∈ W.current, f x ∈ V.current)
    (hp : ∀ x ∈ W.previous, f x ∈ V.previous) :
    W.homology hdM →ₗ[R] V.homology hdN :=
  W.boundaries.mapQ V.boundaries (W.cyclesMap V f hf hc) <| by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := (W.mem_boundaries z).mp hz
    apply (V.mem_boundaries _).mpr
    refine ⟨f w, hp w hw, ?_⟩
    change dN (f w) = f z
    rw [← LinearMap.comp_apply, ← hf, LinearMap.comp_apply, hwz]

@[simp] theorem homologyMap_mk (W : DegreeWindow dM) (V : DegreeWindow dN)
    (f : M →ₗ[R] N) (hdM : dM.comp dM = 0) (hdN : dN.comp dN = 0)
    (hf : f.comp dM = dN.comp f)
    (hc : ∀ x ∈ W.current, f x ∈ V.current)
    (hp : ∀ x ∈ W.previous, f x ∈ V.previous) (z : W.cycles) :
    W.homologyMap V f hdM hdN hf hc hp (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (W.cyclesMap V f hf hc z) := rfl

end DegreeWindow

/-- Degreewise quotient cohomology is preserved by a contraction whose inclusion
and projection preserve the two chosen degrees and whose homotopy lowers the
current degree to the preceding one. No finite-support assumption on cochains
or completed direct-sum identification is needed. -/
def degreeHomologyEquiv (c : TauCeti.LinearSpecialContraction dM dN)
    (hdM : dM.comp dM = 0) (W : DegreeWindow dM) (V : DegreeWindow dN)
    (hi : ∀ x ∈ V.current, c.incl x ∈ W.current)
    (hp : ∀ x ∈ W.current, c.proj x ∈ V.current)
    (hiPrev : ∀ x ∈ V.previous, c.incl x ∈ W.previous)
    (hpPrev : ∀ x ∈ W.previous, c.proj x ∈ V.previous)
    (hh : ∀ x ∈ W.current, c.homotopy x ∈ W.previous) :
    W.homology hdM ≃ₗ[R] V.homology (c.dN_comp_dN_eq_zero hdM) :=
  { W.homologyMap V c.proj hdM (c.dN_comp_dN_eq_zero hdM) c.proj_comp_dM hp hpPrev with
    invFun := V.homologyMap W c.incl (c.dN_comp_dN_eq_zero hdM) hdM
      c.dM_comp_incl.symm hi hiPrev
    left_inv := by
      intro q
      change V.homologyMap W c.incl (c.dN_comp_dN_eq_zero hdM) hdM
        c.dM_comp_incl.symm hi hiPrev (W.homologyMap V c.proj hdM
          (c.dN_comp_dN_eq_zero hdM) c.proj_comp_dM hp hpPrev q) = q
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective W.boundaries q
      simp only [Submodule.mkQ_apply, DegreeWindow.homologyMap_mk]
      apply (Submodule.Quotient.eq _).mpr
      change c.incl (c.proj z) - (z : M) ∈ W.previous.map dM
      refine ⟨-c.homotopy z, W.previous.neg_mem (hh z z.2.1), ?_⟩
      rw [map_neg, c.incl_proj_apply, LinearMap.mem_ker.mp z.2.2, map_zero, sub_zero]
      abel
    right_inv := by
      intro q
      change W.homologyMap V c.proj hdM (c.dN_comp_dN_eq_zero hdM)
        c.proj_comp_dM hp hpPrev (V.homologyMap W c.incl
          (c.dN_comp_dN_eq_zero hdM) hdM c.dM_comp_incl.symm hi hiPrev q) = q
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective V.boundaries q
      simp only [Submodule.mkQ_apply, DegreeWindow.homologyMap_mk]
      congr 1
      exact Subtype.ext (c.proj_incl_apply z) }

@[simp] theorem degreeHomologyEquiv_apply
    (c : TauCeti.LinearSpecialContraction dM dN) (hdM : dM.comp dM = 0)
    (W : DegreeWindow dM) (V : DegreeWindow dN) hi hp hiPrev hpPrev hh
    (q : W.homology hdM) :
    degreeHomologyEquiv c hdM W V hi hp hiPrev hpPrev hh q =
      W.homologyMap V c.proj hdM (c.dN_comp_dN_eq_zero hdM) c.proj_comp_dM hp hpPrev q := rfl

@[simp] theorem degreeHomologyEquiv_symm_apply
    (c : TauCeti.LinearSpecialContraction dM dN) (hdM : dM.comp dM = 0)
    (W : DegreeWindow dM) (V : DegreeWindow dN) hi hp hiPrev hpPrev hh
    (q : V.homology (c.dN_comp_dN_eq_zero hdM)) :
    (degreeHomologyEquiv c hdM W V hi hp hiPrev hpPrev hh).symm q =
      V.homologyMap W c.incl (c.dN_comp_dN_eq_zero hdM) hdM c.dM_comp_incl.symm hi hiPrev q := rfl

end KhanSL2.BGG.Contraction