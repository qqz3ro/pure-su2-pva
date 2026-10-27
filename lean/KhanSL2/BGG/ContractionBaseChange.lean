module

public import TauCeti.Algebra.Homology.Contraction.Linear
public import Mathlib.LinearAlgebra.TensorProduct.Tower

@[expose] public section
noncomputable section
namespace KhanSL2.BGG

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {dM : Module.End R M} {dN : Module.End R N}

/-- Extend a special contraction to an arbitrary (possibly noncommutative)
coefficient algebra. All maps are linear over that coefficient algebra. -/
def contractionBaseChange (A : Type*) [Ring A] [Algebra R A]
    (c : TauCeti.LinearSpecialContraction dM dN) :
    TauCeti.LinearSpecialContraction (dM.baseChange A) (dN.baseChange A) where
  incl := c.incl.baseChange A
  proj := c.proj.baseChange A
  homotopy := c.homotopy.baseChange A
  dM_comp_incl := by
    simpa only [LinearMap.baseChange_comp] using
      congrArg (LinearMap.baseChange A) c.dM_comp_incl
  proj_comp_dM := by
    simpa only [LinearMap.baseChange_comp] using
      congrArg (LinearMap.baseChange A) c.proj_comp_dM
  proj_comp_incl := by
    simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_id] using
      congrArg (LinearMap.baseChange A) c.proj_comp_incl
  dM_comp_homotopy_add_homotopy_comp_dM := by
    simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_add,
      LinearMap.baseChange_sub, LinearMap.baseChange_id] using
      congrArg (LinearMap.baseChange A) c.dM_comp_homotopy_add_homotopy_comp_dM
  homotopy_comp_incl := by
    simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_zero] using
      congrArg (LinearMap.baseChange A) c.homotopy_comp_incl
  proj_comp_homotopy := by
    simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_zero] using
      congrArg (LinearMap.baseChange A) c.proj_comp_homotopy
  homotopy_comp_homotopy := by
    simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_zero] using
      congrArg (LinearMap.baseChange A) c.homotopy_comp_homotopy

end KhanSL2.BGG