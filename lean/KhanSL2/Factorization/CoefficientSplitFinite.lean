module

public import KhanSL2.Factorization.CoefficientSplitExact
public import KhanSL2.BGG.FiniteSl2Splitting

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KhanSL2.Factorization
open BGG

variable {N M P : Type}
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup P] [Module ℂ P] [LieRingModule Current P] [LieModule ℂ Current P]
  [FiniteDimensional ℂ N] [FiniteDimensional ℂ M] [FiniteDimensional ℂ P]

/-- Every finite-dimensional current-module short exact sequence splits for the
constant sl₂ action. Its positive-current action is not required to split. -/
theorem nonempty_constantSplitExact (i : N →ₗ⁅ℂ,Current⁆ M) (p : M →ₗ⁅ℂ,Current⁆ P)
    (hi : Function.Injective i) (he : Function.Exact i p) (hp : Function.Surjective p) :
    Nonempty (ConstantSplitExact i p) := by
  let : LieRingModule G N := LieRingModule.compLieHom N constant
  let : LieModule ℂ G N := LieModule.compLieHom N constant
  let : LieRingModule G M := LieRingModule.compLieHom M constant
  let : LieModule ℂ G M := LieModule.compLieHom M constant
  let : LieRingModule G P := LieRingModule.compLieHom P constant
  let : LieModule ℂ G P := LieModule.compLieHom P constant
  let iG : N →ₗ⁅ℂ,G⁆ M := ⟨i.toLinearMap, fun {x n} => i.map_lie (constant x) n⟩
  let pG : M →ₗ⁅ℂ,G⁆ P := ⟨p.toLinearMap, fun {x m} => p.map_lie (constant x) m⟩
  obtain ⟨r₀,hr₀⟩ := BGG.exists_lie_generalizedInverse iG
  obtain ⟨s,hs⟩ := BGG.exists_lie_generalizedInverse pG
  have hri (n : N) : r₀ (i n) = n := hi (hr₀ n)
  have hps (z : P) : p (s z) = z := by
    obtain ⟨m,rfl⟩ := hp z
    exact hs m
  have hpi : p.toLinearMap.comp i.toLinearMap = 0 :=
    (show Function.Exact i.toLinearMap p.toLinearMap from he).linearMap_comp_eq_zero
  let r : M →ₗ⁅ℂ,G⁆ N := r₀.comp (LieModuleHom.id - s.comp pG)
  refine ⟨{
    retraction := r.toLinearMap
    sectionMap := s.toLinearMap
    retraction_constant := fun x m => r.map_lie x m
    section_constant := fun x z => s.map_lie x z
    zero_comp := hpi
    left_inverse := ?_
    right_inverse := ?_
    decomposition := ?_ }⟩
  · apply LinearMap.ext
    intro n
    change r₀ (i n - s (p (i n))) = n
    have hz : p (i n) = 0 := LinearMap.congr_fun hpi n
    rw [hz,map_zero,sub_zero,hri]
  · apply LinearMap.ext
    exact hps
  · apply LinearMap.ext
    intro m
    change i (r₀ (m-s (p m))) + s (p m) = m
    have hz : p (m-s (p m)) = 0 := by rw [map_sub,hps,sub_self]
    obtain ⟨n,hn⟩ := he (m-s (p m)) |>.mp hz
    rw [← hn,hri,hn,sub_add_cancel]

end KhanSL2.Factorization


