module

public import KhanSL2.Factorization.RelativeChainsDuality

@[expose] public section

/-! Actual maps of square-zero pairs and evaluation naturality of homology duality. -/

noncomputable section
namespace KhanSL2.Factorization.PerfectDuality

variable {X Y Z X' Y' Z' : Type*}
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup Z] [Module ℂ Z]
  [AddCommGroup X'] [Module ℂ X'] [AddCommGroup Y'] [Module ℂ Y']
  [AddCommGroup Z'] [Module ℂ Z']

/-- A map of two specified short complexes. -/
structure PairMap (f : X →ₗ[ℂ] Y) (g : Y →ₗ[ℂ] Z)
    (f' : X' →ₗ[ℂ] Y') (g' : Y' →ₗ[ℂ] Z') where
  left : X →ₗ[ℂ] X'
  middle : Y →ₗ[ℂ] Y'
  right : Z →ₗ[ℂ] Z'
  comm_in : middle.comp f = f'.comp left
  comm_out : right.comp g = g'.comp middle

namespace PairMap

variable {f : X →ₗ[ℂ] Y} {g : Y →ₗ[ℂ] Z}
  {f' : X' →ₗ[ℂ] Y'} {g' : Y' →ₗ[ℂ] Z'}
  (u : PairMap f g f' g')

/-- A specified short-complex map preserves the actual cycle subspaces. -/
def cyclesMap : LinearMap.ker g →ₗ[ℂ] LinearMap.ker g' :=
  u.middle.restrict (fun y hy => by
    change g' (u.middle y) = 0
    have he := LinearMap.congr_fun u.comm_out y
    change u.right (g y) = g' (u.middle y) at he
    rw [show g y = 0 from hy, map_zero] at he
    exact he.symm)

@[simp] theorem cyclesMap_val (z : LinearMap.ker g) :
    (u.cyclesMap z).val = u.middle z.val := rfl

/-- The induced map on the actual cycles/boundaries quotients. -/
def homologyMap (h : g.comp f = 0) (h' : g'.comp f' = 0) :
    PairHomology f g h →ₗ[ℂ] PairHomology f' g' h' :=
  (pairBoundaries f g).mapQ (pairBoundaries f' g') u.cyclesMap (by
    intro z hz
    change z.val ∈ LinearMap.range f at hz
    obtain ⟨x,hx⟩ := hz
    change u.middle z.val ∈ LinearMap.range f'
    refine ⟨u.left x, ?_⟩
    rw [← hx]
    exact (LinearMap.congr_fun u.comm_in x).symm)

@[simp] theorem homologyMap_mk (h : g.comp f = 0) (h' : g'.comp f' = 0)
    (z : LinearMap.ker g) :
    u.homologyMap h h' (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (u.cyclesMap z) := rfl

/-- Transposition reverses the actual short-complex map. -/
def dual : PairMap g'.dualMap f'.dualMap g.dualMap f.dualMap where
  left := u.right.dualMap
  middle := u.middle.dualMap
  right := u.left.dualMap
  comm_in := by
    apply LinearMap.ext
    intro ψ
    apply LinearMap.ext
    intro y
    change ψ (g' (u.middle y)) = ψ (u.right (g y))
    exact congrArg ψ (LinearMap.congr_fun u.comm_out y).symm
  comm_out := by
    apply LinearMap.ext
    intro ℓ
    apply LinearMap.ext
    intro x
    change ℓ (f' (u.left x)) = ℓ (u.middle (f x))
    exact congrArg ℓ (LinearMap.congr_fun u.comm_in x).symm

/-- Homology duality intertwines the specified transposed maps by ordinary evaluation. -/
theorem homologyDual_natural (h : g.comp f = 0) (h' : g'.comp f' = 0) :
    (dualHomologyMap f g h).comp
      (u.dual.homologyMap (dualPair_square f' g' h') (dualPair_square f g h)) =
        (u.homologyMap h h').dualMap.comp (dualHomologyMap f' g' h') := by
  apply LinearMap.ext
  intro a
  obtain ⟨ℓ,rfl⟩ := Submodule.mkQ_surjective (pairBoundaries g'.dualMap f'.dualMap) a
  apply LinearMap.ext
  intro b
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (pairBoundaries f g) b
  rfl

end PairMap
end KhanSL2.Factorization.PerfectDuality
