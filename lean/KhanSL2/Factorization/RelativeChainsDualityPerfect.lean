module

public import KhanSL2.Factorization.RelativeChainsDualityMap

@[expose] public section

/-! A specified perfect pairing of short complexes induces the canonical homology
duality, with an evaluation formula and naturality for transposed maps. -/

noncomputable section
namespace KhanSL2.Factorization.PerfectDuality

variable {X Y Z X' Y' Z' : Type*}
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup Z] [Module ℂ Z]
  [AddCommGroup X'] [Module ℂ X'] [AddCommGroup Y'] [Module ℂ Y']
  [AddCommGroup Z'] [Module ℂ Z']

/-- Three specified linear equivalences intertwining the two differentials. -/
structure PairEquiv (f : X →ₗ[ℂ] Y) (g : Y →ₗ[ℂ] Z)
    (f' : X' →ₗ[ℂ] Y') (g' : Y' →ₗ[ℂ] Z') where
  left : X ≃ₗ[ℂ] X'
  middle : Y ≃ₗ[ℂ] Y'
  right : Z ≃ₗ[ℂ] Z'
  comm_in : middle.toLinearMap.comp f = f'.comp left.toLinearMap
  comm_out : right.toLinearMap.comp g = g'.comp middle.toLinearMap

namespace PairEquiv

variable {f : X →ₗ[ℂ] Y} {g : Y →ₗ[ℂ] Z}
  {f' : X' →ₗ[ℂ] Y'} {g' : Y' →ₗ[ℂ] Z'} (e : PairEquiv f g f' g')

def toPairMap : PairMap f g f' g' where
  left := e.left.toLinearMap
  middle := e.middle.toLinearMap
  right := e.right.toLinearMap
  comm_in := e.comm_in
  comm_out := e.comm_out

/-- The inverse equivalences intertwine the actual differentials as well. -/
def symm : PairEquiv f' g' f g where
  left := e.left.symm
  middle := e.middle.symm
  right := e.right.symm
  comm_in := by
    apply LinearMap.ext
    intro x
    apply e.middle.injective
    change e.middle (e.middle.symm (f' x)) = e.middle (f (e.left.symm x))
    rw [e.middle.apply_symm_apply]
    have he := LinearMap.congr_fun e.comm_in (e.left.symm x)
    change e.middle (f (e.left.symm x)) = f' (e.left (e.left.symm x)) at he
    rw [e.left.apply_symm_apply] at he
    exact he.symm
  comm_out := by
    apply LinearMap.ext
    intro y
    apply e.right.injective
    change e.right (e.right.symm (g' y)) = e.right (g (e.middle.symm y))
    rw [e.right.apply_symm_apply]
    have he := LinearMap.congr_fun e.comm_out (e.middle.symm y)
    change e.right (g (e.middle.symm y)) = g' (e.middle (e.middle.symm y)) at he
    rw [e.middle.apply_symm_apply] at he
    exact he.symm

/-- An actual isomorphism of short complexes induces its actual quotient equivalence. -/
def homologyEquiv (h : g.comp f = 0) (h' : g'.comp f' = 0) :
    PairHomology f g h ≃ₗ[ℂ] PairHomology f' g' h' :=
  { e.toPairMap.homologyMap h h' with
    invFun := e.symm.toPairMap.homologyMap h' h
    left_inv := by
      intro z
      obtain ⟨v,rfl⟩ := Submodule.mkQ_surjective (pairBoundaries f g) z
      change e.symm.toPairMap.homologyMap h' h
        (e.toPairMap.homologyMap h h' (Submodule.Quotient.mk v)) =
          Submodule.Quotient.mk v
      rw [PairMap.homologyMap_mk, PairMap.homologyMap_mk]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact e.middle.symm_apply_apply v.val
    right_inv := by
      intro z
      obtain ⟨v,rfl⟩ := Submodule.mkQ_surjective (pairBoundaries f' g') z
      change e.toPairMap.homologyMap h h'
        (e.symm.toPairMap.homologyMap h' h (Submodule.Quotient.mk v)) =
          Submodule.Quotient.mk v
      rw [PairMap.homologyMap_mk, PairMap.homologyMap_mk]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact e.middle.apply_symm_apply v.val }

@[simp] theorem homologyEquiv_mk (h : g.comp f = 0) (h' : g'.comp f' = 0)
    (z : LinearMap.ker g) :
    e.homologyEquiv h h' (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (e.toPairMap.cyclesMap z) := rfl

end PairEquiv

section Paired

variable {Aminus A₀ Aplus : Type*}
  [AddCommGroup Aminus] [Module ℂ Aminus] [AddCommGroup A₀] [Module ℂ A₀]
  [AddCommGroup Aplus] [Module ℂ Aplus]
  {α : Aminus →ₗ[ℂ] A₀} {β : A₀ →ₗ[ℂ] Aplus}
  (f : X →ₗ[ℂ] Y) (g : Y →ₗ[ℂ] Z)

/-- A perfect evaluation pairing with transposed differentials identifies actual
cohomology with the dual of actual chain homology. -/
def pairedHomologyEquiv (e : PairEquiv α β g.dualMap f.dualMap)
    (hA : β.comp α = 0) (hC : g.comp f = 0) :
    PairHomology α β hA ≃ₗ[ℂ] Module.Dual ℂ (PairHomology f g hC) :=
  (e.homologyEquiv hA (dualPair_square f g hC)).trans (homologyDualEquiv f g hC)

/-- The resulting duality is the specified pairing on represented cycles. -/
@[simp] theorem pairedHomologyEquiv_mk
    (e : PairEquiv α β g.dualMap f.dualMap)
    (hA : β.comp α = 0) (hC : g.comp f = 0)
    (a : LinearMap.ker β) (z : LinearMap.ker g) :
    pairedHomologyEquiv f g e hA hC (Submodule.Quotient.mk a)
      (Submodule.Quotient.mk z) = e.middle a.val z.val := rfl

variable {Aminus' A₀' Aplus' : Type*}
  [AddCommGroup Aminus'] [Module ℂ Aminus'] [AddCommGroup A₀'] [Module ℂ A₀']
  [AddCommGroup Aplus'] [Module ℂ Aplus']
  {α' : Aminus' →ₗ[ℂ] A₀'} {β' : A₀' →ₗ[ℂ] Aplus'}
  {f' : X' →ₗ[ℂ] Y'} {g' : Y' →ₗ[ℂ] Z'}

/-- The perfect-pairing duality is natural for the specified mutually transposed maps. -/
theorem pairedHomologyEquiv_natural
    (e : PairEquiv α β g.dualMap f.dualMap)
    (e' : PairEquiv α' β' g'.dualMap f'.dualMap)
    (uA : PairMap α' β' α β) (uC : PairMap f g f' g')
    (hA : β.comp α = 0) (hC : g.comp f = 0)
    (hA' : β'.comp α' = 0) (hC' : g'.comp f' = 0)
    (ht : ∀ a y, e.middle (uA.middle a) y = e'.middle a (uC.middle y)) :
    (pairedHomologyEquiv f g e hA hC).toLinearMap.comp (uA.homologyMap hA' hA) =
      (uC.homologyMap hC hC').dualMap.comp
        (pairedHomologyEquiv f' g' e' hA' hC').toLinearMap := by
  apply LinearMap.ext
  intro a
  obtain ⟨a,rfl⟩ := Submodule.mkQ_surjective (pairBoundaries α' β') a
  apply LinearMap.ext
  intro z
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (pairBoundaries f g) z
  exact ht a.val z.val

end Paired
end KhanSL2.Factorization.PerfectDuality
