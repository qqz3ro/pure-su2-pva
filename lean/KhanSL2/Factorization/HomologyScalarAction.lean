module

public import KhanSL2.Factorization.CoefficientTotalFunctor

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! An original coefficient action commuting with a square-zero differential
induces its genuine scalar action on the actual cycles modulo boundaries. -/
noncomputable section
namespace KhanSL2.Factorization
open BGG.Contraction
variable (R : Type) [CommRing R] [Algebra ℂ R]
variable {X : Type} [AddCommGroup X] [Module ℂ X]
variable (d : Module.End ℂ X) (hd : d.comp d = 0)
variable (ρ : R →ₐ[ℂ] Module.End ℂ X)
variable (hρ : ∀ r : R, (ρ r).comp d = d.comp (ρ r))

/-- The actual scalar endomorphism on homology, obtained by applying it to a cycle. -/
def homologyScalarMap (r : R) :
    Module.End ℂ (PerfectDuality.PairHomology d d hd) :=
  (totalPairMap (ρ r) (hρ r)).homologyMap hd hd

/-- The original scalar action on homology is an algebra representation. -/
def homologyScalarAction : R →ₐ[ℂ] Module.End ℂ (PerfectDuality.PairHomology d d hd) where
  toFun := homologyScalarMap R d hd ρ hρ
  map_zero' := by
    apply LinearMap.ext
    intro u
    obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (PerfectDuality.pairBoundaries d d) u
    change Submodule.Quotient.mk _ = 0
    have hz : (totalPairMap (ρ 0) (hρ 0)).cyclesMap z = 0 := by
      apply Subtype.ext
      exact LinearMap.congr_fun ρ.map_zero z.val
    rw [hz,Submodule.Quotient.mk_zero]
  map_one' := by
    apply LinearMap.ext
    intro u
    obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (PerfectDuality.pairBoundaries d d) u
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk z
    congr 1
    apply Subtype.ext
    exact LinearMap.congr_fun ρ.map_one z.val
  map_add' r s := by
    apply LinearMap.ext
    intro u
    obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (PerfectDuality.pairBoundaries d d) u
    change (Submodule.Quotient.mk _ : PerfectDuality.PairHomology d d hd) = Submodule.Quotient.mk _ + Submodule.Quotient.mk _
    rw [← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    exact LinearMap.congr_fun (ρ.map_add r s) z.val
  map_mul' r s := by
    apply LinearMap.ext
    intro u
    obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (PerfectDuality.pairBoundaries d d) u
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    exact LinearMap.congr_fun (ρ.map_mul r s) z.val
  commutes' c := by
    apply LinearMap.ext
    intro u
    obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (PerfectDuality.pairBoundaries d d) u
    conv_rhs => rw [Algebra.algebraMap_eq_smul_one]
    rw [LinearMap.smul_apply]
    change (Submodule.Quotient.mk _ : PerfectDuality.PairHomology d d hd) = c • Submodule.Quotient.mk z
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    exact LinearMap.congr_fun (ρ.commutes c) z.val

/-- The homology module uses precisely this original action on cycle representatives. -/
@[instance_reducible] def homologyScalarModule :
    Module R (PerfectDuality.PairHomology d d hd) :=
  Module.compHom _ (homologyScalarAction R d hd ρ hρ).toRingHom

end KhanSL2.Factorization
