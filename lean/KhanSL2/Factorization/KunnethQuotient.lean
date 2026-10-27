module

public import KhanSL2.Factorization.RelativeChainsDualityMap

@[expose] public section

/-! Generic quotient map for total cycles, kept abstract in the differential
so concrete CE expressions are not unfolded during construction. -/
noncomputable section
namespace KhanSL2.Factorization

variable {A : Type*} [AddCommGroup A] [Module ℂ A]

/-- The literal class of an actual cycle modulo the actual image of d. -/
def squareZeroClass (d : Module.End ℂ A) : LinearMap.ker d →ₗ[ℂ]
    LinearMap.ker d ⧸ PerfectDuality.pairBoundaries d d :=
  (PerfectDuality.pairBoundaries d d).mkQ

@[simp] theorem squareZeroClass_apply (d : Module.End ℂ A) (u : LinearMap.ker d) :
    squareZeroClass d u = Submodule.Quotient.mk u := rfl

end KhanSL2.Factorization
