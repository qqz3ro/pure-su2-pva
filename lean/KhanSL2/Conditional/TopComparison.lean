module

public import KhanSL2.Conditional.BGGComparison
public import KhanSL2.Conditional.Top

@[expose] public section

/-! # The unconditional comparison from top BGG cycles to the coefficient ring

The canonical BGG homology comparison and the proved surjectivity of the
polynomial comparison give this surjection before any rank-one claim is used.
-/

noncomputable section
namespace KhanSL2.Conditional
open scoped KhanSL2.Conditional
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

universe u
section Projection
variable {R : Type u} [CommRing R]
  (C : ℕ → Type u) [∀ p, AddCommGroup (C p)] [∀ p, Module R (C p)]
  (d : ∀ p, C (p+1) →ₗ[R] C p)

/-- The ordinary quotient map from cycles to homology. -/
def cycleQuotient (p : ℕ) : Depth.cycles C d p →ₗ[R] Depth.homology C d p :=
  ((LinearMap.range (d p)).comap (Depth.cycles C d p).subtype).mkQ

theorem cycleQuotient_surjective (p : ℕ) : Function.Surjective (cycleQuotient C d p) :=
  Submodule.mkQ_surjective _
end Projection

local instance topComparison_termAddCommGroup (B p : ℕ) : AddCommGroup (BGGComplex.Term B p) := inferInstance
local instance topComparison_termCoefficientModule (B : ℕ) (p : ℕ) :
    Module (CoefficientRing B) (BGGComplex.Term B p) := inferInstance
local instance topComparison_cyclesAddCommGroup (B : ℕ) (p : ℕ) :
    AddCommGroup (Depth.cycles (BGGComplex.Term B) (bggDifferential B) p) := inferInstance
local instance topComparison_cyclesCoefficientModule (B : ℕ) (p : ℕ) :
    Module (CoefficientRing B) (Depth.cycles (BGGComplex.Term B) (bggDifferential B) p) := inferInstance

section FixedBGG
variable (B : ℕ)

/-- The canonical cycle-to-homology-to-CE map on the fixed complex. -/
def cyclesToK (p : ℕ) :
    Depth.cycles (BGGComplex.Term B) (bggDifferential B) p →ₗ[CoefficientRing B] K B p :=
  (bggHomologyEquiv B p).toLinearMap.comp
    (cycleQuotient (BGGComplex.Term B) (bggDifferential B) p)

theorem cyclesToK_surjective (p : ℕ) : Function.Surjective (cyclesToK B p) :=
  (bggHomologyEquiv B p).surjective.comp
    (cycleQuotient_surjective (BGGComplex.Term B) (bggDifferential B) p)

/-- The specified comparison on top cycles, in the proved rank-one target coordinates. -/
def topCycleMap :
    Depth.cycles (BGGComplex.Term B) (bggDifferential B) B →ₗ[CoefficientRing B] CoefficientRing B :=
  (depthJBTopEquiv B).toLinearMap.comp ((psi B B).comp (cyclesToK B B))

theorem topCycleMap_surjective : Function.Surjective (topCycleMap B) :=
  (depthJBTopEquiv B).surjective.comp ((psi_surjective B B).comp (cyclesToK_surjective B B))

end FixedBGG

end KhanSL2.Conditional
