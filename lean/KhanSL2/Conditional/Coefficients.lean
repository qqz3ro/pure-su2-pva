module

public import KhanSL2.Modules.CoefficientLinearity
public import KhanSL2.Modules.DepthModuleComparison
public import KhanSL2.Depth.SourceDescent

@[expose] public section

/-! The actual coefficient homology and comparison in elementary symmetric coordinates. -/

noncomputable section
namespace KhanSL2.Conditional

abbrev CoefficientRing (B : ℕ) := Depth.RB B
abbrev K (B p : ℕ) := Modules.KTotal B p
abbrev J (B p : ℕ) := ↥(Depth.JB B p)

/-- Restrict the proved coefficient action through the explicit coordinate isomorphism. -/
scoped instance kCoefficientModule (B p : ℕ) : Module (CoefficientRing B) (K B p) :=
  Module.compHom (K B p) (Modules.elementaryAlgEquiv B).toRingHom

open scoped KhanSL2.Conditional

/-- Exactly the specified comparison, with the depth presentation of its target. -/
def psi (B p : ℕ) : K B p →ₗ[CoefficientRing B] J B p where
  toFun x := (Modules.depthJBEquiv B p).symm (Modules.psiB B p x)
  map_add' x y := by simp only [map_add]
  map_smul' a x := by
    apply (Modules.depthJBEquiv B p).injective
    simp only [LinearEquiv.apply_symm_apply, map_smulₛₗ]
    exact Modules.psiB_smul B p (Modules.elementaryAlgEquiv B a) x

@[simp] theorem psi_apply (B p : ℕ) (x : K B p) :
    psi B p x = (Modules.depthJBEquiv B p).symm (Modules.psiB B p x) := rfl

/-- Coordinate changes add no surjectivity assumption. -/
theorem psi_surjective (B p : ℕ) : Function.Surjective (psi B p) :=
  (Modules.depthJBEquiv B p).symm.surjective.comp (Modules.psiB_surjective B p)

/-- The conditional proof still concerns the original specified polynomial map. -/
theorem psi_injective_iff (B p : ℕ) :
    Function.Injective (psi B p) ↔ Function.Injective (Modules.psiB B p) := by
  constructor
  · intro h x y hxy
    exact h (congrArg (Modules.depthJBEquiv B p).symm hxy)
  · intro h x y hxy
    exact h ((Modules.depthJBEquiv B p).symm.injective hxy)

/-- The induction hypothesis used in the deformation and collision-support steps. -/
def EarlierComparisons (B : ℕ) : Prop :=
  ∀ b : ℕ, b < B → ∀ p : ℕ, Function.Injective (psi b p)

/-- The precise output required from the deformation/staircase proof. -/
def LowDegreeStep : Prop :=
  ∀ B : ℕ, 0 < B → EarlierComparisons B →
    ∀ p : ℕ, p ≤ 1 → p < B → Function.Injective (psi B p)

/-- The precise output required from distinct-evaluation factorization. -/
def CollisionSupportStep : Prop :=
  ∀ B : ℕ, 0 < B → EarlierComparisons B →
    ∀ p : ℕ, 2 ≤ p → p < B →
      Module.support (CoefficientRing B) (LinearMap.ker (psi B p)) ⊆
        PrimeSpectrum.zeroLocus (Depth.collisionIdeal B)

end KhanSL2.Conditional
