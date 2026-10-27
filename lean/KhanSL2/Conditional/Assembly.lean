module

public import KhanSL2.Conditional.BGGInput
public import KhanSL2.Conditional.TopComparison
public import KhanSL2.Conditional.DepthAssembly
public import KhanSL2.Conditional.KernelTransport
public import KhanSL2.Conditional.Duality
public import KhanSL2.Deformation.LowDegree

@[expose] public section

/-! # Conditional completion from collision support alone -/

noncomputable section
namespace KhanSL2.Conditional
open scoped KhanSL2.Conditional
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- All unresolved hypotheses of the conditional completion, in one proposition. -/
structure RemainingInputs : Prop where
  collisionSupport : CollisionSupportStep

/-- The previously proved surjectivity supplies the other half of the induction hypothesis. -/
theorem earlier_bijective {B : ℕ} (h : EarlierComparisons B) (b : ℕ) (hb : b < B) (p : ℕ) :
    Function.Bijective (psi b p) := ⟨h b hb p, psi_surjective b p⟩

local instance termAddCommGroup (B p : ℕ) : AddCommGroup (BGGComplex.Term B p) := inferInstance
local instance termCoefficientModule (B : ℕ) (p : ℕ) :
    Module (CoefficientRing B) (BGGComplex.Term B p) := inferInstance
local instance cyclesAddCommGroup (B : ℕ) (p : ℕ) :
    AddCommGroup (Depth.cycles (BGGComplex.Term B) (bggDifferential B) p) := inferInstance
local instance cyclesCoefficientModule (B : ℕ) (p : ℕ) :
    Module (CoefficientRing B) (Depth.cycles (BGGComplex.Term B) (bggDifferential B) p) := inferInstance

section FixedBGG
variable (B : ℕ)

/-- Top-degree injectivity follows from the rank-one term and the proved surjectivity.
This also covers the base coefficient degree B=0. -/
theorem psi_top_injective : Function.Injective (psi B B) := by
  have hk : Function.Injective (topCycleMap B) :=
    rankOne_submodule_surjective_injective (topTermEquiv B)
      (Depth.cycles (BGGComplex.Term B) (bggDifferential B) B)
      (topCycleMap B) (topCycleMap_surjective B)
  intro x y hxy
  obtain ⟨u, hu⟩ := cyclesToK_surjective B B x
  obtain ⟨v, hv⟩ := cyclesToK_surjective B B y
  have huv : topCycleMap B u = topCycleMap B v :=
    (congrArg (fun z : K B B => depthJBTopEquiv B (psi B B z)) hu).trans
      ((congrArg (depthJBTopEquiv B) hxy).trans
        (congrArg (fun z : K B B => depthJBTopEquiv B (psi B B z)) hv).symm)
  exact hu.symm.trans ((congrArg (cyclesToK B B) (hk huv)).trans hv)

end FixedBGG

/-- No degree above B remains in actual coefficient homology; no remaining input is used. -/
theorem psi_above_injective (B p : ℕ) (hp : B < p) : Function.Injective (psi B p) := by
  have : Subsingleton (BGGComplex.Term B p) := BGGComplex.term_subsingleton_of_lt B p hp
  have : Subsingleton (BGGComplex.Homology B p) := inferInstance
  have : Subsingleton (K B p) := (BGGComplex.homologyEquivK B p).symm.injective.subsingleton
  exact Function.injective_of_subsingleton _

/-- The actual top differential vanishes; it is not an additional remaining hypothesis. -/
theorem bgg_top_differential_zero_succ (n : ℕ) : bggDifferential (n+1) n = 0 := by
  have : Module.Projective (CoefficientRing (n+1)) (BGGComplex.Term (n+1) n) :=
    PolynomialBGG.bggTerm_projective (n+1) n
  have : Module.IsTorsionFree (CoefficientRing (n+1)) (BGGComplex.Term (n+1) n) :=
    projective_isTorsionFree (R := CoefficientRing (n+1)) (N := BGGComplex.Term (n+1) n)
  exact top_differential_eq_zero (topTermEquiv (n+1)) (bggDifferential (n+1) n)
    (topCycleMap (n+1)) (topCycleMap_surjective (n+1))

theorem bgg_top_differential_zero (B : ℕ) (hB : 0 < B) : bggDifferential B (B-1) = 0 := by
  cases B with
  | zero => omega
  | succ n => exact bgg_top_differential_zero_succ n

/-- The depth theorem gives every middle-degree injection from actual kernel support. -/
theorem psi_middle_injective (B : ℕ) (hB : 0 < B)
    (hsupp : ∀ p : ℕ, 2 ≤ p → p < B →
      Module.support (CoefficientRing B) (LinearMap.ker (psi B p)) ⊆
        PrimeSpectrum.zeroLocus (Depth.collisionIdeal B))
    (p : ℕ) (hp : 2 ≤ p) (hpB : p < B) : Function.Injective (psi B p) := by
  have : ∀ q, Module.Finite (CoefficientRing B) (BGGComplex.Term B q) :=
    fun q => PolynomialBGG.bggTerm_finite B q
  have : ∀ q, Module.Projective (CoefficientRing B) (BGGComplex.Term B q) :=
    fun q => PolynomialBGG.bggTerm_projective B q
  have ht : bggDifferential B (Depth.collisionList B).length = 0 := by
    rw [Depth.collisionList_length]
    exact bgg_top_differential_zero B hB
  have hk := kernel_eq_zero_of_support_of_top_zero
    (R := CoefficientRing B) (C := BGGComplex.Term B)
    (d := bggDifferential B) (rs := Depth.collisionList B) (Depth.collisionList_isRegular B)
    ht (fun q => bggDifferential_square_zero B q) (J B)
    (fun q => (psi B q).comp (bggHomologyEquiv B q).toLinearMap)
    (fun q _ _ => (psi_surjective B q).comp (bggHomologyEquiv B q).surjective)
    (fun q hq hc => (support_ker_comp_subset_iff (bggHomologyEquiv B q) (psi B q)
      (PrimeSpectrum.zeroLocus (Depth.collisionIdeal B))).2
        (hsupp q hq (by rw [Depth.collisionList_length] at hc; omega)))
    (fun q hq hc => Depth.depth_JB_ge B q (by omega)
      (by rw [Depth.collisionList_length] at hc; omega))
    p hp (by rw [Depth.collisionList_length]; omega)
  exact (injective_comp_equiv_iff (bggHomologyEquiv B p) (psi B p)).mp
    (LinearMap.ker_eq_bot.mp hk)

/-- Strong induction uses proved polynomial properties and low degrees, with collision support as its only input. -/
theorem psi_injective_of_inputs (H : RemainingInputs) :
    ∀ B p : ℕ, Function.Injective (psi B p) := by
  intro B
  induction B using Nat.strong_induction_on with
  | h B ih =>
    have he : EarlierComparisons B := ih
    intro p
    by_cases hp : p = B
    · subst p
      exact psi_top_injective B
    by_cases ha : B < p
    · exact psi_above_injective B p ha
    have hpB : p < B := by omega
    have hB : 0 < B := by omega
    by_cases hl : p ≤ 1
    · exact KhanSL2.lowDegreeStep B hB he p hl hpB
    · exact psi_middle_injective B hB (H.collisionSupport B hB he) p (by omega) hpB

/-- Conditional bijectivity concerns the existing polynomial comparison map. -/
theorem psiB_bijective_of_inputs (H : RemainingInputs) (B p : ℕ) :
    Function.Bijective (Modules.psiB B p) :=
  ⟨(psi_injective_iff B p).mp (psi_injective_of_inputs H B p), Modules.psiB_surjective B p⟩

/-- The full original PVA-isomorphism proposition, conditional only on the named milestones. -/
theorem mainStatement_of_inputs (H : RemainingInputs) : MainStatement :=
  mainStatement_of_psiB_injective (fun B p => (psiB_bijective_of_inputs H B p).1)

/-- Collision support alone closes the comparison induction in every degree. -/
theorem psi_injective_of_collisionSupport (hC : CollisionSupportStep) :
    ∀ B p : ℕ, Function.Injective (psi B p) :=
  psi_injective_of_inputs ⟨hC⟩

/-- Collision support alone gives bijectivity of the actual coefficient comparison. -/
theorem psiB_bijective_of_collisionSupport (hC : CollisionSupportStep) (B p : ℕ) :
    Function.Bijective (Modules.psiB B p) :=
  psiB_bijective_of_inputs ⟨hC⟩ B p

/-- The original specified-map PVA-isomorphism follows from collision support alone. -/
theorem mainStatement_of_collisionSupport (hC : CollisionSupportStep) : MainStatement :=
  mainStatement_of_inputs ⟨hC⟩

end KhanSL2.Conditional

