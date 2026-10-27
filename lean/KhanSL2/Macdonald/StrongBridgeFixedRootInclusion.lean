module

public import KhanSL2.Macdonald.StrongBridgeFixedCoordinates

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The fixed symmetric-degree root model is the corresponding actual
summand of the full root model, with its specified inclusion. -/
noncomputable section
open scoped DirectSum
namespace KhanSL2.Macdonald
open Factorization

/-- Convert fixed-degree monomial coordinates to their actual root blocks. -/
def fixedFreeRootEquiv (s : ℕ) : (FixedFreeIndex s →₀ ℂ) ≃ₗ[ℂ]
    ⨁ d : RootHomologyDegrees s, RootHomologyModel d.val.1 d.val.2 :=
  (Finsupp.domLCongr (fixedFreeBidegreeEquiv s).symm).trans
    ((sigmaFinsuppLequivDFinsupp ℂ).trans (DFinsupp.mapRange.linearEquiv
      (fun d : RootHomologyDegrees s => freeBidegreeRootEquiv d.val.1 d.val.2)))

/-- Embed the actual fixed-degree root blocks by their existing bidegrees. -/
def fixedRootInclusion (s : ℕ) :
    (⨁ d : RootHomologyDegrees s, RootHomologyModel d.val.1 d.val.2) →ₗ[ℂ]
      (⨁ d : ℕ × ℕ, RootHomologyModel d.1 d.2) :=
  DirectSum.toModule ℂ (RootHomologyDegrees s) _
    (fun d => DirectSum.lof ℂ (ℕ × ℕ) (fun d => RootHomologyModel d.1 d.2) d.val)

@[simp] theorem fixedRootInclusion_of (s : ℕ) (d : RootHomologyDegrees s)
    (x : RootHomologyModel d.val.1 d.val.2) :
    fixedRootInclusion s
      (DirectSum.of (fun d : RootHomologyDegrees s => RootHomologyModel d.val.1 d.val.2) d x) =
        DirectSum.of (fun d : ℕ × ℕ => RootHomologyModel d.1 d.2) d.val x :=
  DirectSum.toModule_lof ℂ (φ := fun d : RootHomologyDegrees s =>
    DirectSum.lof ℂ (ℕ × ℕ) (fun d => RootHomologyModel d.1 d.2) d.val) d x

theorem fixedRootInclusion_apply (s : ℕ)
    (x : ⨁ d : RootHomologyDegrees s, RootHomologyModel d.val.1 d.val.2)
    (d : RootHomologyDegrees s) : fixedRootInclusion s x d.val = x d := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add]
    change fixedRootInclusion s x d.val + fixedRootInclusion s y d.val = x d + y d
    rw [hx,hy]
  | of e x =>
    rw [fixedRootInclusion_of]
    by_cases he : d=e
    · subst e; simp
    · rw [DirectSum.of_eq_of_ne _ _ _ (fun h => he (Subtype.ext h)),
        DirectSum.of_eq_of_ne _ _ _ he]

theorem fixedRootInclusion_injective (s : ℕ) : Function.Injective (fixedRootInclusion s) := by
  intro x y h
  apply DFinsupp.ext
  intro d
  have hd := congrArg (fun v => v d.val) h
  simpa only [fixedRootInclusion_apply] using hd

/-- The root-basis construction commutes with extension of fixed-degree coordinates. -/
theorem freeRootModelEquiv_fixedInclusion (s : ℕ) (x : FixedFreeIndex s →₀ ℂ) :
    freeRootModelEquiv (fixedFreeCoordinateInclusion s x) =
      fixedRootInclusion s (fixedFreeRootEquiv s x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | single b c =>
    simp [freeRootModelEquiv,fixedFreeCoordinateInclusion,fixedFreeRootEquiv,
      Finsupp.domLCongr_single,freeBidegreePartitionEquiv,fixedFreeBidegreeEquiv]
    let d : RootHomologyDegrees s := ⟨(b.val.2.card,b.val.1.degree),b.property⟩
    let j : FreeBidegreeIndex d.val.1 d.val.2 := ⟨b.val,rfl,rfl⟩
    change DFinsupp.mapRange (fun d : ℕ × ℕ => freeBidegreeRootEquiv d.1 d.2)
      (fun d => map_zero (freeBidegreeRootEquiv d.1 d.2))
      (DFinsupp.single d.val (Finsupp.single j c)) =
        fixedRootInclusion s (DFinsupp.mapRange
          (fun d : RootHomologyDegrees s => freeBidegreeRootEquiv d.val.1 d.val.2)
          (fun d => map_zero (freeBidegreeRootEquiv d.val.1 d.val.2))
            (DFinsupp.single d (Finsupp.single j c)))
    rw [DFinsupp.mapRange_single,DFinsupp.mapRange_single]
    exact (fixedRootInclusion_of s d _).symm

/-- The specified fixed root model is the restriction of the actual total homology model. -/
theorem strongTotalHomologyRootEquiv_symmetricInclusion (s : ℕ)
    (u : TotalHomology (symmetricPower s)) :
    strongTotalHomologyRootEquiv (symmetricHomologyInclusion s u) =
      fixedRootInclusion s (symmetricPowerRootEquiv s u) := by
  change freeRootModelEquiv
    (strongFreeUncoloredEquiv (strongTotalHomologyFreeEquiv (symmetricHomologyInclusion s u))) = _
  rw [strongTotalHomologyFreeEquiv_symmetricInclusion,freeRootModelEquiv_fixedInclusion]
  rfl

/-- The weighted power-sum endomorphism in a fixed coefficient degree. -/
def fixedRootPowerSumEnd (m s : ℕ) : Module.End ℂ
    (⨁ d : RootHomologyDegrees s, RootHomologyModel d.val.1 d.val.2) :=
  DirectSum.lmap (fun d => rootHomologyPowerSumEnd m d.val.1 d.val.2)

/-- The fixed root action is the restriction of the original total root action. -/
theorem fixedRootInclusion_shift (m s : ℕ)
    (x : ⨁ d : RootHomologyDegrees s, RootHomologyModel d.val.1 d.val.2) :
    fixedRootInclusion s (fixedRootPowerSumEnd m s x) =
      rootTotalPowerSumEnd m (fixedRootInclusion s x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | of d x =>
    simp only [fixedRootPowerSumEnd,DirectSum.lmap_of,fixedRootInclusion_of,
      rootTotalPowerSumEnd_of]

end KhanSL2.Macdonald
