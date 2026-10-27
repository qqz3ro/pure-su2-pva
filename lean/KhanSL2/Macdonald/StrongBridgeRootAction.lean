module

public import KhanSL2.Macdonald.RootPolynomialAction
public import KhanSL2.Macdonald.StrongBridgeHomologyRaising

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The actual homology power sums become the explicit weighted root power sums. -/
noncomputable section
open scoped DirectSum
namespace KhanSL2.Macdonald
open Factorization

/-- The specified free algebra in alternating/symmetric root-polynomial coordinates. -/
def strongFreeRootEquiv : strongFree ≃ₗ[ℂ]
    ⨁ d : ℕ × ℕ, RootHomologyModel d.1 d.2 :=
  strongFreeUncoloredEquiv.trans freeRootModelEquiv

/-- The root comparison places each bidegree in its original direct-sum component. -/
theorem freeRootModelEquiv_inclusion (q r : ℕ) (x : FreeBidegreeIndex q r →₀ ℂ) :
    freeRootModelEquiv (freeBidegreeCoordinateInclusion q r x) =
      DirectSum.of (fun d : ℕ × ℕ => RootHomologyModel d.1 d.2) (q,r)
        (freeBidegreeRootEquiv q r x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | single b c =>
    have hb : freeBidegreePartitionEquiv.symm b.val = ⟨(q,r),b⟩ :=
      freeBidegreePartitionEquiv.symm_apply_eq.mpr rfl
    change DFinsupp.mapRange (fun d : ℕ × ℕ => freeBidegreeRootEquiv d.1 d.2)
      (fun d => map_zero (freeBidegreeRootEquiv d.1 d.2))
        ((sigmaFinsuppLequivDFinsupp ℂ)
          (Finsupp.domLCongr (R := ℂ) freeBidegreePartitionEquiv.symm
            (Finsupp.mapDomain (fun b : FreeBidegreeIndex q r => b.val) (Finsupp.single b c)))) = _
    rw [Finsupp.mapDomain_single,Finsupp.domLCongr_single,hb]
    have hs : (sigmaFinsuppLequivDFinsupp ℂ)
        (Finsupp.single (⟨(q,r),b⟩ : Σ d : ℕ × ℕ, FreeBidegreeIndex d.1 d.2) c) =
          DFinsupp.single (q,r) (Finsupp.single b c) := sigmaFinsuppEquivDFinsupp_single _ _
    rw [hs]
    exact DFinsupp.mapRange_single

/-- The canonical root coordinates agree with multiplication of the actual generator embeddings. -/
theorem strongFreeRootEquiv_bidegreeMap (q r : ℕ) (x : RootFreeBidegree q r) :
    strongFreeRootEquiv (rootFreeBidegreeMap q r x) =
      DirectSum.of (fun d : ℕ × ℕ => RootHomologyModel d.1 d.2) (q,r)
        (rootFreeToRootEquiv q r x) := by
  obtain ⟨y,rfl⟩ := (freeBidegreeSourceEquiv q r).surjective x
  change freeRootModelEquiv
    (strongFreeUncoloredEquiv (rootFreeBidegreeMap q r (freeBidegreeSourceEquiv q r y))) = _
  rw [rootFreeBidegreeMap_coordinates,freeRootModelEquiv_inclusion,rootFreeToRootEquiv_source]

/-- Actual weighted root multiplication on the algebraic direct sum. -/
def rootTotalPowerSumEnd (m : ℕ) : Module.End ℂ
    (⨁ d : ℕ × ℕ, RootHomologyModel d.1 d.2) :=
  DirectSum.lmap (fun d => rootHomologyPowerSumEnd m d.1 d.2)

@[simp] theorem rootTotalPowerSumEnd_of (m : ℕ) (d : ℕ × ℕ)
    (x : RootHomologyModel d.1 d.2) :
    rootTotalPowerSumEnd m
      (DirectSum.of (fun d : ℕ × ℕ => RootHomologyModel d.1 d.2) d x) =
        DirectSum.of (fun d : ℕ × ℕ => RootHomologyModel d.1 d.2) d
          (rootHomologyPowerSumEnd m d.1 d.2 x) := DirectSum.lmap_of _ _ _

/-- The explicitly defined free raising derivation becomes actual root-power-sum multiplication. -/
theorem strongFreeRootEquiv_shift (m : ℕ) (u : strongFree) :
    strongFreeRootEquiv (strongFreeRaiseEnd m u) =
      rootTotalPowerSumEnd m (strongFreeRootEquiv u) := by
  obtain ⟨y,rfl⟩ := strongFreeRootEquiv.symm.surjective u
  induction y using DirectSum.induction_on with
  | zero => simp
  | add y z hy hz => simp only [map_add,hy,hz]
  | of d x =>
    have hi : strongFreeRootEquiv.symm
        (DirectSum.of (fun d : ℕ × ℕ => RootHomologyModel d.1 d.2) d x) =
          rootFreeBidegreeMap d.1 d.2 ((rootFreeToRootEquiv d.1 d.2).symm x) := by
      apply strongFreeRootEquiv.symm_apply_eq.mpr
      rw [strongFreeRootEquiv_bidegreeMap,LinearEquiv.apply_symm_apply]
    rw [LinearEquiv.apply_symm_apply,rootTotalPowerSumEnd_of,hi,
      ← rootFreeBidegreeMap_shift,strongFreeRootEquiv_bidegreeMap,
      rootFreeToRootEquiv_shift,LinearEquiv.apply_symm_apply]

/-- The actual symmetric relative homology action is multiplication by
p_m(odd roots)+2p_m(even roots), under the specified homology equivalence. -/
theorem strongTotalHomologyRootEquiv_shift (m : ℕ)
    (h : TotalHomology SymmetricCoefficients) :
    strongTotalHomologyRootEquiv (totalSymmetricShift m h) =
      rootTotalPowerSumEnd m (strongTotalHomologyRootEquiv h) := by
  change strongFreeRootEquiv (strongTotalHomologyFreeEquiv (totalSymmetricShift m h)) =
    rootTotalPowerSumEnd m (strongFreeRootEquiv (strongTotalHomologyFreeEquiv h))
  rw [strongTotalHomologyFreeEquiv_shift,strongFreeRootEquiv_shift]

end KhanSL2.Macdonald
