module

public import KhanSL2.Macdonald.StrongBridgeIndexDegree
public import KhanSL2.Factorization.RelativeChainsSymmetricHomology

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The actual fixed symmetric-coefficient degree homology, with precisely
q+2r=s root-polynomial summands and the specified factorial normalization. -/
noncomputable section
open scoped DirectSum
namespace KhanSL2.Macdonald
open Factorization

abbrev FixedStrongFreeIndex (s : ℕ) :=
  {b : strongFreeIndices // StrongMacdonald.diagVal (fun _ => 2) (fun _ => 1) b.val.1 b.val.2 = s}

abbrev FixedFreeIndex (s : ℕ) :=
  {b : FreeMonomialIndex // 2*b.1.degree+b.2.card = s}

abbrev RootHomologyDegrees (s : ℕ) := {d : ℕ × ℕ // 2*d.2+d.1 = s}

/-- Forget the uniquely determined loop weight in a fixed coefficient degree. -/
def strongFixedIndexEquiv (s : ℕ) :
    (Σ w : ℕ, strongFreePieceIndices w s) ≃ FixedStrongFreeIndex s where
  toFun b := ⟨⟨b.2.val,b.2.property.1⟩,b.2.property.2.2⟩
  invFun b := ⟨StrongMacdonald.wtVal b.val.val.1 b.val.val.2,
    ⟨b.val.val,b.val.property,rfl,b.property⟩⟩
  left_inv b := by
    obtain ⟨w,b,hb⟩ := b
    rcases hb with ⟨hp,hw,hs⟩
    dsimp only
    cases hw
    rfl
  right_inv _b := rfl

/-- Remove only the fixed color labels, preserving actual coefficient degree. -/
def fixedFreeIndexEquiv (s : ℕ) : FixedStrongFreeIndex s ≃ FixedFreeIndex s :=
  strongFreeIndexEquiv.subtypeEquiv (fun b => by rw [strongFreeIndex_coefficientDegree])

/-- The finite-weight homology coordinates of a fixed symmetric power. -/
def symmetricPowerHomologyCoordinateEquiv (s : ℕ) :
    TotalHomology (symmetricPower s) ≃ₗ[ℂ] FixedStrongFreeIndex s →₀ ℂ :=
  (symmetricPowerHomologyEquiv s).trans
    ((DFinsupp.mapRange.linearEquiv (fun w => strongWeightHomologyCoordinateEquiv w s)).trans
      ((sigmaFinsuppLequivDFinsupp ℂ).symm.trans (Finsupp.domLCongr (strongFixedIndexEquiv s))))

/-- Apply the original symmetric factorial normalization within the fixed coefficient degree. -/
def symmetricPowerHomologyFreeCoordinateEquiv (s : ℕ) :
    TotalHomology (symmetricPower s) ≃ₗ[ℂ] FixedFreeIndex s →₀ ℂ :=
  (symmetricPowerHomologyCoordinateEquiv s).trans
    ((coordinateScaleEquiv (fun b : FixedStrongFreeIndex s => (strongFreeFactorial b.val)⁻¹)
      (fun b => inv_ne_zero (strongFreeFactorial_ne_zero b.val))).trans
        (Finsupp.domLCongr (fixedFreeIndexEquiv s)))

/-- Partition the fixed coefficient degree by its actual odd/even generator counts. -/
def fixedFreeBidegreeEquiv (s : ℕ) :
    (Σ d : RootHomologyDegrees s, FreeBidegreeIndex d.val.1 d.val.2) ≃ FixedFreeIndex s where
  toFun b := ⟨b.2.val,by
    rw [b.2.property.1,b.2.property.2]
    exact b.1.property⟩
  invFun b := ⟨⟨(b.val.2.card,b.val.1.degree),b.property⟩,⟨b.val,rfl,rfl⟩⟩
  left_inv b := by
    obtain ⟨⟨⟨q,r⟩,hd⟩,b,hb⟩ := b
    rcases hb with ⟨he,ho⟩
    dsimp only
    cases he
    cases ho
    rfl
  right_inv _b := rfl

/-- The proved actual symmetric-power homology formula, with the specified root coordinates. -/
def symmetricPowerRootEquiv (s : ℕ) : TotalHomology (symmetricPower s) ≃ₗ[ℂ]
    ⨁ d : RootHomologyDegrees s, RootHomologyModel d.val.1 d.val.2 :=
  (symmetricPowerHomologyFreeCoordinateEquiv s).trans
    ((Finsupp.domLCongr (fixedFreeBidegreeEquiv s).symm).trans
      ((sigmaFinsuppLequivDFinsupp ℂ).trans (DFinsupp.mapRange.linearEquiv
        (fun d : RootHomologyDegrees s => freeBidegreeRootEquiv d.val.1 d.val.2))))

end KhanSL2.Macdonald
