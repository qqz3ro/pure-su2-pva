module

public import KhanSL2.Macdonald.StrongBridgeFixedRootModel
public import KhanSL2.Macdonald.StrongBridgeRootAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The fixed-degree coordinates are the restriction of the actual total
homology coordinates, under the original coefficient inclusion. -/
noncomputable section
open scoped DirectSum
namespace KhanSL2.Macdonald
open Factorization

/-- Forget the fixed coefficient degree by extending coordinates by zero. -/
def fixedStrongCoordinateInclusion (s : ℕ) :
    (FixedStrongFreeIndex s →₀ ℂ) →ₗ[ℂ] (strongFreeIndices →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ (fun b => b.val)

@[simp] theorem symmetricPowerHomologyCoordinateEquiv_apply_graded (s w : ℕ)
    (u : TotalHomology (symmetricPower s)) (b : strongFreePieceIndices w s) :
    symmetricPowerHomologyCoordinateEquiv s u (strongFixedIndexEquiv s ⟨w,b⟩) =
      strongWeightHomologyCoordinateEquiv w s
        (weightHomologyComponent w s (symmetricHomologyInclusion s u)) b := by
  change Finsupp.domLCongr (R := ℂ) (strongFixedIndexEquiv s)
    ((sigmaFinsuppLequivDFinsupp ℂ).symm
      (DFinsupp.mapRange.linearEquiv (fun w => strongWeightHomologyCoordinateEquiv w s)
        (symmetricPowerHomologyEquiv s u))) (strongFixedIndexEquiv s ⟨w,b⟩) = _
  rw [Finsupp.domLCongr_apply,Finsupp.domCongr_apply,Finsupp.equivMapDomain_apply,
    Equiv.symm_apply_apply]
  change strongWeightHomologyCoordinateEquiv w s (symmetricPowerHomologyEquiv s u w) b = _
  rw [symmetricPowerHomologyEquiv_apply]

@[simp] theorem strongTotalHomologyCoordinateEquiv_apply_graded
    (u : TotalHomology SymmetricCoefficients) (w s : ℕ)
    (b : strongFreePieceIndices w s) :
    strongTotalHomologyCoordinateEquiv u (strongFreeGradedIndexEquiv ⟨(w,s),b⟩) =
      strongWeightHomologyCoordinateEquiv w s (weightHomologyComponent w s u) b := by
  change Finsupp.domLCongr (R := ℂ) strongFreeGradedIndexEquiv
    (strongTotalHomologyGradedCoordinateEquiv u) (strongFreeGradedIndexEquiv ⟨(w,s),b⟩) = _
  rw [Finsupp.domLCongr_apply,Finsupp.domCongr_apply,Finsupp.equivMapDomain_apply,
    Equiv.symm_apply_apply,strongTotalHomologyGradedCoordinateEquiv_apply]

/-- The actual coefficient inclusion has no components in other symmetric degrees. -/
theorem weightHomologyComponent_symmetricInclusion_ne (s w t : ℕ) (ht : t ≠ s)
    (u : TotalHomology (symmetricPower s)) :
    weightHomologyComponent w t (symmetricHomologyInclusion s u) = 0 := by
  obtain ⟨y,rfl⟩ := (weightSymmetricHomologyEquiv s).surjective u
  induction y using DirectSum.induction_on with
  | zero => simp
  | add y z hy hz => simp only [map_add,hy,hz,add_zero]
  | of w' y =>
    rw [weightSymmetricHomologyEquiv_of]
    have hi := symmetricHomologyProjection_weightInclusion s w' s y
    rw [if_pos rfl] at hi
    rw [hi]
    exact weightHomologyComponent_inclusion_ne (fun he => ht (congrArg Prod.snd he)) y

/-- Exact compatibility of fixed and total coordinates with the original inclusion. -/
theorem strongTotalHomologyCoordinateEquiv_symmetricInclusion (s : ℕ)
    (u : TotalHomology (symmetricPower s)) :
    strongTotalHomologyCoordinateEquiv (symmetricHomologyInclusion s u) =
      fixedStrongCoordinateInclusion s (symmetricPowerHomologyCoordinateEquiv s u) := by
  apply Finsupp.ext
  intro b
  obtain ⟨⟨⟨w,t⟩,c⟩,rfl⟩ := strongFreeGradedIndexEquiv.surjective b
  rw [strongTotalHomologyCoordinateEquiv_apply_graded]
  by_cases ht : t=s
  · subst t
    have hc : strongFreeGradedIndexEquiv ⟨(w,s),c⟩ =
        (strongFixedIndexEquiv s ⟨w,c⟩).val := rfl
    rw [hc]
    change _ = Finsupp.mapDomain (fun b : FixedStrongFreeIndex s => b.val)
      (symmetricPowerHomologyCoordinateEquiv s u) ((strongFixedIndexEquiv s ⟨w,c⟩).val)
    rw [Finsupp.mapDomain_apply_of_injective Subtype.val_injective,
      symmetricPowerHomologyCoordinateEquiv_apply_graded]
  · rw [weightHomologyComponent_symmetricInclusion_ne s w t ht,map_zero,Finsupp.zero_apply]
    change 0 = Finsupp.mapDomain (fun b : FixedStrongFreeIndex s => b.val)
      (symmetricPowerHomologyCoordinateEquiv s u) (strongFreeGradedIndexEquiv ⟨(w,t),c⟩)
    symm
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨b,hb⟩
    change b.val = strongFreeGradedIndexEquiv ⟨(w,t),c⟩ at hb
    have hp := b.property
    rw [hb] at hp
    exact ht (c.property.2.2.symm.trans hp)

/-- Extend fixed-degree uncolored coordinates into the full free model. -/
def fixedFreeCoordinateInclusion (s : ℕ) :
    (FixedFreeIndex s →₀ ℂ) →ₗ[ℂ] (FreeMonomialIndex →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ (fun b => b.val)

theorem coordinateScaleEquiv_single {ι : Type*} (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (i : ι) (c : ℂ) : coordinateScaleEquiv a ha (Finsupp.single i c) =
      Finsupp.single i (a i*c) := by
  ext j
  by_cases hj : i=j
  · subst j; simp
  · simp [hj,Ne.symm hj]

/-- The factorial normalization and color removal commute with this inclusion. -/
theorem fixedStrongCoordinateInclusion_normalization (s : ℕ)
    (x : FixedStrongFreeIndex s →₀ ℂ) :
    Finsupp.domLCongr (R := ℂ) strongFreeIndexEquiv
      (strongFreeNormalization (fixedStrongCoordinateInclusion s x)) =
        fixedFreeCoordinateInclusion s
          (Finsupp.domLCongr (R := ℂ) (fixedFreeIndexEquiv s)
            (coordinateScaleEquiv (fun b : FixedStrongFreeIndex s => (strongFreeFactorial b.val)⁻¹)
              (fun b => inv_ne_zero (strongFreeFactorial_ne_zero b.val)) x)) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | single b c =>
    simp only [fixedStrongCoordinateInclusion,fixedFreeCoordinateInclusion,
      Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,strongFreeNormalization,coordinateScaleEquiv_single,
      Finsupp.domLCongr_single]
    rfl

/-- The normalized fixed model is the restriction of the specified total model. -/
theorem strongTotalHomologyFreeEquiv_symmetricInclusion (s : ℕ)
    (u : TotalHomology (symmetricPower s)) :
    strongFreeUncoloredEquiv (strongTotalHomologyFreeEquiv (symmetricHomologyInclusion s u)) =
      fixedFreeCoordinateInclusion s (symmetricPowerHomologyFreeCoordinateEquiv s u) := by
  change Finsupp.domLCongr (R := ℂ) strongFreeIndexEquiv
    (strongFreeCoordinateEquiv (strongTotalHomologyFreeEquiv (symmetricHomologyInclusion s u))) = _
  have hn : strongFreeCoordinateEquiv (strongTotalHomologyFreeEquiv
      (symmetricHomologyInclusion s u)) =
        strongFreeNormalization (strongTotalHomologyCoordinateEquiv
          (symmetricHomologyInclusion s u)) := by
    ext b
    exact strongTotalHomologyFreeEquiv_coordinate _ b
  rw [hn,strongTotalHomologyCoordinateEquiv_symmetricInclusion,
    fixedStrongCoordinateInclusion_normalization]
  rfl

end KhanSL2.Macdonald
