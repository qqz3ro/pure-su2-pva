module

public import KhanSL2.Macdonald.StrongBridgeGenerators
public import KhanSL2.Macdonald.GeneratorShift
public import KhanSL2.StrongMacdonald.SliceRing

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The specified Macdonald generator map intertwines the actual coefficient
power sums with weight-two even and weight-one odd root shifts. -/
noncomputable section
namespace KhanSL2.Macdonald

/-- The free-source lowering action dual to root power sums of weights 2 and 1. -/
def strongFreeLower (m : ℕ) : Module.End ℂ StrongMacdonald.W :=
  StrongMacdonald.mkDer
    (fun g => if m ≤ g.index then (2 : ℂ) • StrongMacdonald.sigOf (g.index-m) g.color else 0)
    (fun g => if m ≤ g.index then StrongMacdonald.psiOf (g.index-m) g.color else 0)

theorem strongFreeLower_homDer (m : ℕ) : StrongMacdonald.HomDer 0 (strongFreeLower m) :=
  StrongMacdonald.mkDer_homDer _ _
    (fun _g => StrongMacdonald.isPar_ite _ ((StrongMacdonald.isPar_sigOf _ _).smul _))
    (fun _g => StrongMacdonald.isPar_ite _ (StrongMacdonald.isPar_psiOf _ _))

@[simp] theorem strongFreeLower_sig (m : ℕ) (g : StrongMacdonald.SMode) :
    strongFreeLower m (StrongMacdonald.sig g) =
      if m ≤ g.index then (2 : ℂ) • StrongMacdonald.sigOf (g.index-m) g.color else 0 :=
  StrongMacdonald.mkDer_sig _ _ _

@[simp] theorem strongFreeLower_psi (m : ℕ) (g : Mode) :
    strongFreeLower m (StrongMacdonald.psi g) =
      if m ≤ g.index then StrongMacdonald.psiOf (g.index-m) g.color else 0 :=
  StrongMacdonald.mkDer_psi _ _ _

@[simp] theorem strongModel_Gmap_sig (g : StrongMacdonald.SMode) :
    strongModel (StrongMacdonald.Gmap (StrongMacdonald.sig g)) =
      if g.color = 0 then -S g.index else 0 := by
  rw [StrongMacdonald.Gmap, StrongMacdonald.substW_sig, StrongMacdonald.Gsig]
  split <;> simp

@[simp] theorem strongModel_Gmap_psi (g : Mode) :
    strongModel (StrongMacdonald.Gmap (StrongMacdonald.psi g)) =
      if g.color = 0 then (2 : ℂ) • E (g.index+1) else 0 := by
  rw [StrongMacdonald.Gmap, StrongMacdonald.substW_psi, StrongMacdonald.Gpsi]
  split <;> simp

theorem coefficientShift_strongGmap_sig (m : ℕ) (g : StrongMacdonald.SMode) :
    coefficientShift m (strongModel (StrongMacdonald.Gmap (StrongMacdonald.sig g))) =
      strongModel (StrongMacdonald.Gmap (strongFreeLower m (StrongMacdonald.sig g))) := by
  rw [strongModel_Gmap_sig, strongFreeLower_sig]
  by_cases hc : g.color = 0 <;> by_cases hm : m ≤ g.index <;>
    simp [hc, hm, coefficientShift_S, StrongMacdonald.sigOf]

theorem coefficientShift_strongGmap_psi (m : ℕ) (g : Mode) :
    coefficientShift m (strongModel (StrongMacdonald.Gmap (StrongMacdonald.psi g))) =
      strongModel (StrongMacdonald.Gmap (strongFreeLower m (StrongMacdonald.psi g))) := by
  rw [strongModel_Gmap_psi, strongFreeLower_psi]
  by_cases hc : g.color = 0
  · rw [if_pos hc]
    by_cases hm : m ≤ g.index
    · rw [if_pos hm]
      simp only [map_smul, coefficientShift_E]
      have he : g.index+1-m = g.index-m+1 := by omega
      simp [StrongMacdonald.psiOf, hc, he]
    · rw [if_neg hm, map_zero, map_zero, map_smul,
        coefficientShift_E_eq_zero (by omega), smul_zero]
  · rw [if_neg hc, map_zero]
    split <;> simp [StrongMacdonald.psiOf, hc]

/-- The coefficient operator identity holds on every free expression, retaining
 the actual -S and 2E normalization of the imported theorem. -/
theorem coefficientShift_strongGmap (m : ℕ) (u : StrongMacdonald.W) :
    coefficientShift m (strongModel (StrongMacdonald.Gmap u)) =
      strongModel (StrongMacdonald.Gmap (strongFreeLower m u)) := by
  refine StrongMacdonald.induction_gen (P := fun u =>
    coefficientShift m (strongModel (StrongMacdonald.Gmap u)) =
      strongModel (StrongMacdonald.Gmap (strongFreeLower m u))) ?_ ?_ ?_ ?_ ?_ ?_ u
  · simp
  · rw [map_one, strongModel_one, coefficientShift_one,
      (strongFreeLower_homDer m).map_one, map_zero, map_zero]
  · intro u v hu hv
    simp only [map_add, hu, hv]
  · intro c u hu
    simp only [map_smul, hu]
  · intro g u hu
    rw [map_mul, strongModel_mul, coefficientShift_mul, coefficientShift_strongGmap_sig, hu,
      (strongFreeLower_homDer m).zero_mul_apply, map_add, map_mul, map_mul,
      map_add, strongModel_mul, strongModel_mul]
  · intro g u hu
    rw [map_mul, strongModel_mul, coefficientShift_mul, coefficientShift_strongGmap_psi, hu,
      (strongFreeLower_homDer m).zero_mul_apply, map_add, map_mul, map_mul,
      map_add, strongModel_mul, strongModel_mul]

end KhanSL2.Macdonald
