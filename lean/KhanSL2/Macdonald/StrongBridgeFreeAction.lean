module

public import KhanSL2.Macdonald.StrongBridgeCohomology
public import KhanSL2.Macdonald.StrongBridgeShift
public import KhanSL2.Macdonald.StrongBridgeFreeGrading

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The explicit source lowering operators preserve the actual free algebra;
their specified generator map intertwines the actual coefficient action. -/
noncomputable section
namespace KhanSL2.Macdonald

/-- Lowering mode numbers does not change a generator's colour. -/
theorem strongFreeLower_projFull (m : ℕ) (u : StrongMacdonald.W) :
    strongFreeLower m (StrongMacdonald.projFull u) =
      StrongMacdonald.projFull (strongFreeLower m u) := by
  apply strong_algHom_derivation_intertwining StrongMacdonald.projFull
    (strongFreeLower m) (strongFreeLower m)
    (strongFreeLower_homDer m) (strongFreeLower_homDer m)
  · intro g
    by_cases hc : g.color = 0 <;> by_cases hm : m ≤ g.index <;>
      simp [StrongMacdonald.projFull_sig, strongFreeLower_sig,
        StrongMacdonald.sigOf, hc, hm]
  · intro g
    by_cases hc : g.color = 0 <;> by_cases hm : m ≤ g.index <;>
      simp [StrongMacdonald.projFull_psi, strongFreeLower_psi,
        StrongMacdonald.psiOf, hc, hm]

/-- The source root-power-sum operator, with weight two on even generators. -/
def strongFreeLowerEnd (m : ℕ) : Module.End ℂ strongFree :=
  (strongFreeLower m).restrict (by
    intro u hu
    change StrongMacdonald.projFull u = u at hu
    change StrongMacdonald.projFull (strongFreeLower m u) = strongFreeLower m u
    rw [← strongFreeLower_projFull, hu])

@[simp] theorem strongFreeLowerEnd_val (m : ℕ) (u : strongFree) :
    (strongFreeLowerEnd m u).val = strongFreeLower m u.val := rfl

/-- Exact coefficient intertwining on the actual source, without an assumed module action. -/
theorem coefficientShift_strongFree (m : ℕ) (u : strongFree) :
    coefficientShift m (strongModel (StrongMacdonald.Gmap u.val)) =
      strongModel (StrongMacdonald.Gmap (strongFreeLowerEnd m u).val) :=
  coefficientShift_strongGmap m u.val

end KhanSL2.Macdonald
