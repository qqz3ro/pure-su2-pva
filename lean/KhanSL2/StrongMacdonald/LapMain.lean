module

public import KhanSL2.StrongMacdonald.LapPsiPsi

@[expose] public section

/-!
# FGT Lemma 3.13 for `𝔰𝔩₂`

`□̄ = □ + D + K` on the whole super-polynomial algebra `W`.
-/

noncomputable section
open scoped BigOperators

namespace KhanSL2.StrongMacdonald

theorem cross_Fam_psiOf_sigOf (i r k : ℕ) (b c : Fin 3) :
    cross (Fam i) (psiOf r b) (sigOf k c) = cross (Fam i) (sigOf k c) (psiOf r b) := by
  simp only [cross, Fam_sigOf, mul_zero, zero_mul, sub_zero, psiOf_mul_sigOf]
  rw [sigOf]
  congr 1
  exact (sig_commute _ _).symm

/-- **FGT Lemma 3.13.** `□̄ = □ + D + K`. -/
theorem lap_eq_box_D_K : lap = boxOp + DOp + KOp := by
  apply lap_eq_of
  · intro g N hg
    cases g with
    | s g =>
      exact Finset.sum_eq_zero fun i _ => Fam_sigOf i g.index g.color
    | p m => exact sum_Fam_psiOf m.index N m.color hg
  · intro g h N hg hh
    cases g with
    | s g =>
      cases h with
      | s h => exact Finset.sum_eq_zero fun i _ =>
          cross_Fam_sigOf_sigOf i g.index h.index g.color h.color
      | p m => exact sum_cross_sigOf_psiOf g.index m.index g.color m.color N hg hh
    | p m =>
      cases h with
      | s h =>
        have := sum_cross_sigOf_psiOf h.index m.index h.color m.color N hh hg
        rw [← Finset.sum_congr rfl fun i _ =>
          cross_Fam_psiOf_sigOf i m.index h.index m.color h.color] at this
        exact this
      | p m' => exact sum_cross_psiOf_psiOf m.index m'.index m.color m'.color N hg hh

end KhanSL2.StrongMacdonald
