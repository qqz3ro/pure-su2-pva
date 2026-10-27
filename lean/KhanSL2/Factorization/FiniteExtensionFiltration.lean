module

public import KhanSL2.Factorization.FiniteCurrent
public import KhanSL2.Factorization.ShuffleSubmoduleFiltration

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! A genuine finite current-submodule filtration is a finite extension of
its actual successive quotients. -/
noncomputable section
namespace KhanSL2.Factorization
open BGG
namespace FiniteExtensionClosure
variable {G : FiniteCurrent → Prop} {M : FiniteCurrent}

/-- Recover finite extension membership from the original finite filtration. -/
theorem of_filtration (F : ℕ → LieSubmodule ℂ Current M)
    (hF : Antitone F) (hzero : F 0 = ⊤) (n : ℕ) (hend : F n = ⊥)
    (hq : ∀ j, j<n → FiniteExtensionClosure G (FiniteCurrent.of (FiltrationGraded F j))) :
    FiniteExtensionClosure G M := by
  have haux : ∀ k j, j+k=n → FiniteExtensionClosure G (FiniteCurrent.of (F j)) := by
    intro k
    induction k with
    | zero =>
      intro j hj
      have hj' : j=n := by omega
      subst j
      apply FiniteExtensionClosure.zero
      refine ⟨fun x y => Subtype.ext ?_⟩
      have hx : x.val = 0 := (show F n ≤ ⊥ from le_of_eq hend) x.property
      have hy : y.val = 0 := (show F n ≤ ⊥ from le_of_eq hend) y.property
      exact hx.trans hy.symm
    | succ k ih =>
      intro j hj
      exact .extension _ _ (filtrationStepSplit F hF j)
        (ih (j+1) (by omega)) (hq j (by omega))
  exact .equiv (fullFiltrationEquiv F hzero) (haux n 0 (by omega))

end FiniteExtensionClosure
end KhanSL2.Factorization
