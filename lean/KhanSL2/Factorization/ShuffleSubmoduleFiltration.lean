module

public import KhanSL2.Factorization.ShuffleFiniteFiltration
public import KhanSL2.Factorization.ShuffleEquivalences
public import KhanSL2.Factorization.CoefficientSplitFinite

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Finite filtrations by actual current submodules give dévissage for the
specified shuffle. All constant splittings are proved from finite dimension. -/
noncomputable section
open CategoryTheory
namespace KhanSL2.Factorization
open BGG
variable {M : Type} [AddCommGroup M] [Module ℂ M]
  [LieRingModule Current M] [LieModule ℂ Current M] [FiniteDimensional ℂ M]

/-- The successor as a submodule of the present filtration term. -/
def filtrationSuccessor (F : ℕ → LieSubmodule ℂ Current M) (j : ℕ) :
    LieSubmodule ℂ Current (F j) := (F (j+1)).comap (F j).incl

/-- The original successive quotient. -/
abbrev FiltrationGraded (F : ℕ → LieSubmodule ℂ Current M) (j : ℕ) :=
  F j ⧸ filtrationSuccessor F j

/-- The actual inclusion and quotient form a constant-split exact sequence. -/
def filtrationStepSplit (F : ℕ → LieSubmodule ℂ Current M) (hF : Antitone F) (j : ℕ) :
    ConstantSplitExact (LieSubmodule.inclusion (hF (Nat.le_succ j)))
      (LieSubmodule.Quotient.mk' (filtrationSuccessor F j)) :=
  Classical.choice (nonempty_constantSplitExact _ _
    (LieSubmodule.inclusion_injective _) (by
      intro x
      rw [LieSubmodule.Quotient.mk_eq_zero]
      constructor
      · intro hx
        exact ⟨⟨x.val,hx⟩,Subtype.ext rfl⟩
      · rintro ⟨y,rfl⟩
        exact y.property)
    (LieSubmodule.Quotient.surjective_mk' _))

/-- A full filtration term is its original ambient current module. -/
def fullFiltrationEquiv (F : ℕ → LieSubmodule ℂ Current M) (hF : F 0 = ⊤) :
    M ≃ₗ⁅ℂ,Current⁆ F 0 where
  toFun m := ⟨m,by rw [hF]; trivial⟩
  invFun m := m.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  map_lie' := rfl

variable (T : Type) [AddCommGroup T] [Module ℂ T]
  [LieRingModule Current T] [LieModule ℂ Current T]

/-- The first-variable filtration criterion needs only the original graded comparisons. -/
theorem shuffle_quasiIso_submoduleFiltration_first
    (F : ℕ → LieSubmodule ℂ Current M) (hF : Antitone F) (hzero : F 0 = ⊤)
    (n : ℕ) (hend : F n = ⊥)
    (hq : ∀ j, j<n → QuasiIso (shuffleComplex (FiltrationGraded F j) T)) :
    QuasiIso (shuffleComplex M T) := by
  have : Subsingleton (F n) := by
    refine ⟨fun x y => Subtype.ext ?_⟩
    have hx : (x : M) = 0 := (show F n ≤ ⊥ from le_of_eq hend) x.property
    have hy : (y : M) = 0 := (show F n ≤ ⊥ from le_of_eq hend) y.property
    exact hx.trans hy.symm
  have : QuasiIso (shuffleComplex (F 0) T) :=
    shuffle_quasiIso_finiteFiltration_zero_first (fun j => F j) (FiltrationGraded F) T
      (fun j => LieSubmodule.inclusion (hF (Nat.le_succ j)))
      (fun j => LieSubmodule.Quotient.mk' (filtrationSuccessor F j)) n
      (fun j _ => filtrationStepSplit F hF j) hq
  exact shuffle_quasiIso_of_equiv_first T (fullFiltrationEquiv F hzero)

/-- The same criterion holds in the second coefficient variable. -/
theorem shuffle_quasiIso_submoduleFiltration_second
    (F : ℕ → LieSubmodule ℂ Current M) (hF : Antitone F) (hzero : F 0 = ⊤)
    (n : ℕ) (hend : F n = ⊥)
    (hq : ∀ j, j<n → QuasiIso (shuffleComplex T (FiltrationGraded F j))) :
    QuasiIso (shuffleComplex T M) := by
  have : Subsingleton (F n) := by
    refine ⟨fun x y => Subtype.ext ?_⟩
    have hx : (x : M) = 0 := (show F n ≤ ⊥ from le_of_eq hend) x.property
    have hy : (y : M) = 0 := (show F n ≤ ⊥ from le_of_eq hend) y.property
    exact hx.trans hy.symm
  have : QuasiIso (shuffleComplex T (F 0)) :=
    shuffle_quasiIso_finiteFiltration_zero_second (fun j => F j) (FiltrationGraded F) T
      (fun j => LieSubmodule.inclusion (hF (Nat.le_succ j)))
      (fun j => LieSubmodule.Quotient.mk' (filtrationSuccessor F j)) n
      (fun j _ => filtrationStepSplit F hF j) hq
  exact shuffle_quasiIso_of_equiv_second T (fullFiltrationEquiv F hzero)

end KhanSL2.Factorization
