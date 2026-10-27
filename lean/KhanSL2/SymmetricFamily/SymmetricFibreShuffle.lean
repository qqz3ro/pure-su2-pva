module

public import KhanSL2.SymmetricFamily.FactorSpecialization
public import KhanSL2.SymmetricFamily.NativeShuffle
public import KhanSL2.Factorization.ShuffleEquivalences

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

/-! Transfer from the actual balanced ground-field shuffle to the original
native shuffle, and from iterated scalar extension to the genuine coefficient fibres. -/
noncomputable section
open CategoryTheory HomologicalComplex
namespace KhanSL2.SymmetricFamily
open Factorization

variable {A : Type} [CommRing A] [Algebra ℂ A]
  [Algebra A ℂ] [IsScalarTower ℂ A ℂ]

/-- Actual point-specialized factors retain the native shuffle comparison. -/
theorem factorSymmetric_shuffle_of_baseChanged (r s : ℕ) (f g : Polynomial A)
    [QuasiIso (balancedShuffleComplex ℂ
      (CoefficientBaseChange A (FactorSymmetric r f) ℂ)
      (CoefficientBaseChange A (FactorSymmetric s g) ℂ))] :
    QuasiIso (shuffleComplex (FactorSymmetric r (f.map (algebraMap A ℂ)))
      (FactorSymmetric s (g.map (algebraMap A ℂ)))) := by
  have := nativeShuffle_quasiIso_of_balanced
    (CoefficientBaseChange A (FactorSymmetric r f) ℂ)
    (CoefficientBaseChange A (FactorSymmetric s g) ℂ)
  have := shuffle_quasiIso_of_equiv_first
    (CoefficientBaseChange A (FactorSymmetric s g) ℂ)
      (factorSymmetricBaseChangeEquiv (K:=ℂ) r f).symm
  exact shuffle_quasiIso_of_equiv_second
    (FactorSymmetric r (f.map (algebraMap A ℂ)))
      (factorSymmetricBaseChangeEquiv (K:=ℂ) s g).symm

end KhanSL2.SymmetricFamily
