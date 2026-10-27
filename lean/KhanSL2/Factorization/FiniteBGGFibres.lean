module

public import KhanSL2.SymmetricFamily.ExteriorFibreShuffle
public import KhanSL2.SymmetricFamily.FactorSpecializationExterior
public import KhanSL2.Factorization.BalancedScalarReflection
public import KhanSL2.Factorization.BalancedShuffleNative

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open CategoryTheory HomologicalComplex
namespace KhanSL2.Factorization.BGGTransfer
open BGG SymmetricFamily NonnegativeCone

variable {A : Type} [CommRing A] [Algebra ℂ A]
  [Algebra A ℂ] [IsScalarTower ℂ A ℂ]

/-- At every complex point the actual balanced exterior shuffle is a quasi-isomorphism.
Internal collisions within either factor remain allowed. -/
theorem exteriorShuffle_complexPoint (hSym : SymmetricTensorShuffle)
    (r s : ℕ) (hr : 0<r) (hs : 0<s) (f g : Polynomial A)
    (hf : f.Monic) (hg : g.Monic) (hfr : f.natDegree=r) (hgs : g.natDegree=s)
    (hfg : IsCoprime f g) :
    QuasiIso (scalarMap ℂ (balancedShuffleComplex A (FactorExterior r f) (FactorExterior s g))) := by
  let fp := f.map (algebraMap A ℂ)
  let gp := g.map (algebraMap A ℂ)
  have : QuasiIso (shuffleComplex (FactorExterior r fp) (FactorExterior s gp)) :=
    factorExterior_shuffle_of_symmetricTensorShuffle hSym r s hr hs fp gp
      (hf.map _) (hg.map _) ((hf.natDegree_map _).trans hfr) ((hg.natDegree_map _).trans hgs)
      (hfg.map (Polynomial.mapRingHom (algebraMap A ℂ)))
  have : QuasiIso (shuffleComplex (CoefficientBaseChange A (FactorExterior r f) ℂ)
      (FactorExterior s gp)) :=
    shuffle_quasiIso_of_equiv_first (FactorExterior s gp) (factorExteriorBaseChangeEquiv (K:=ℂ) r f)
  have : QuasiIso (shuffleComplex (CoefficientBaseChange A (FactorExterior r f) ℂ)
      (CoefficientBaseChange A (FactorExterior s g) ℂ)) :=
    shuffle_quasiIso_of_equiv_second (CoefficientBaseChange A (FactorExterior r f) ℂ)
      (factorExteriorBaseChangeEquiv (K:=ℂ) s g)
  have := balancedShuffleComplex_quasiIso_of_native
    (CoefficientBaseChange A (FactorExterior r f) ℂ) (CoefficientBaseChange A (FactorExterior s g) ℂ)
  exact balancedShuffleComplex_scalar_quasiIso_of_specialized A (FactorExterior r f) (FactorExterior s g) ℂ

end KhanSL2.Factorization.BGGTransfer
