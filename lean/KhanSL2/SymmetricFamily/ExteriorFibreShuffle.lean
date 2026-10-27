module

public import KhanSL2.SymmetricFamily.FactorTensorWords
public import KhanSL2.Factorization.EvenTensorShuffle

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KhanSL2.SymmetricFamily
open Factorization

/-- The original exterior coefficient fibres factor under the actual CE shuffle
at any two coprime positive-degree polynomials, with internal collisions allowed. -/
theorem factorExterior_shuffle_of_symmetricTensorShuffle (hSym : SymmetricTensorShuffle)
    (r s : ℕ) (hr : 0<r) (hs : 0<s) (f g : Polynomial ℂ)
    (hf : f.Monic) (hg : g.Monic) (hfr : f.natDegree=r) (hgs : g.natDegree=s)
    (hfg : IsCoprime f g) :
    QuasiIso (shuffleComplex (FactorExterior r f) (FactorExterior s g)) := by
  obtain ⟨u,hu,hsu,_,⟨eu⟩⟩ := exists_factorExteriorWordEquiv r f hf hfr hr
  obtain ⟨v,hv,hsv,_,⟨ev⟩⟩ := exists_factorExteriorWordEquiv s g hg hgs hs
  have hd : Disjoint u.support v.support := by
    rw [hsu,hsv]
    exact EvenTensorWord.root_support_disjoint hf.ne_zero hg.ne_zero hfg
  have : QuasiIso (shuffleComplex u.exteriorModule v.exteriorModule) :=
    exteriorTensorWord_shuffle hSym u v hu hv hd
  have : QuasiIso (shuffleComplex (FactorExterior r f) v.exteriorModule) :=
    shuffle_quasiIso_of_equiv_first v.exteriorModule eu
  exact shuffle_quasiIso_of_equiv_second (FactorExterior r f) ev

end KhanSL2.SymmetricFamily
