module

public import KhanSL2.SymmetricFamily.FactorCoprimeExterior
public import KhanSL2.SymmetricFamily.FactorSymmetricTensorWords
public import KhanSL2.SymmetricFamily.SymmetricTensorWords
public import KhanSL2.Factorization.EvenTensorPolynomialDecomposition
public import KhanSL2.Factorization.CurrentTensorEquiv

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048

/-! Iterating the genuine coprime coefficient equivalence gives the original
global fibre as the actual tensor of its one-point fibres. -/
noncomputable section
namespace KhanSL2.SymmetricFamily
open Factorization Factorization.EvenTensorWord

/-- The global exterior fibre is the corresponding genuine local exterior tensor family. -/
def factorExteriorWordEquiv (t : EvenTensorWord) (ht : t.Distinct) :
    FactorExterior t.weight t.polynomial ≃ₗ⁅ℂ,BGG.Current⁆ t.exteriorModule := by
  induction t with
  | leaf a q =>
    exact { (LinearEquiv.refl ℂ (LocalExteriorFibre q a)) with map_lie' := rfl }
  | tensor u v ihu ihv =>
    exact (factorExteriorCoprimeComplexEquiv u.weight v.weight u.polynomial v.polynomial
      u.polynomial_monic v.polynomial_monic u.polynomial_natDegree v.polynomial_natDegree
      (u.polynomial_isCoprime v ht.2.2)).trans (tensorCurrentEquiv (ihu ht.1) (ihv ht.2.1))

/-- Any genuine positive-degree exterior fibre has the original-action local tensor model. -/
theorem exists_factorExteriorWordEquiv (n : ℕ) (f : Polynomial ℂ) (hf : f.Monic)
    (hdeg : f.natDegree=n) (hn : 0<n) :
    ∃ t : EvenTensorWord, t.Distinct ∧ t.support=(f.roots.toFinset : Set ℂ) ∧ t.weight=n ∧
      Nonempty (FactorExterior n f ≃ₗ⁅ℂ,BGG.Current⁆ t.exteriorModule) := by
  obtain ⟨t,ht,hs,hp,hw⟩ := exists_of_monic f hf (by omega)
  refine ⟨t,ht,hs,hw.trans hdeg,?_⟩
  have e := factorExteriorWordEquiv t ht
  rw [hp,hw,hdeg] at e
  exact ⟨e⟩

end KhanSL2.SymmetricFamily
