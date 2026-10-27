module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

@[expose] public section
noncomputable section
open TensorProduct
namespace KhanSL2.Factorization.FibreExactness

variable {R : Type*} [CommRing R]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Residue fibres at maximal ideals detect a finite module. -/
theorem subsingleton_of_maximal_fibres [Module.Finite R M]
    (h : ∀ (p : Ideal R) [p.IsMaximal], Subsingleton (p.ResidueField ⊗[R] M)) :
    Subsingleton M := by
  by_contra hn
  let : Nontrivial M := not_subsingleton_iff_nontrivial.mp hn
  obtain ⟨p,hp⟩ := Module.nonempty_support_of_nontrivial (R := R) (M := M)
  have ha : Module.annihilator R M ≠ ⊤ := by
    intro ht
    have hle := (Module.mem_support_iff_of_finite.mp hp)
    rw [ht] at hle
    exact p.isPrime.ne_top (top_le_iff.mp hle)
  obtain ⟨q,hq,hqa⟩ := Ideal.exists_le_maximal (Module.annihilator R M) ha
  let := hq
  have hs : (⟨q,inferInstance⟩ : PrimeSpectrum R) ∈ Module.support R M :=
    Module.mem_support_iff_of_finite.mpr hqa
  have hnt := (Module.mem_support_iff_nontrivial_residueField_tensorProduct
    (M := M) ⟨q,inferInstance⟩).mp hs
  let := hnt
  let := h q
  exact false_of_nontrivial_of_subsingleton (q.ResidueField ⊗[R] M)

/-- Surjectivity on maximal residue fibres detects a map onto a finite module.
This is applied to bottom differentials, never to ordinary homology base change. -/
theorem surjective_of_maximal_fibres [Module.Finite R N] (f : M →ₗ[R] N)
    (h : ∀ (p : Ideal R) [p.IsMaximal], Function.Surjective (f.lTensor p.ResidueField)) :
    Function.Surjective f := by
  have hc : Subsingleton (N ⧸ LinearMap.range f) := by
    apply subsingleton_of_maximal_fibres (R := R)
    intro p hp
    let := hp
    apply (subsingleton_iff_forall_eq 0).mpr
    intro z
    obtain ⟨y,rfl⟩ := (LinearMap.range f).mkQ.lTensor_surjective p.ResidueField
      (Submodule.mkQ_surjective _) z
    obtain ⟨x,rfl⟩ := h p y
    rw [← LinearMap.comp_apply,← LinearMap.lTensor_comp]
    rw [(LinearMap.exact_map_mkQ_range f).linearMap_comp_eq_zero]
    simp only [LinearMap.lTensor_zero,LinearMap.zero_apply]
  exact LinearMap.range_eq_top.mp (Submodule.Quotient.subsingleton_iff.mp hc)

end KhanSL2.Factorization.FibreExactness
