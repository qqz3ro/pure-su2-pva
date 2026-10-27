module

public import KhanSL2.Factorization.EvenWeightBoundsDecomposition
public import KhanSL2.Factorization.EvenWeightBoundsInheritance

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped DirectSum
namespace KhanSL2.Factorization.EvenWeightBounds
open BGG

theorem cartan_standard (n : ℕ) : cartan (TauCeti.Sl2Std ℂ n) = TauCeti.Sl2Std.diag ℂ n := by
  apply LinearMap.ext
  intro v
  change ⁅MatrixSL2.h,v⁆ = _
  rw [matrix_h_eq_standard,TauCeti.Sl2Std.lie_slFinTwoBasis_two]

theorem coefficient_top_eigenspace_bot (q m : ℕ) (hqm : q < m) :
    (cartan (Coefficient q)).eigenspace (2*(m : ℂ)) = ⊥ := by
  rw [cartan_standard]
  apply TauCeti.Sl2Std.eigenspace_diag_eq_bot
  intro i hi
  have hz : 2*(m : ℤ) = 2*(q : ℤ)-2*(i.val : ℤ) := by exact_mod_cast hi
  omega

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule G V] [LieModule ℂ G V] [FiniteDimensional ℂ V]

/-- An actual nonzero top eigenvector forces a copy of the top standard module
inside the finite module; no multiplicity or irreducibility hypothesis is added. -/
theorem exists_top_embedding_of_eigenvector (m : ℕ)
    (hp : aeval (cartan V) (evenBoundPolynomial m) = 0)
    (v : V) (hv : v ≠ 0) (hweight : cartan V v = (2*(m : ℂ)) • v) :
    ∃ j : Coefficient m →ₗ⁅ℂ,G⁆ V, Function.Injective j := by
  classical
  obtain ⟨k,q,hq,⟨e⟩⟩ := exists_bounded_lieModuleEquiv m hp
  have hcoord : ∃ i : Fin k, e v i ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    apply e.injective
    ext i
    simpa only [map_zero,DFinsupp.zero_apply] using h i
  obtain ⟨i,hi⟩ := hcoord
  let p := DirectSum.lieModuleComponent ℂ (Fin k) G (fun i => Coefficient (q i)) i
  have hweight' : cartan (Coefficient (q i)) (e v i) = (2*(m : ℂ)) • e v i := by
    change ⁅MatrixSL2.h,p (e v)⁆ = (2*(m : ℂ)) • p (e v)
    rw [← p.map_lie]
    have he : e ⁅MatrixSL2.h,v⁆ = ⁅MatrixSL2.h,e v⁆ := e.toLieModuleHom.map_lie _ _
    rw [← he]
    change p (e (cartan V v)) = _
    rw [hweight,map_smul,map_smul]
  have hqi : q i = m := by
    by_contra hne
    have hlt : q i < m := lt_of_le_of_ne (hq i) hne
    have hmem : e v i ∈ (cartan (Coefficient (q i))).eigenspace (2*(m : ℂ)) :=
      Module.End.mem_eigenspace_iff.mpr hweight'
    rw [coefficient_top_eigenspace_bot (q i) m hlt] at hmem
    exact hi hmem
  let j : Coefficient (q i) →ₗ⁅ℂ,G⁆ V := e.symm.toLieModuleHom.comp
    (DirectSum.lieModuleOf ℂ (Fin k) G (fun i => Coefficient (q i)) i)
  have hj : Function.LeftInverse (fun y => e y i) j := by
    intro x
    change e (e.symm (DirectSum.of (fun i => Coefficient (q i)) i x)) i = x
    rw [e.apply_symm_apply]
    simp
  rw [← hqi]
  exact ⟨j,hj.injective⟩

/-- A one-dimensional top eigenspace in particular supplies a genuine top irreducible summand. -/
theorem exists_top_embedding (m : ℕ)
    (hp : aeval (cartan V) (evenBoundPolynomial m) = 0)
    (htop : Module.finrank ℂ ((cartan V).eigenspace (2*(m : ℂ))) = 1) :
    ∃ j : Coefficient m →ₗ⁅ℂ,G⁆ V, Function.Injective j := by
  obtain ⟨v,hv⟩ := (Module.finrank_pos_iff_exists_ne_zero
    (R:=ℂ) (M:=(cartan V).eigenspace (2*(m : ℂ)))).mp (by rw [htop]; decide)
  apply exists_top_embedding_of_eigenvector m hp v.val
  · intro h
    exact hv (Subtype.ext h)
  · exact Module.End.mem_eigenspace_iff.mp v.property

end KhanSL2.Factorization.EvenWeightBounds

