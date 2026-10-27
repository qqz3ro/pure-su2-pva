module

public import KhanSL2.Factorization.NonnegativeConeBaseChange

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace KhanSL2.Factorization.NonnegativeCone

variable {R : Type*} [CommRing R]

/-- Exactness here is exactness of the tensor differential, before taking homology. -/
theorem scalarComplex_acyclic_iff (S : Type*) [CommRing S] [Algebra R S]
    (C : ChainComplex (ModuleCat R) ℕ) :
    (scalarComplex S C).Acyclic ↔
      Function.Surjective ((C.d 1 0).hom.lTensor S) ∧
        ∀ n, Function.Exact ((C.d (n+2) (n+1)).hom.lTensor S)
          ((C.d (n+1) n).hom.lTensor S) := by
  rw [ComplexExactness.acyclic_iff]
  simp only [scalarComplex_d,ModuleCat.hom_ofHom,LinearMap.baseChange_eq_lTensor]
  rfl

variable {C D : ChainComplex (ModuleCat R) ℕ} (φ : C ⟶ D)

/-- Appendix A.2: a quasi-isomorphism between nonnegative flat complexes survives
arbitrary scalar extension, including nonflat thickened fibres. -/
theorem quasiIso_scalarMap_of_flat
    [∀ n, Module.Flat R (C.X n)] [∀ n, Module.Flat R (D.X n)] [QuasiIso φ]
    (S : Type*) [CommRing S] [Algebra R S] : QuasiIso (scalarMap S φ) := by
  let : ∀ n, Module.Flat R ((complex φ).X n) := fun n => by
    change Module.Flat R (Term C D n)
    infer_instance
  have hcone := acyclic_of_quasiIso φ
  have hscalar : (scalarComplex S (complex φ)).Acyclic :=
    (scalarComplex_acyclic_iff S (complex φ)).mpr
      (ComplexExactness.lTensor_exact_of_acyclic (complex φ) hcone S)
  apply quasiIso_of_acyclic
  intro n
  exact (hscalar n).of_iso (scalarConeIso S φ)

/-- Derived residue-fibre detection for maps of nonnegative finite projective
complexes. The proof tensors the mapping cone; it never commutes homology with
a nonflat residue-field specialization. -/
theorem quasiIso_of_maximal_scalarMaps
    [∀ n, Module.Finite R (C.X n)] [∀ n, Module.Finite R (D.X n)]
    [∀ n, Module.Projective R (C.X n)] [∀ n, Module.Projective R (D.X n)]
    (h : ∀ (p : Ideal R) [p.IsMaximal], QuasiIso (scalarMap p.ResidueField φ)) : QuasiIso φ := by
  let : ∀ n, Module.Finite R ((complex φ).X n) := fun n => by
    change Module.Finite R (Term C D n)
    infer_instance
  let : ∀ n, Module.Projective R ((complex φ).X n) := fun n => by
    change Module.Projective R (Term C D n)
    infer_instance
  have hf (p : Ideal R) [p.IsMaximal] : (scalarComplex p.ResidueField (complex φ)).Acyclic := by
    let := h p
    have hc := acyclic_of_quasiIso (scalarMap p.ResidueField φ)
    intro n
    exact (hc n).of_iso (scalarConeIso p.ResidueField φ).symm
  apply quasiIso_of_acyclic
  apply ComplexExactness.acyclic_of_maximal_fibres
  · intro p hp
    let := hp
    exact ((scalarComplex_acyclic_iff p.ResidueField (complex φ)).mp (hf p)).1
  · intro n p hp
    let := hp
    exact ((scalarComplex_acyclic_iff p.ResidueField (complex φ)).mp (hf p)).2 n

end KhanSL2.Factorization.NonnegativeCone
