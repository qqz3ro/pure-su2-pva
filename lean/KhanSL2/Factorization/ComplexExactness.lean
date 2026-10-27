module

public import KhanSL2.Factorization.FibreComplex
public import KhanSL2.Factorization.FlatAcyclic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

@[expose] public section
noncomputable section
open CategoryTheory
namespace KhanSL2.Factorization.ComplexExactness

variable {R : Type*} [CommRing R]

/-- Concrete exactness criterion for a nonnegative complex of modules. -/
theorem acyclic_iff (C : ChainComplex (ModuleCat R) ℕ) :
    C.Acyclic ↔ Function.Surjective (C.d 1 0).hom ∧
      ∀ n, Function.Exact (C.d (n+2) (n+1)).hom (C.d (n+1) n).hom := by
  have hzero : C.d 0 0 = 0 := C.shape _ _ (by simp)
  constructor
  · intro hC
    constructor
    · have he := (C.exactAt_iff' 1 0 0 (by simp) (by simp)).mp (hC 0)
      rw [CategoryTheory.ShortComplex.moduleCat_exact_iff] at he
      intro x
      exact he x (by change (C.d 0 0) x = 0; rw [hzero]; rfl)
    · intro n
      have he := (C.exactAt_iff' (n+2) (n+1) n (by simp) (by simp)).mp (hC (n+1))
      exact (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp he
  · rintro ⟨h₀,h⟩ n
    cases n with
    | zero =>
      apply (C.exactAt_iff' 1 0 0 (by simp) (by simp)).mpr
      rw [CategoryTheory.ShortComplex.moduleCat_exact_iff]
      intro x _
      exact h₀ x
    | succ n =>
      apply (C.exactAt_iff' (n+2) (n+1) n (by simp) (by simp)).mpr
      exact (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (h n)

theorem differential_square (C : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    (C.d (n+1) n).hom.comp (C.d (n+2) (n+1)).hom = 0 :=
  congrArg ModuleCat.Hom.hom (C.d_comp_d (n+2) (n+1) n)

/-- Residue-fibre detection stated for actual chain complexes, ready to apply
to a mapping cone of finite projective complexes. -/
theorem acyclic_of_maximal_fibres (C : ChainComplex (ModuleCat R) ℕ)
    [∀ n, Module.Finite R (C.X n)] [∀ n, Module.Projective R (C.X n)]
    (h₀ : ∀ (p : Ideal R) [p.IsMaximal],
      Function.Surjective ((C.d 1 0).hom.lTensor p.ResidueField))
    (h : ∀ n (p : Ideal R) [p.IsMaximal],
      Function.Exact ((C.d (n+2) (n+1)).hom.lTensor p.ResidueField)
        ((C.d (n+1) n).hom.lTensor p.ResidueField)) : C.Acyclic :=
  (acyclic_iff C).mpr (FibreExactness.exact_of_maximal_fibres (fun n => C.X n)
    (fun n => (C.d (n+1) n).hom) (differential_square C) h₀ h)

/-- Base-changing differentials of an acyclic flat complex is exact, including
specialization to nonflat or nonreduced coefficient algebras. -/
theorem lTensor_exact_of_acyclic (C : ChainComplex (ModuleCat R) ℕ)
    [∀ n, Module.Flat R (C.X n)] (hC : C.Acyclic)
    (S : Type*) [AddCommGroup S] [Module R S] :
    Function.Surjective ((C.d 1 0).hom.lTensor S) ∧
      ∀ n, Function.Exact ((C.d (n+2) (n+1)).hom.lTensor S)
        ((C.d (n+1) n).hom.lTensor S) :=
  FlatAcyclic.lTensor_exact (fun n => C.X n) (fun n => (C.d (n+1) n).hom)
    ((acyclic_iff C).mp hC).1 ((acyclic_iff C).mp hC).2 S

end KhanSL2.Factorization.ComplexExactness
