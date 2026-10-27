module

public import KhanSL2.Factorization.ResultantChartClosedPoints
public import KhanSL2.Factorization.QuasiIsoBaseChange
public import KhanSL2.Factorization.TensorCoefficientEquiv

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace KhanSL2.Factorization.ChartBridge
open NonnegativeCone

variable {A : Type*} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
variable {C D : ChainComplex (ModuleCat A) ℕ}

/-- To prove a finite-projective comparison over a finite-type complex algebra,
it suffices to prove its actual scalar extension at every complex-valued point.
The residue-field identification and tensor transport are proved here. -/
theorem quasiIso_of_complex_points (φ : C ⟶ D)
    [∀ n, Module.Finite A (C.X n)] [∀ n, Module.Finite A (D.X n)]
    [∀ n, Module.Projective A (C.X n)] [∀ n, Module.Projective A (D.X n)]
    (h : ∀ χ : A →ₐ[ℂ] ℂ, let := χ.toRingHom.toAlgebra; QuasiIso (scalarMap ℂ φ)) :
    QuasiIso φ := by
  let : ∀ n, Module.Finite A ((complex φ).X n) := fun n => by
    change Module.Finite A (Term C D n)
    infer_instance
  let : ∀ n, Module.Projective A ((complex φ).X n) := fun n => by
    change Module.Projective A (Term C D n)
    infer_instance
  have hf (p : Ideal A) [p.IsMaximal] :
      Function.Surjective (((complex φ).d 1 0).hom.lTensor p.ResidueField) ∧
        ∀ n, Function.Exact (((complex φ).d (n+2) (n+1)).hom.lTensor p.ResidueField)
          (((complex φ).d (n+1) n).hom.lTensor p.ResidueField) := by
    let := closedPointAlgebra p
    let : QuasiIso (scalarMap ℂ φ) := h (closedPoint p)
    have hc := acyclic_of_quasiIso (scalarMap ℂ φ)
    have hscalar : (scalarComplex ℂ (complex φ)).Acyclic :=
      fun n => (hc n).of_iso (scalarConeIso ℂ φ).symm
    have hp := (scalarComplex_acyclic_iff ℂ (complex φ)).mp hscalar
    let e := (residuePointEquiv p).toLinearEquiv
    refine ⟨(TensorCoefficientEquiv.surjective_iff e ((complex φ).d 1 0).hom).mpr hp.1,fun n => ?_⟩
    exact (TensorCoefficientEquiv.exact_iff e ((complex φ).d (n+2) (n+1)).hom
      ((complex φ).d (n+1) n).hom).mpr (hp.2 n)
  apply quasiIso_of_acyclic
  apply ComplexExactness.acyclic_of_maximal_fibres
  · intro p hp
    let := hp
    exact (hf p).1
  · intro n p hp
    let := hp
    exact (hf p).2 n

end KhanSL2.Factorization.ChartBridge
