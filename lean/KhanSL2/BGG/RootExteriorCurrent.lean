module

public import KhanSL2.BGG.CurrentBasis
public import KhanSL2.BGG.RootExterior

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The degree-one root exterior generators are the actual positive current Lie algebra. -/

noncomputable section
namespace KhanSL2.BGG

/-- The support half-weight uses the same normalization as the actual Cartan bracket. -/
theorem rootWeight_eq_twice_halfWeight (a : Fin 3) :
    rootWeight a = 2 * (rootHalfWeight a : ℂ) := by
  fin_cases a <;> norm_num [rootWeight, rootHalfWeight]
/-- Embed an actual positive current by its root-mode coordinates. -/
def rootCurrentGenerator : positive →ₗ[ℂ] RootExterior :=
  positiveBasis.constr ℂ FiniteExterior.generator

@[simp] theorem rootCurrentGenerator_positiveBasis (n : ℕ) (a : Fin 3) :
    rootCurrentGenerator (positiveBasis (n, a)) = FiniteExterior.generator (n, a) := by
  exact positiveBasis.constr_basis ℂ _ (n, a)

@[simp] theorem rootCurrentGenerator_positiveMode_rootBasis (n : ℕ) (a : Fin 3) :
    rootCurrentGenerator (positiveMode n (rootBasis a)) = FiniteExterior.generator (n, a) := by
  rw [← positiveBasis_apply, rootCurrentGenerator_positiveBasis]

theorem rootGenerators_linearIndependent :
    LinearIndependent ℂ (FiniteExterior.generator : RootMode → RootExterior) := by
  rw [show (FiniteExterior.generator : RootMode → RootExterior) =
    (fun x => Finsupp.single {x} (1 : ℂ)) by funext x; rfl]
  have h := (Finsupp.basisSingleOne : Module.Basis (Finset RootMode) ℂ RootExterior).linearIndependent.comp
     (fun i : RootMode => ({i} : Finset RootMode)) Finset.singleton_injective
  simpa [FiniteExterior.generator, FiniteExterior.monomial, Function.comp_def] using h

theorem rootCurrentGenerator_injective : Function.Injective rootCurrentGenerator :=
  positiveBasis.injective_constr_of_linearIndependent rootGenerators_linearIndependent

end KhanSL2.BGG