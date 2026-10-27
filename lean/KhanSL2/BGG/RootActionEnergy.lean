module

public import KhanSL2.BGG.RootAction
public import KhanSL2.BGG.RootExteriorPieces
public import Mathlib.Data.Finset.Powerset
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The actual sl₂ action preserves both exterior degree and current energy. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.BGG

/-- The root-mode generators allowed at energy at most `N`. -/
def boundedRootModes (N : ℕ) : Finset RootMode :=
  Finset.range N ×ˢ (Finset.univ : Finset (Fin 3))

theorem rootSupport_subset_bounded (s : Finset RootMode) :
    s ⊆ boundedRootModes (rootMonomialEnergy s) := by
  intro i hi
  have hle : i.1 + 1 ≤ rootMonomialEnergy s :=
    Finset.single_le_sum (f := fun k : RootMode => k.1 + 1) (fun _ _ => Nat.zero_le _) hi
  simp only [boundedRootModes, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true]
  omega

theorem finite_rootMonomialEnergy_fibre (N : ℕ) :
    {s : Finset RootMode | rootMonomialEnergy s = N}.Finite := by
  apply (boundedRootModes N).powerset.finite_toSet.subset
  intro s hs
  change rootMonomialEnergy s = N at hs
  change s ∈ (boundedRootModes N).powerset
  rw [Finset.mem_powerset]
  simpa only [hs] using rootSupport_subset_bounded s
/-- Exterior vectors of one degree and one current energy. -/
def rootExteriorPiece (d N : ℕ) : Submodule ℂ RootExterior :=
  Finsupp.supported ℂ ℂ {s : Finset RootMode | s.card = d ∧ rootMonomialEnergy s = N}

instance finiteDimensional_rootExteriorPiece (d N : ℕ) :
    FiniteDimensional ℂ (rootExteriorPiece d N) := by
  have hfinite : {s : Finset RootMode | s.card = d ∧ rootMonomialEnergy s = N}.Finite :=
    (finite_rootMonomialEnergy_fibre N).subset (fun _ h => h.2)
  let := hfinite.fintype
  exact FiniteDimensional.of_injective
    (Finsupp.supportedEquivFinsupp (M := ℂ) (R := ℂ)
      {s : Finset RootMode | s.card = d ∧ rootMonomialEnergy s = N}).toLinearMap
    (Finsupp.supportedEquivFinsupp (M := ℂ) (R := ℂ)
      {s : Finset RootMode | s.card = d ∧ rootMonomialEnergy s = N}).injective
@[simp] theorem rootMonomial_mem_piece (s : Finset RootMode) (d N : ℕ) :
    FiniteExterior.monomial s ∈ rootExteriorPiece d N ↔
      s.card = d ∧ rootMonomialEnergy s = N := by
  simp [rootExteriorPiece, Finsupp.mem_supported, FiniteExterior.monomial]

theorem rootGenerator_mul_monomial_mem (i : RootMode) (s : Finset RootMode) :
    FiniteExterior.generator i * FiniteExterior.monomial s ∈
      rootExteriorPiece (s.card + 1) (rootMonomialEnergy s + (i.1 + 1)) := by
  change FiniteExterior.wedge FiniteExterior.GeneratorOrder.code
    (FiniteExterior.generator i) (FiniteExterior.monomial s) ∈ _
  rw [FiniteExterior.wedge_generator_monomial_eq]
  by_cases hi : i ∈ s
  · rw [if_pos hi]
    exact Submodule.zero_mem _
  · rw [if_neg hi]
    apply Submodule.smul_mem
    rw [rootMonomial_mem_piece]
    constructor
    · exact Finset.card_insert_of_notMem hi
    · simp [rootMonomialEnergy, Finset.sum_insert hi, add_comm]

/-- Replacing only the color of one factor preserves degree and energy. -/
theorem rootRecolor_mul_erase_mem (s : Finset RootMode) (i : RootMode) (hi : i ∈ s)
    (b : Fin 3) :
    FiniteExterior.generator (i.1, b) * FiniteExterior.monomial (s.erase i) ∈
      rootExteriorPiece s.card (rootMonomialEnergy s) := by
  have hc : (s.erase i).card + 1 = s.card := Finset.card_erase_add_one hi
  have he : rootMonomialEnergy (s.erase i) + (i.1 + 1) = rootMonomialEnergy s :=
    Finset.sum_erase_add _ _ hi
  simpa only [hc, he] using rootGenerator_mul_monomial_mem (i.1, b) (s.erase i)

/-- Each individual monomial stays in its degree-energy piece under constants. -/
theorem rootExteriorAction_monomial_mem (x : G) (s : Finset RootMode) :
    rootExteriorAction x (FiniteExterior.monomial s) ∈
      rootExteriorPiece s.card (rootMonomialEnergy s) := by
  change FiniteExterior.extendDerivation FiniteExterior.GeneratorOrder.code
    (fun i => FiniteExterior.generatorLinear (rootModeAction x (Finsupp.single i 1)))
    (FiniteExterior.monomial s) ∈ _
  rw [FiniteExterior.extendDerivation_monomial]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  rw [← rootExteriorAction_generator, rootExteriorAction_generator_eq_sum]
  simp only [FiniteExterior.wedge, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  apply Submodule.sum_mem
  intro b _
  apply Submodule.smul_mem
  exact rootRecolor_mul_erase_mem s i hi b

/-- The action preserves every whole degree-energy subspace. -/
theorem rootExteriorAction_mem_piece (x : G) {d N : ℕ} {u : RootExterior}
    (hu : u ∈ rootExteriorPiece d N) : rootExteriorAction x u ∈ rootExteriorPiece d N := by
  have heq : u = ∑ s ∈ u.support, u s • FiniteExterior.monomial s := by
    simpa only [Finsupp.sum, FiniteExterior.monomial, Finsupp.smul_single,
      smul_eq_mul, mul_one] using (Finsupp.sum_single u).symm
  rw [heq, map_sum]
  apply Submodule.sum_mem
  intro s hs
  rw [map_smul]
  apply Submodule.smul_mem
  have h := hu hs
  simpa only [h.1, h.2] using rootExteriorAction_monomial_mem x s

/-- The fixed degree-energy component is a genuine representation of actual sl₂. -/
def rootExteriorLiePiece (d N : ℕ) : LieSubmodule ℂ G RootExterior :=
  { rootExteriorPiece d N with
    lie_mem := fun {x _u} hu => rootExteriorAction_mem_piece x hu }

instance finiteDimensional_rootExteriorLiePiece (d N : ℕ) :
    FiniteDimensional ℂ (rootExteriorLiePiece d N) :=
  inferInstanceAs (FiniteDimensional ℂ (rootExteriorPiece d N))

end KhanSL2.BGG