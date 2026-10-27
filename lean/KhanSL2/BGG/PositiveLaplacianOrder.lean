module

public import KhanSL2.BGG.PositiveLaplacianBasics
public import KhanSL2.BGG.ExteriorSecondOrderCalculus

@[expose] public section

/-! The actual positive-current Laplacian is a second-order exterior operator. -/
noncomputable section
open scoped BigOperators
open KhanSL2.FiniteExterior
namespace KhanSL2.BGG.PositiveCE

/-- A finite algebraic approximation, used only with cutoffs containing the input supports. -/
def finiteLaplacian (S : Finset Mode) : Module.End ℂ Cochain :=
  d.comp (finiteBoundary S) + (finiteBoundary S).comp d

@[simp] theorem finiteLaplacian_apply (S : Finset Mode) (u : Cochain) :
    finiteLaplacian S u = d (finiteBoundary S u) + finiteBoundary S (d u) := rfl

private theorem secondOrder_sum {ι : Type*} (S : Finset ι) (f : ι → Module.End ℂ Cochain)
    (hf : ∀ i∈S, HasSecondOrderLeibniz (f i)) : HasSecondOrderLeibniz (∑ i∈S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro a u v
    simp [generatorDefect_apply]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (by simp)).add (ih (fun j hj => hf j (by simp [hj])))

/-- Every finite bracket summand has second-order supercommutator with the actual d. -/
theorem finiteLaplacian_secondOrder (S : Finset Mode) :
    HasSecondOrderLeibniz (finiteLaplacian S) := by
  have hD : HasOddLeibniz d := d_mul
  have hC (m : Mode) : HasOddLeibniz (contract m) :=
    contraction_wedge Mode.code Mode.code_injective m
  have hterm (m n : Mode) (a : Fin 3) :
      HasSecondOrderLeibniz (d.comp (boundaryTerm m n a) + (boundaryTerm m n a).comp d) :=
    secondOrder_odd_boundary_summand d (contract n) (contract m)
      hD (hC n) (hC m) d_parity (contract_parity n) (contract_parity m) (mergeMode m n a)
  have hexpand : finiteLaplacian S = (-(1/2 : ℂ)) •
      ∑ m∈S, ∑ n∈S, ∑ a : Fin 3, epsilon a m.color n.color •
        (d.comp (boundaryTerm m n a) + (boundaryTerm m n a).comp d) := by
    apply LinearMap.ext
    intro u
    simp only [finiteLaplacian_apply, finiteBoundary, LinearMap.smul_apply,
      LinearMap.sum_apply, LinearMap.add_apply, LinearMap.comp_apply,
      map_smul, map_sum, smul_add, Finset.sum_add_distrib]
  rw [hexpand]
  apply HasSecondOrderLeibniz.smul
  apply secondOrder_sum
  intro m _
  apply secondOrder_sum
  intro n _
  apply secondOrder_sum
  intro a _
  exact (hterm m n a).smul _

/-- A sufficiently large finite formula agrees with the actual Laplacian on the given input. -/
theorem finiteLaplacian_eq (S : Finset Mode) (u : Cochain)
    (hu : supportModes u ⊆ S) (hdu : supportModes (d u) ⊆ S) :
    finiteLaplacian S u = laplacian u := by
  rw [finiteLaplacian_apply, finiteBoundary_eq S u hu,
    finiteBoundary_eq S (d u) hdu, laplacian_apply]

/-- The second-order Leibniz property follows from the finite boundary formula,
    the odd Leibniz rules, and finite support. -/
theorem laplacian_secondOrder : HasSecondOrderLeibniz laplacian := by
  classical
  intro a u v
  let inputs : Finset Cochain :=
    {FiniteExterior.generator a * (u*v), FiniteExterior.generator a,
      u*v, FiniteExterior.generator a * u, u, FiniteExterior.generator a * v, v}
  let S : Finset Mode := inputs.biUnion fun w => supportModes w ∪ supportModes (d w)
  have heq (w : Cochain) (hw : w∈inputs) : finiteLaplacian S w = laplacian w := by
    apply finiteLaplacian_eq
    · intro m hm
      exact Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_union_left _ hm⟩
    · intro m hm
      exact Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_union_right _ hm⟩
  have h := finiteLaplacian_secondOrder S a u v
  simp only [generatorDefect_apply] at h ⊢
  rw [heq _ (by simp [inputs]), heq _ (by simp [inputs]),
    heq _ (by simp [inputs]), heq _ (by simp [inputs]),
    heq _ (by simp [inputs]), heq _ (by simp [inputs]),
    heq _ (by simp [inputs])] at h
  exact h

end KhanSL2.BGG.PositiveCE
