module

public import KhanSL2.BGG.PositiveBoundaryAdjoint
public import KhanSL2.BGG.PositiveCEParity

@[expose] public section

/-! The concrete homology boundary is equivariant for the actual constant sl₂ action. -/
noncomputable section
open scoped BigOperators
open KhanSL2.FiniteExterior
namespace KhanSL2.BGG.PositiveCE

/-- A finite color-action formula, with all colors retained below the cutoff. -/
def finiteColorAction (N : ℕ) (a : Fin 3) : Module.End ℂ Cochain :=
  finiteDerivation Mode.code (fun m => colorAction a (FiniteExterior.generator m)) (modesBelow N)

theorem finiteColorAction_apply (N : ℕ) (a : Fin 3) (u : Cochain) :
    finiteColorAction N a u = ∑ i∈Finset.range N, ∑ b : Fin 3, ∑ c : Fin 3,
      epsilon a b c • (FiniteExterior.generator (⟨i,c⟩ : Mode) * contract (⟨i,b⟩ : Mode) u) := by
  rw [finiteColorAction, finiteDerivation_apply, sum_modesBelow]
  change (∑ i∈Finset.range N, ∑ b : Fin 3,
    colorAction a (FiniteExterior.generator (⟨i,b⟩ : Mode)) * contract (⟨i,b⟩ : Mode) u) = _
  simp only [colorAction_generator, Finset.sum_mul, smul_mul_assoc]

@[simp] theorem finiteColorAction_one (N : ℕ) (a : Fin 3) : finiteColorAction N a 1 = 0 := by
  simp [finiteColorAction_apply]

theorem finiteColorAction_mul (N : ℕ) (a : Fin 3) (u v : Cochain) :
    finiteColorAction N a (u*v) = finiteColorAction N a u*v + u*finiteColorAction N a v := by
  apply finiteDerivation_wedge_twist Mode.code Mode.code_injective
  intro m
  have hm : parityLinear (colorAction a (FiniteExterior.generator m)) =
      -colorAction a (FiniteExterior.generator m) := by
    rw [← colorAction_parity, parity_generator, map_neg]
  exact (wedge_comm_of_parity_odd Mode.code Mode.code_injective _ hm u).symm

theorem finiteColorAction_generator (N : ℕ) (a : Fin 3) (m : Mode) (hm : m.index < N) :
    finiteColorAction N a (FiniteExterior.generator m) = colorAction a (FiniteExterior.generator m) := by
  rw [finiteColorAction, finiteDerivation_apply]
  change (∑ n∈modesBelow N, colorAction a (FiniteExterior.generator n) *
    contract n (FiniteExterior.generator m)) = _
  simp only [contract_generator, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    mem_modesBelow, hm, ite_true]

/-- The finite formula agrees with the given color action on any supported input. -/
theorem finiteColorAction_eq (N : ℕ) (a : Fin 3) (u : Cochain)
    (hu : supportModes u ⊆ modesBelow N) : finiteColorAction N a u = colorAction a u := by
  have hmono (s : Finset Mode) (hs : s ⊆ modesBelow N) :
      finiteColorAction N a (monomial s) = colorAction a (monomial s) := by
    induction s using Finset.induction_on with
    | empty =>
      change finiteColorAction N a 1 = colorAction a 1
      rw [finiteColorAction_one, colorAction_one]
    | @insert m s hm ih =>
      rw [monomial_insert Mode.code m s hm, map_smul, map_smul]
      congr 1
      change finiteColorAction N a (FiniteExterior.generator m * monomial s) =
        colorAction a (FiniteExterior.generator m * monomial s)
      rw [finiteColorAction_mul, colorAction_mul, finiteColorAction_generator N a m
        ((mem_modesBelow N m).mp (hs (by simp))),
        ih (fun n hn => hs (Finset.mem_insert_of_mem hn))]
  rw [eq_sum_support u]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro s hs
  rw [hmono s ((subset_supportModes hs).trans hu)]

/-- The finite color matrix is skew-transpose for the exterior coefficient pairing. -/
theorem finiteColorAction_pairing (N : ℕ) (a : Fin 3) (u v : Cochain) :
    coefficientPairing (finiteColorAction N a u) v =
      -coefficientPairing u (finiteColorAction N a v) := by
  have hcontract (m : Mode) (w : Cochain) :
      coefficientPairing (contract m u) w = coefficientPairing u (FiniteExterior.generator m * w) :=
    coefficientPairing_contraction (α := Mode) m u w
  simp only [finiteColorAction_apply, map_sum, LinearMap.sum_apply,
    map_smul, LinearMap.smul_apply, coefficientPairing_generator_mul (α := Mode),
    hcontract]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  calc
    (∑ c : Fin 3, ∑ b : Fin 3, epsilon a b c •
      coefficientPairing u (FiniteExterior.generator (⟨i,b⟩ : Mode) *
        contract (⟨i,c⟩ : Mode) v)) =
      ∑ c : Fin 3, ∑ b : Fin 3, (-epsilon a c b) •
      coefficientPairing u (FiniteExterior.generator (⟨i,b⟩ : Mode) *
        contract (⟨i,c⟩ : Mode) v) := by
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro b _
          rw [epsilon_swap_right a b c]
    _ = _ := by simp only [neg_smul, Finset.sum_neg_distrib]

/-- Every genuine color action is skew-adjoint for the algebraic coefficient pairing. -/
theorem colorAction_pairing (a : Fin 3) (u v : Cochain) :
    coefficientPairing (colorAction a u) v = -coefficientPairing u (colorAction a v) := by
  let S := supportModes u ∪ supportModes v
  let N := S.sup Mode.index + 1
  have hbound (m : Mode) (hm : m∈S) : m∈modesBelow N := by
    rw [mem_modesBelow]
    have h := Finset.le_sup (f := Mode.index) hm
    change m.index < S.sup Mode.index + 1
    omega
  have hu : supportModes u ⊆ modesBelow N :=
    fun m hm => hbound m (Finset.mem_union_left _ hm)
  have hv : supportModes v ⊆ modesBelow N :=
    fun m hm => hbound m (Finset.mem_union_right _ hm)
  rw [← finiteColorAction_eq N a u hu, ← finiteColorAction_eq N a v hv,
    finiteColorAction_pairing]

/-- Adjointness transfers the proved CE equivariance to the actual homology boundary. -/
theorem boundary_colorAction (a : Fin 3) (u : Cochain) :
    boundary (colorAction a u) = colorAction a (boundary u) := by
  apply sub_eq_zero.mp
  apply coefficientPairing_left_nondegenerate
  intro v
  simp only [map_sub, LinearMap.sub_apply, boundary_pairing, colorAction_pairing,
    d_colorAction, sub_self]

/-- Boundary equivariance for every actual matrix sl₂ element. -/
theorem boundary_positiveAction (x : G) (u : Cochain) :
    boundary (ColorRoot.positiveAction x u) = ColorRoot.positiveAction x (boundary u) := by
  rw [← MatrixSL2.color_decomposition x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    ColorRoot.positiveAction_color, boundary_colorAction]

/-- The proved boundary as an actual morphism of sl₂ representations. -/
def boundaryLie : Cochain →ₗ⁅ℂ,G⁆ Cochain :=
  { boundary with map_lie' := fun {x u} => boundary_positiveAction x u }

@[simp] theorem boundaryLie_apply (u : Cochain) : boundaryLie u = boundary u := rfl

end KhanSL2.BGG.PositiveCE
