module

public import KhanSL2.Macdonald.StrongBridgeDifferential
public import KhanSL2.Macdonald.TensorPairing
public import KhanSL2.Macdonald.ChainModel

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The imported coboundary is transposed to the actual symmetric-coefficient
CE boundary under the bilinear factorial pairing. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.Macdonald

theorem currentLower_pairing (m : ℕ) (a : Fin 3) (p q : Poly) :
    polynomialPairing (currentLower m a p) q =
      -polynomialPairing p (currentAction (BGG.mode m (MatrixSL2.color a)) q) := by
  symm
  rw [polynomialPairing_symm p _, currentAction_pairing, neg_neg, polynomialPairing_symm]

/-- The odd creation operator and current coadjoint operator jointly transpose
 to the coefficient contribution to the true CE boundary. -/
theorem coefficientTerm_pairing (i : ℕ) (a : Fin 3) (u v : W) :
    pairing (psi a i * tensorPolynomialDerivation (currentLower (i+1) a) u) v =
      -pairing u (TensorProduct.map
        (currentAction (BGG.mode (i+1) (MatrixSL2.color a))).toLinearMap
        (BGG.PositiveCE.contract (⟨i,a⟩ : Mode)) v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u w hu hw => simp only [map_add, mul_add, LinearMap.add_apply, hu, hw, neg_add]
  | tmul p ω =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v w hv hw => simp only [map_add, hv, hw, neg_add]
    | tmul q η =>
      simp only [psi, tensorPolynomialDerivation_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, TensorProduct.map_tmul, pairing_tmul, currentLower_pairing,
        FiniteExterior.coefficientPairing_generator_mul, neg_mul]
      rfl

theorem exteriorTerm_pairing (u v : W) :
    pairing (tensorExteriorDifferential u) v =
      pairing u (TensorProduct.map LinearMap.id BGG.PositiveCE.boundary v) := by
  apply pairing_tensor_map LinearMap.id LinearMap.id BGG.PositiveCE.d BGG.PositiveCE.boundary
    (fun _ _ => rfl) _ u v
  intro ω η
  rw [FiniteExterior.coefficientPairing_symm, ← BGG.PositiveCE.boundary_pairing,
    FiniteExterior.coefficientPairing_symm]

/-- Actual CE boundary in a uniform finite physical-mode cutoff. -/
theorem chainBoundary_tmul_cutoff (N : ℕ) (p : Poly) (ω : Exterior)
    (hω : ∀ m ∈ FiniteExterior.supportModes ω, m.index < N) :
    chainBoundary (p ⊗ₜ[ℂ] ω) = p ⊗ₜ[ℂ] BGG.PositiveCE.boundary ω -
      ∑ i ∈ Finset.range N, ∑ a : Fin 3,
        currentAction (BGG.mode (i+1) (MatrixSL2.color a)) p ⊗ₜ[ℂ]
          BGG.PositiveCE.contract (⟨i,a⟩ : Mode) ω := by
  rw [chainBoundary_tmul (BGG.PositiveCE.modesBelow N) p ω
    (fun m hm => (BGG.PositiveCE.mem_modesBelow N m).mpr (hω m hm)),
    BGG.PositiveCE.sum_modesBelow]
  rfl

/-- Pointwise finite formula for the imported coefficient term. -/
theorem strongCoefficientDifferential_cutoff (u : StrongMacdonald.W) (N : ℕ)
    (hN : ∀ i, N ≤ i → strongCoefficientDifferentialFamily i u = 0) :
    strongModel (strongCoefficientDifferential u) =
      ∑ i ∈ Finset.range N, ∑ a : Fin 3,
        psi a i * tensorPolynomialDerivation (currentLower (i+1) a) (strongModel u) := by
  rw [strongCoefficientDifferential, StrongMacdonald.lsum_apply_of_bound _ N hN]
  simp only [map_sum, strongCoefficientDifferentialFamily, LinearMap.sum_apply,
    Module.End.mul_apply, StrongMacdonald.lmul_apply, strongModel_mul,
    strongModel_psiOf, strongModel_Rlow]

/-- The concrete bridge to the genuine symmetric-current CE differential. -/
theorem strongDbar_chainBoundary_pairing (u : StrongMacdonald.W) (v : W) :
    pairing (strongModel (StrongMacdonald.dbar u)) v = pairing (strongModel u) (chainBoundary v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | tmul p ω =>
    obtain ⟨N₀,hN₀⟩ := strongCoefficientDifferentialFamily_kills.evZero u
    let N := max N₀ ((FiniteExterior.supportModes ω).sup BGG.PositiveCE.Mode.index + 1)
    have hN : ∀ i, N ≤ i → strongCoefficientDifferentialFamily i u = 0 :=
      fun i hi => hN₀ i (le_trans (le_max_left _ _) hi)
    have hω : ∀ m ∈ FiniteExterior.supportModes ω, m.index < N := by
      intro m hm
      exact lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup hm)) (le_max_right _ _)
    rw [strongDbar_decomposition, LinearMap.add_apply, map_add,
      strongCoefficientDifferential_cutoff u N hN, strongModel_exteriorDifferential,
      chainBoundary_tmul_cutoff N p ω hω]
    simp only [map_sum, LinearMap.sum_apply, map_add, LinearMap.add_apply,
      map_sub, coefficientTerm_pairing, exteriorTerm_pairing, TensorProduct.map_tmul,
      LinearMap.id_apply, Finset.sum_neg_distrib]
    abel_nf
    simp only [Nat.add_comm]
    exact add_comm _ _

end KhanSL2.Macdonald
