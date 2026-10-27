module

public import KhanSL2.BGG.FreeCEAugmentation
public import KhanSL2.BGG.PolynomialKoszul
public import Mathlib.Tactic.NoncommRing

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The finite operator identities underlying the free CE square-zero proof. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.BGG.FreeCE

open PositiveCE FiniteExterior

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The exterior color brackets are the brackets of the actual positive-current Lie algebra. -/
theorem lieGenerator_bracket (m n : Mode) :
    ⁅lieGenerator m, lieGenerator n⁆ =
      ∑ a : Fin 3, KhanSL2.epsilon a m.color n.color • lieGenerator (mergeMode m n a) := by
  apply Subtype.ext
  change ⁅mode (m.index+1) (MatrixSL2.color m.color),
    mode (n.index+1) (MatrixSL2.color n.color)⁆ =
      ∑ a : Fin 3, KhanSL2.epsilon a m.color n.color •
        mode ((mergeMode m n a).index+1) (MatrixSL2.color a)
  rw [mode_lie, MatrixSL2.color_bracket, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul, ← epsilon_rotate a m.color n.color]
  have hi : (m.index+1)+(n.index+1)=(mergeMode m n a).index+1 := by
    simp only [mergeMode]
    omega
  rw [hi]

/-- The actual associative commutator realizes exactly the CE structure constants. -/
theorem ueGenerator_commutator (m n : Mode) :
    ueGenerator m * ueGenerator n - ueGenerator n * ueGenerator m =
      ∑ a : Fin 3, KhanSL2.epsilon a m.color n.color • ueGenerator (mergeMode m n a) := by
  change ⁅UniversalEnvelopingAlgebra.ι ℂ (lieGenerator m),
    UniversalEnvelopingAlgebra.ι ℂ (lieGenerator n)⁆ = _
  rw [← LieHom.map_lie, lieGenerator_bracket, map_sum]
  simp only [map_smul, ueGenerator]

/-- A contraction commutes with an even pair of contractions. -/
theorem contract_contract_pair (p m n : Mode) (ω : Cochain) :
    contract p (contract n (contract m ω)) = contract n (contract m (contract p ω)) := by
  rw [PolynomialKoszul.contracts_anticomm p n,
    PolynomialKoszul.contracts_anticomm p m, map_neg, neg_neg]

/-- Contracting a bracket-boundary summand selects its created output mode. -/
theorem contract_boundaryTerm (p m n : Mode) (a : Fin 3) (ω : Cochain) :
    contract p (boundaryTerm m n a ω) + boundaryTerm m n a (contract p ω) =
      if p = mergeMode m n a then contract n (contract m ω) else 0 := by
  simp only [boundaryTerm_apply]
  have hc (v : Cochain) : contract p (FiniteExterior.generator (mergeMode m n a) * v) =
      (if p=mergeMode m n a then v else 0) -
        FiniteExterior.generator (mergeMode m n a) * contract p v :=
    contraction_generator_wedge PositiveCE.Mode.code PositiveCE.Mode.code_injective p (mergeMode m n a) v
  rw [hc, contract_contract_pair]
  abel

/-- Tensor one bracket summand over the actual enveloping coefficient module. -/
def bracketTerm (m n : Mode) (a : Fin 3) : Module.End PositiveEnveloping Chain :=
  Induced.tensorLift ((TensorProduct.mk ℂ PositiveEnveloping Cochain 1).comp (boundaryTerm m n a))

@[simp] theorem bracketTerm_tmul (m n : Mode) (a : Fin 3)
    (u : PositiveEnveloping) (ω : Cochain) :
    bracketTerm m n a (u ⊗ₜ[ℂ] ω) = u ⊗ₜ[ℂ] boundaryTerm m n a ω := by
  rw [bracketTerm, Induced.tensorLift_tmul]
  change (u * 1) ⊗ₜ[ℂ] boundaryTerm m n a ω = _
  rw [mul_one]

/-- The mixed anticommutator is precisely the coefficient-bracket correction. -/
theorem actionTerm_bracketTerm (p m n : Mode) (a : Fin 3)
    (u : PositiveEnveloping) (ω : Cochain) :
    actionTerm p (bracketTerm m n a (u ⊗ₜ[ℂ] ω)) +
      bracketTerm m n a (actionTerm p (u ⊗ₜ[ℂ] ω)) =
      if p = mergeMode m n a then
        (u * ueGenerator p) ⊗ₜ[ℂ] contract n (contract m ω) else 0 := by
  simp only [actionTerm_tmul, bracketTerm_tmul]
  rw [← TensorProduct.tmul_add, contract_boundaryTerm]
  split_ifs <;> simp only [TensorProduct.tmul_zero]

/-- Two action summands contribute their associative coefficient commutator. -/
theorem actionTerm_anticommutator (m n : Mode) (u : PositiveEnveloping) (ω : Cochain) :
    actionTerm m (actionTerm n (u ⊗ₜ[ℂ] ω)) +
      actionTerm n (actionTerm m (u ⊗ₜ[ℂ] ω)) =
      (u * (ueGenerator n * ueGenerator m - ueGenerator m * ueGenerator n)) ⊗ₜ[ℂ]
        contract m (contract n ω) := by
  simp only [actionTerm_tmul]
  rw [PolynomialKoszul.contracts_anticomm n m, TensorProduct.tmul_neg,
    ← sub_eq_add_neg, ← TensorProduct.sub_tmul]
  congr 1
  noncomm_ring

end KhanSL2.BGG.FreeCE
