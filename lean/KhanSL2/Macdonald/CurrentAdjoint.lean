module

public import KhanSL2.Macdonald.CurrentAction
public import KhanSL2.Macdonald.DerivationFiniteSum

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Bilinear transpose of the actual adjoint current action. The lowering
operator has the coadjoint minus sign, independently of the Hermitian metric. -/
noncomputable section
open scoped BigOperators
namespace KhanSL2.Macdonald

/-- The coadjoint lowering vector field in the even coordinates. -/
def currentLower (m : ℕ) (a : Fin 3) : Derivation ℂ Poly Poly :=
  MvPolynomial.mkDerivation ℂ (fun i : Mode =>
    if m ≤ i.index then ∑ c : Fin 3,
      epsilon a i.color c • MvPolynomial.X (⟨i.index-m,c⟩ : Mode) else 0)

@[simp] theorem currentLower_X (m n : ℕ) (a b : Fin 3) :
    currentLower m a (MvPolynomial.X (⟨n,b⟩ : Mode)) =
      if m ≤ n then ∑ c : Fin 3, epsilon a b c • MvPolynomial.X (⟨n-m,c⟩ : Mode)
      else 0 := MvPolynomial.mkDerivation_X _ _ _

private def finiteRaise (N m : ℕ) (a : Fin 3) : Derivation ℂ Poly Poly :=
  ∑ n ∈ Finset.range N, ∑ b : Fin 3, ∑ c : Fin 3,
    epsilon a b c • ((MvPolynomial.X (⟨m+n,c⟩ : Mode) : Poly) • MvPolynomial.pderiv (⟨n,b⟩ : Mode))

private def finiteTranspose (N m : ℕ) (a : Fin 3) : Derivation ℂ Poly Poly :=
  ∑ n ∈ Finset.range N, ∑ b : Fin 3, ∑ c : Fin 3,
    epsilon a b c • ((MvPolynomial.X (⟨n,b⟩ : Mode) : Poly) • MvPolynomial.pderiv (⟨m+n,c⟩ : Mode))

private theorem finiteRaise_X (N m n : ℕ) (a b : Fin 3) (hn : n < N) :
    finiteRaise N m a (MvPolynomial.X (⟨n,b⟩ : Mode)) =
      currentAction (BGG.mode m (MatrixSL2.color a)) (MvPolynomial.X (⟨n,b⟩ : Mode)) := by
  classical
  rw [currentAction_mode_X]
  simp [finiteRaise, _root_.sum_apply, MvPolynomial.pderiv_X, Pi.single_apply,
    BGG.PositiveCE.Mode.mk.injEq, ite_and, hn, smul_eq_mul]

private theorem finiteTranspose_X (N m n : ℕ) (a b : Fin 3) (hn : n < N) :
    finiteTranspose N m a (MvPolynomial.X (⟨n,b⟩ : Mode)) =
      -currentLower m a (MvPolynomial.X (⟨n,b⟩ : Mode)) := by
  classical
  rw [currentLower_X]
  simp only [finiteTranspose, _root_.sum_apply, Derivation.smul_apply,
    MvPolynomial.pderiv_X, Pi.single_apply, BGG.PositiveCE.Mode.mk.injEq, ite_and]
  by_cases hm : m ≤ n
  · rw [if_pos hm]
    have he (i : ℕ) : n = m+i ↔ i = n-m := by omega
    simp only [he, smul_ite, smul_zero, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_range, show n-m < N by omega, if_true]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [epsilon_swap_right a c b, neg_smul]
  · rw [if_neg hm, neg_zero]
    have he (i : ℕ) : ¬n = m+i := by omega
    simp [he]

private theorem finiteRaise_transpose (N m : ℕ) (a : Fin 3) (p q : Poly) :
    polynomialPairing (finiteRaise N m a p) q =
      polynomialPairing p (finiteTranspose N m a q) := by
  simp only [finiteRaise, finiteTranspose, _root_.sum_apply, Derivation.smul_apply,
    smul_eq_mul, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    polynomialPairing_vectorField]

/-- The actual raising action is the negative transpose of the coadjoint
lowering action under the factorial-normalized restricted-dual pairing. -/
theorem currentAction_pairing (m : ℕ) (a : Fin 3) (p q : Poly) :
    polynomialPairing (currentAction (BGG.mode m (MatrixSL2.color a)) p) q =
      -polynomialPairing p (currentLower m a q) := by
  classical
  let N := (p.vars ∪ q.vars).sup BGG.PositiveCE.Mode.index + 1
  have hp : currentAction (BGG.mode m (MatrixSL2.color a)) p = finiteRaise N m a p := by
    apply MvPolynomial.derivation_eq_of_forall_mem_vars
    rintro ⟨n,b⟩ hi
    apply (finiteRaise_X N m n a b _).symm
    exact Nat.lt_succ_of_le (Finset.le_sup (f := BGG.PositiveCE.Mode.index)
      (Finset.mem_union_left _ hi))
  have hq : finiteTranspose N m a q = (-currentLower m a) q := by
    apply MvPolynomial.derivation_eq_of_forall_mem_vars
    rintro ⟨n,b⟩ hi
    apply finiteTranspose_X N m n a b
    exact Nat.lt_succ_of_le (Finset.le_sup (f := BGG.PositiveCE.Mode.index)
      (Finset.mem_union_right _ hi))
  rw [hp, finiteRaise_transpose, hq, Derivation.neg_apply, map_neg]

end KhanSL2.Macdonald
