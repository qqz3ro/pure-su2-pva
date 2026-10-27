module

public import KhanSL2.CohomologyGrading
public import KhanSL2.Injectivity.FinitePairing
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# Finite chains and graded transposes

Chains are finite linear combinations of exterior monomials, exactly like
cochains; the two are paired by the coefficient pairing. Every graded piece
of monomials is a finite set, so a homogeneous operator on cochains has a
transpose on chains with the same finiteness. Identities between homogeneous
operators transpose because the pairing separates chains.
-/

noncomputable section

namespace KhanSL2

open FiniteExterior

/-- Finite chains. Definitionally the same space as cochains; the separate name
records which side of the coefficient pairing is meant. -/
abbrev Chain := ExteriorMonomial →₀ ℂ

/-- The coefficient pairing between cochains and chains. -/
abbrev pairing : Cochain →ₗ[ℂ] Chain →ₗ[ℂ] ℂ := coefficientPairing

@[simp] theorem pairing_single_single (s t : ExteriorMonomial) (a b : ℂ) :
    pairing (Finsupp.single s a) (Finsupp.single t b) =
      if s = t then a * b else 0 := by
  by_cases h : s = t
  · subst h; simp
  · simp [h]

theorem pairing_single_left (s : ExteriorMonomial) (ζ : Chain) :
    pairing (Finsupp.single s 1) ζ = ζ s := by simp

theorem pairing_single_right (u : Cochain) (s : ExteriorMonomial) :
    pairing u (Finsupp.single s 1) = u s :=
  coefficientPairing_monomial_right u s

/-- The pairing separates chains. -/
theorem chain_ext {ζ ξ : Chain} (h : ∀ u : Cochain, pairing u ζ = pairing u ξ) :
    ζ = ξ := by
  ext s
  simpa using h (Finsupp.single s 1)

/-- The pairing separates cochains. -/
theorem cochain_ext_pairing {u v : Cochain} (h : ∀ ζ : Chain, pairing u ζ = pairing v ζ) :
    u = v := by
  ext s
  have := h (Finsupp.single s 1)
  rwa [pairing_single_right, pairing_single_right] at this

/-! ## Finite graded pieces of monomials -/

/-- All generators of weight at most `S`. -/
def modesBelow (S : ℕ) : Finset Mode :=
  ((Finset.range S) ×ˢ (Finset.univ : Finset (Fin 3))).image (fun x => Mode.b x.1 x.2) ∪
    ((Finset.range S) ×ˢ (Finset.univ : Finset (Fin 3))).image (fun x => Mode.c x.1 x.2)

theorem mem_modesBelow {S : ℕ} {m : Mode} : m ∈ modesBelow S ↔ m.weight ≤ S := by
  cases m with
  | b j a => simp [modesBelow, Mode.weight, Nat.lt_iff_add_one_le]
  | c j a => simp [modesBelow, Mode.weight, Nat.lt_iff_add_one_le]

theorem weight_le_of_mem {s : ExteriorMonomial} {m : Mode} (hm : m ∈ s) :
    m.weight ≤ ∑ n ∈ s, n.weight :=
  Finset.single_le_sum (f := Mode.weight) (fun _ _ => Nat.zero_le _) hm

/-- The finite set of monomials of a given degree. -/
def degreeMonomials (d : Degree) : Finset ExteriorMonomial :=
  ((modesBelow d.2.2.toNat).powerset).filter fun s => monomialDegree s = d

theorem mem_degreeMonomials {d : Degree} {s : ExteriorMonomial} :
    s ∈ degreeMonomials d ↔ monomialDegree s = d := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, h⟩
    intro m hm
    rw [mem_modesBelow]
    have hw : (d.2.2) = ((∑ n ∈ s, n.weight : ℕ) : ℤ) := by
      rw [← h]; rfl
    rw [hw, Int.toNat_natCast]
    exact weight_le_of_mem hm

theorem single_mem_cochainPiece_iff {s : ExteriorMonomial} {d : Degree} {r : ℂ}
    (hr : r ≠ 0) : Finsupp.single s r ∈ cochainPiece d ↔ monomialDegree s = d := by
  constructor
  · intro h
    have hs : s ∈ (Finsupp.single s r).support := by simp [hr]
    exact h hs
  · intro h
    rw [← h]
    exact cochain_single_mem s r

/-- The coefficient of a homogeneous cochain at a monomial of another degree vanishes. -/
theorem apply_eq_zero_of_mem_piece {d : Degree} {u : Cochain} (hu : u ∈ cochainPiece d)
    {s : ExteriorMonomial} (hs : monomialDegree s ≠ d) : u s = 0 := by
  by_contra h
  exact hs (hu (Finsupp.mem_support_iff.mpr h))

/-! ## Graded transposes -/

/-- The transpose, on finite chains, of an operator raising the degree by `δ`. -/
def gradedTranspose (F : Cochain →ₗ[ℂ] Cochain) (δ : Degree) : Chain →ₗ[ℂ] Chain :=
  Finsupp.linearCombination ℂ fun s =>
    ∑ t ∈ degreeMonomials (monomialDegree s - δ),
      F (Finsupp.single t 1) s • (Finsupp.single t 1 : Chain)

/-- An operator raising every degree by `δ`. -/
def IsHomogeneousOp (F : Cochain →ₗ[ℂ] Cochain) (δ : Degree) : Prop :=
  ∀ d u, u ∈ cochainPiece d → F u ∈ cochainPiece (d + δ)

theorem gradedTranspose_single_apply (F : Cochain →ₗ[ℂ] Cochain) (δ : Degree)
    (hF : IsHomogeneousOp F δ) (s t : ExteriorMonomial) :
    gradedTranspose F δ (Finsupp.single s 1) t = F (Finsupp.single t 1) s := by
  classical
  rw [gradedTranspose, Finsupp.linearCombination_single, one_smul, Finset.sum_apply']
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq']
  split_ifs with ht
  · rfl
  · symm
    apply apply_eq_zero_of_mem_piece (hF _ _ (cochain_single_mem t 1))
    intro h
    exact ht (mem_degreeMonomials.mpr (eq_sub_of_add_eq h.symm))

/-- The defining adjunction of the graded transpose. -/
theorem pairing_gradedTranspose (F : Cochain →ₗ[ℂ] Cochain) (δ : Degree)
    (hF : IsHomogeneousOp F δ) (u : Cochain) (ζ : Chain) :
    pairing (F u) ζ = pairing u (gradedTranspose F δ ζ) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]
  | single t a =>
    induction ζ using Finsupp.induction_linear with
    | zero => simp
    | add ζ ξ hζ hξ => simp only [map_add, hζ, hξ]
    | single s b =>
      have hs : (Finsupp.single s b : Chain) = b • Finsupp.single s 1 := by simp
      have ht : (Finsupp.single t a : Cochain) = a • Finsupp.single t 1 := by simp
      rw [hs, ht]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, pairing_single_right,
        pairing_single_left, gradedTranspose_single_apply F δ hF s t]

end KhanSL2

namespace KhanSL2

open FiniteExterior

theorem gradedTranspose_degree (F : Cochain →ₗ[ℂ] Cochain) (δ : Degree)
    (hF : IsHomogeneousOp F δ) {d : Degree} {ζ : Chain} (hζ : ζ ∈ cochainPiece d) :
    gradedTranspose F δ ζ ∈ cochainPiece (d - δ) := by
  intro t ht
  have ht' := Finsupp.mem_support_iff.mp (Finset.mem_coe.mp ht)
  show monomialDegree t = d - δ
  by_contra hdeg
  apply ht'
  have hζ' : ζ = ∑ s ∈ ζ.support, ζ s • (Finsupp.single s 1 : Chain) := by
    conv_lhs => rw [← Finsupp.sum_single ζ]
    simp [Finsupp.sum, Finsupp.smul_single]
  rw [hζ', map_sum, Finset.sum_apply']
  apply Finset.sum_eq_zero
  intro s hs
  rw [map_smul, Finsupp.smul_apply, gradedTranspose_single_apply F δ hF, smul_eq_mul]
  have hsd : monomialDegree s = d := hζ hs
  rw [apply_eq_zero_of_mem_piece (hF _ _ (cochain_single_mem t 1)), mul_zero]
  intro h
  apply hdeg
  rw [← hsd, h]; abel

/-- Transposes reverse composition. -/
theorem gradedTranspose_comp (F G : Cochain →ₗ[ℂ] Cochain) (δ ε : Degree)
    (hF : IsHomogeneousOp F δ) (hG : IsHomogeneousOp G ε) (ζ : Chain) :
    gradedTranspose (F ∘ₗ G) (ε + δ) ζ = gradedTranspose G ε (gradedTranspose F δ ζ) := by
  have hFG : IsHomogeneousOp (F ∘ₗ G) (ε + δ) := by
    intro d u hu
    have := hF _ _ (hG d u hu)
    simpa [add_assoc] using this
  apply chain_ext
  intro u
  rw [← pairing_gradedTranspose _ _ hFG, ← pairing_gradedTranspose _ _ hG,
    ← pairing_gradedTranspose _ _ hF, LinearMap.comp_apply]

/-- The transpose of an operator that vanishes is zero. -/
theorem gradedTranspose_eq_zero (F : Cochain →ₗ[ℂ] Cochain) (δ : Degree)
    (hF : IsHomogeneousOp F δ) (h : ∀ u, F u = 0) (ζ : Chain) :
    gradedTranspose F δ ζ = 0 := by
  apply chain_ext
  intro u
  rw [← pairing_gradedTranspose _ _ hF, h u]
  simp

/-- The cochain represented, in a fixed degree, by a functional on chains. -/
def cochainOfFunctional (d : Degree) (G : Chain →ₗ[ℂ] ℂ) : Cochain :=
  ∑ s ∈ degreeMonomials d, G (Finsupp.single s 1) • (Finsupp.single s 1 : Cochain)

theorem cochainOfFunctional_mem (d : Degree) (G : Chain →ₗ[ℂ] ℂ) :
    cochainOfFunctional d G ∈ cochainPiece d := by
  apply Submodule.sum_mem
  intro s hs
  apply Submodule.smul_mem
  rw [← mem_degreeMonomials.mp hs]
  exact cochain_single_mem s 1

theorem chain_eq_sum_of_mem {d : Degree} {ζ : Chain} (hζ : ζ ∈ cochainPiece d) :
    ζ = ∑ s ∈ degreeMonomials d, ζ s • (Finsupp.single s 1 : Chain) := by
  conv_lhs => rw [← Finsupp.sum_single ζ]
  rw [Finsupp.sum]
  apply Finset.sum_subset_zero_on_sdiff
  · intro s hs
    exact mem_degreeMonomials.mpr (hζ hs)
  · intro s hs
    have : ζ s = 0 := by
      have := (Finset.mem_sdiff.mp hs).2
      simpa using this
    simp [this]
  · intro s _
    simp [Finsupp.smul_single]

theorem pairing_cochainOfFunctional (d : Degree) (G : Chain →ₗ[ℂ] ℂ) {ζ : Chain}
    (hζ : ζ ∈ cochainPiece d) : pairing (cochainOfFunctional d G) ζ = G ζ := by
  conv_rhs => rw [chain_eq_sum_of_mem hζ]
  simp only [cochainOfFunctional, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, pairing_single_left, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- A homogeneous cochain is determined by its pairings with monomials of its degree. -/
theorem cochain_eq_zero_of_pairing {d : Degree} {u : Cochain} (hu : u ∈ cochainPiece d)
    (h : ∀ s, monomialDegree s = d → pairing u (Finsupp.single s 1) = 0) : u = 0 := by
  ext s
  by_cases hs : monomialDegree s = d
  · simpa [pairing_single_right] using h s hs
  · exact apply_eq_zero_of_mem_piece hu hs

end KhanSL2
