module

public import KhanSL2.ExteriorRing
public import KhanSL2.ExteriorSupercomm
public import Mathlib.Data.Finset.Sort

/-! Substitution of anticommuting square-zero elements into the explicit
finite exterior algebra. This extends the existing reindexing operation
to the linear color substitutions required by Cartan restriction. -/

@[expose] public section

noncomputable section

set_option maxHeartbeats 400000

namespace KhanSL2.FiniteExterior

variable {α : Type*} [DecidableEq α] [GeneratorOrder α]

abbrev codeOrder : LinearOrder α :=
  LinearOrder.lift' GeneratorOrder.code GeneratorOrder.code_injective

attribute [local instance] codeOrder

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Evaluate the generators of a monomial in increasing code order. -/
def orderedEval (f : α → A) (s : Finset α) : A :=
  ((s.sort (· ≤ ·)).map f).prod

omit [DecidableEq α] [Algebra ℂ A] in
@[simp] theorem orderedEval_empty (f : α → A) : orderedEval f ∅ = 1 := by
  simp [orderedEval]

omit [DecidableEq α] [Algebra ℂ A] in
@[simp] theorem orderedEval_singleton (f : α → A) (a : α) :
    orderedEval f {a} = f a := by
  simp [orderedEval]

omit [Algebra ℂ A] in
theorem orderedEval_insert_min (f : α → A) (a : α) (s : Finset α)
    (ha : ∀ b ∈ s, GeneratorOrder.code a < GeneratorOrder.code b) :
    orderedEval f (insert a s) = f a * orderedEval f s := by
  have hlt : ∀ b ∈ s, a < b := ha
  have hnot : a ∉ s := fun h => lt_irrefl a (hlt a h)
  simp [orderedEval, Finset.sort_insert _ (fun b hb => (hlt b hb).le) hnot]

/-- Multiplication by a generator satisfies exactly the exterior insertion
rule, for every anticommuting square-zero family in the target algebra. -/
theorem generator_mul_orderedEval (f : α → A)
    (hsq : ∀ a, f a * f a = 0)
    (hanti : ∀ a b, f a * f b = -(f b * f a))
    (a : α) (s : Finset α) :
    f a * orderedEval f s =
      if a ∈ s then 0 else
        (-1 : ℂ) ^ position GeneratorOrder.code a s • orderedEval f (insert a s) := by
  induction s using Finset.induction_on_min with
  | empty => simp [position]
  | insert b s hb ih =>
    have hbs : b ∉ s := fun h => lt_irrefl b (hb b h)
    have hbcode : ∀ c ∈ s, GeneratorOrder.code b < GeneratorOrder.code c := hb
    rw [orderedEval_insert_min f b s hbcode]
    rcases lt_trichotomy a b with hab | rfl | hba
    · have haall : ∀ c ∈ insert b s, GeneratorOrder.code a < GeneratorOrder.code c := by
        intro c hc
        rcases Finset.mem_insert.mp hc with rfl | hc
        · exact hab
        · exact lt_trans hab (hb c hc)
      have hanot : a ∉ insert b s := fun h => lt_irrefl a (haall a h)
      have hpos : position GeneratorOrder.code a (insert b s) = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.filter_eq_empty_iff.mpr
        intro c hc
        exact not_lt.mpr (le_of_lt (haall c hc))
      rw [if_neg hanot, hpos, pow_zero, one_smul,
        orderedEval_insert_min f a (insert b s) haall,
        orderedEval_insert_min f b s hbcode]
    · rw [if_pos (Finset.mem_insert_self a s), ← mul_assoc, hsq, zero_mul]
    · have hab : a ≠ b := ne_of_gt hba
      have hmem : a ∈ insert b s ↔ a ∈ s := by simp [hab]
      have hpos : position GeneratorOrder.code a (insert b s) =
          position GeneratorOrder.code a s + 1 := by
        unfold position
        rw [Finset.filter_insert]
        simp [show GeneratorOrder.code b < GeneratorOrder.code a from hba, hbs]
      have hmin : ∀ c ∈ insert a s, GeneratorOrder.code b < GeneratorOrder.code c := by
        intro c hc
        rcases Finset.mem_insert.mp hc with rfl | hc
        · exact hba
        · exact hb c hc
      calc
        f a * (f b * orderedEval f s) = -(f b * (f a * orderedEval f s)) := by
          rw [← mul_assoc, hanti a b, neg_mul, mul_assoc]
        _ = _ := by
          rw [ih]
          by_cases ha : a ∈ s
          · simp [hmem, ha]
          · have hins : insert a (insert b s) = insert b (insert a s) := by
              ext c
              simp only [Finset.mem_insert, or_left_comm]
            rw [if_neg ha, if_neg (hmem.not.mpr ha), hpos,
              hins, orderedEval_insert_min f b (insert a s) hmin]
            simp [pow_succ, mul_smul_comm, neg_smul]

attribute [-instance] codeOrder

/-- Linear extension of ordered generator evaluation. -/
def substituteLinear (f : α → A) : Exterior α →ₗ[ℂ] A :=
  Finsupp.linearCombination ℂ (orderedEval f)

omit [DecidableEq α] in
@[simp] theorem substituteLinear_monomial (f : α → A) (s : Finset α) :
    substituteLinear f (monomial s) = orderedEval f s := by
  simp [substituteLinear, monomial]

omit [DecidableEq α] in
@[simp] theorem substituteLinear_generator (f : α → A) (a : α) :
    substituteLinear f (generator a) = f a := by
  simp [generator]

@[simp] theorem substituteLinear_one (f : α → A) :
    substituteLinear f (1 : Exterior α) = 1 := by
  change substituteLinear f (monomial ∅) = 1
  simp

theorem substituteLinear_generator_mul (f : α → A)
    (hsq : ∀ a, f a * f a = 0)
    (hanti : ∀ a b, f a * f b = -(f b * f a))
    (a : α) (u : Exterior α) :
    substituteLinear f (generator a * u) = f a * substituteLinear f u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [mul_add, hu, hv]
  | single s r =>
    have hr : Finsupp.single s r = r • monomial s := by simp [monomial]
    rw [hr, mul_smul_comm, map_smul, map_smul, mul_smul_comm]
    congr 1
    change substituteLinear f (wedge GeneratorOrder.code (generator a) (monomial s)) = _
    rw [wedge_generator_monomial_eq, substituteLinear_monomial,
      generator_mul_orderedEval f hsq hanti]
    by_cases ha : a ∈ s
    · rw [if_pos ha, if_pos ha, map_zero]
    · rw [if_neg ha, if_neg ha, map_smul, substituteLinear_monomial]

theorem substituteLinear_mul (f : α → A)
    (hsq : ∀ a, f a * f a = 0)
    (hanti : ∀ a b, f a * f b = -(f b * f a))
    (u v : Exterior α) :
    substituteLinear f (u * v) = substituteLinear f u * substituteLinear f v := by
  refine induction_on GeneratorOrder.code
    (P := fun w => substituteLinear f (w * v) =
      substituteLinear f w * substituteLinear f v) ?_ ?_ ?_ ?_ ?_ u
  · simp
  · change substituteLinear f (1 * v) = substituteLinear f 1 * _
    simp
  · intro w z hw hz
    simp only [add_mul, map_add, hw, hz]
  · intro r w hw
    simp only [smul_mul_assoc, map_smul, hw]
  · intro a u hu
    change substituteLinear f ((generator a * u) * v) =
      substituteLinear f (generator a * u) * substituteLinear f v
    rw [mul_assoc, substituteLinear_generator_mul f hsq hanti a (u * v),
      substituteLinear_generator_mul f hsq hanti a u, hu, mul_assoc]

/-- The universal substitution homomorphism for the concrete exterior algebra. -/
def substitute (f : α → A)
    (hsq : ∀ a, f a * f a = 0)
    (hanti : ∀ a b, f a * f b = -(f b * f a)) : Exterior α →ₐ[ℂ] A where
  toFun := substituteLinear f
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := substituteLinear_one f
  map_mul' := substituteLinear_mul f hsq hanti
  commutes' r := by
    change substituteLinear f (Finsupp.single ∅ r) = algebraMap ℂ A r
    simp [substituteLinear, Algebra.algebraMap_eq_smul_one]

@[simp] theorem substitute_generator (f : α → A)
    (hsq : ∀ a, f a * f a = 0)
    (hanti : ∀ a b, f a * f b = -(f b * f a)) (a : α) :
    substitute f hsq hanti (generator a) = f a :=
  substituteLinear_generator f a

theorem odd_mul_odd {β : Type*} [DecidableEq β] [GeneratorOrder β]
    (u v : Exterior β) (hu : parityLinear u = -u) (hv : parityLinear v = -v) :
    u * v = -(v * u) := by
  change wedge GeneratorOrder.code u v = -wedge GeneratorOrder.code v u
  rw [wedge_comm_of_parity_odd GeneratorOrder.code GeneratorOrder.code_injective v hv u, hu]
  simp [wedge]

theorem odd_sq_zero {β : Type*} [DecidableEq β] [GeneratorOrder β]
    (u : Exterior β) (hu : parityLinear u = -u) : u * u = 0 := by
  have h := odd_mul_odd u u hu hu
  have htwo : (2 : ℂ) • (u * u) = 0 := by
    simpa only [two_smul] using eq_neg_iff_add_eq_zero.mp h
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Any odd generator family admits substitution into another finite
exterior algebra. -/
def substituteOdd {β : Type*} [DecidableEq β] [GeneratorOrder β]
    (f : α → Exterior β) (hf : ∀ a, parityLinear (f a) = -f a) :
    Exterior α →ₐ[ℂ] Exterior β :=
  substitute f (fun a => odd_sq_zero (f a) (hf a))
    (fun a b => odd_mul_odd (f a) (f b) (hf a) (hf b))

@[simp] theorem substituteOdd_generator {β : Type*} [DecidableEq β] [GeneratorOrder β]
    (f : α → Exterior β) (hf : ∀ a, parityLinear (f a) = -f a) (a : α) :
    substituteOdd f hf (generator a) = f a := substituteLinear_generator f a

end KhanSL2.FiniteExterior
