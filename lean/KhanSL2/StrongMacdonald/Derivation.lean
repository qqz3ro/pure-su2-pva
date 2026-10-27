module

public import KhanSL2.StrongMacdonald.DiffOp

@[expose] public section

/-!
# Super-commutation and derivations on the Macdonald algebra

`W` is super-commutative: even generators are central and an odd FiniteExterior.generator moves past
any element at the cost of the parity automorphism. Super-derivations have order at
most one, and the graded commutator of a derivation with an operator of order `≤ l`
again has order `≤ l`.
-/

noncomputable section
open scoped BigOperators

namespace KhanSL2.StrongMacdonald

open AddMonoidAlgebra (single)

/-! ## Exterior commutation -/

theorem ext_generator_anticomm (a b : PMode) :
    (FiniteExterior.generator a : Ext) * FiniteExterior.generator b = -(FiniteExterior.generator b * FiniteExterior.generator a) := by
  rw [FiniteExterior.mul_def, FiniteExterior.mul_def]
  simp only [FiniteExterior.generator, FiniteExterior.wedge_monomial]
  by_cases hab : a = b
  · subst hab
    simp [FiniteExterior.monomialWedge]
  · have hd : Disjoint ({a} : Finset PMode) {b} := Finset.disjoint_singleton.mpr hab
    have hd' : Disjoint ({b} : Finset PMode) {a} := hd.symm
    simp only [FiniteExterior.monomialWedge, hd, hd', ↓reduceIte, FiniteExterior.inversionCount,
      Finset.sum_singleton, Finset.union_comm {b} {a}]
    rw [← Finsupp.single_neg]
    congr 1
    have hcode : FiniteExterior.GeneratorOrder.code a ≠ FiniteExterior.GeneratorOrder.code b :=
      fun h => hab (FiniteExterior.GeneratorOrder.code_injective h)
    rcases lt_or_gt_of_ne hcode with h | h
    · rw [Finset.filter_singleton, Finset.filter_singleton, if_neg (by omega), if_pos h]
      simp
    · rw [Finset.filter_singleton, Finset.filter_singleton, if_pos h, if_neg (by omega)]
      simp

theorem ext_mul_generator (u : Ext) (m : PMode) :
    u * FiniteExterior.generator m = FiniteExterior.generator m * FiniteExterior.parityLinear u := by
  refine FiniteExterior.induction_on BGG.PositiveCE.Mode.code
    (P := fun u : Ext => u * FiniteExterior.generator m = FiniteExterior.generator m * FiniteExterior.parityLinear u) ?_ ?_ ?_ ?_ ?_ u
  · simp
  · change (1 : Ext) * FiniteExterior.generator m = FiniteExterior.generator m * FiniteExterior.parityLinear 1
    rw [one_mul, show FiniteExterior.parityLinear (1 : Ext) = 1 from FiniteExterior.parity_one, mul_one]
  · intro u v hu hv
    rw [add_mul, hu, hv, map_add, mul_add]
  · intro r u hu
    rw [smul_mul_assoc, hu, map_smul, mul_smul_comm]
  · intro a u hu
    change FiniteExterior.generator a * u * FiniteExterior.generator m =
      FiniteExterior.generator m * FiniteExterior.parityLinear (FiniteExterior.generator a * u)
    have hpar : FiniteExterior.parityLinear (FiniteExterior.generator a * u : Ext) =
        -(FiniteExterior.generator a) * FiniteExterior.parityLinear u := by
      have := map_mul FiniteExterior.parity (FiniteExterior.generator a : Ext) u
      rw [FiniteExterior.parity_apply, FiniteExterior.parity_apply, FiniteExterior.parity_apply,
        FiniteExterior.parity_generator] at this
      exact this
    rw [mul_assoc, hu, ← mul_assoc, ext_generator_anticomm, hpar]
    simp [mul_assoc]

/-! ## Super-commutation in `W` -/

theorem mul_psi (x : W) (m : PMode) : x * psi m = psi m * parity x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_mul, hx, hy, map_add, mul_add]
  | single e u =>
    rw [parity_single, psi_mul_single, psi, AddMonoidAlgebra.single_mul_single, add_zero,
      ext_mul_generator]

/-- Homogeneous elements of parity `q`. -/
def IsPar (q : ℕ) (x : W) : Prop := parity x = ((-1 : ℂ) ^ q) • x

theorem isPar_sig (g : SMode) : IsPar 0 (sig g) := by simp [IsPar]

theorem isPar_psi (m : PMode) : IsPar 1 (psi m) := by simp [IsPar]

theorem isPar_gen (g : Gen) : IsPar g.par g.elt := by
  cases g with
  | s g => exact isPar_sig g
  | p m => exact isPar_psi m

theorem IsPar.add {q : ℕ} {x y : W} (hx : IsPar q x) (hy : IsPar q y) : IsPar q (x + y) := by
  unfold IsPar at *
  rw [map_add, hx, hy, smul_add]

theorem IsPar.smul {q : ℕ} (r : ℂ) {x : W} (hx : IsPar q x) : IsPar q (r • x) := by
  unfold IsPar at *
  rw [map_smul, hx, smul_comm]

theorem IsPar.zero (q : ℕ) : IsPar q 0 := by simp [IsPar]

theorem IsPar.mul {q r : ℕ} {x y : W} (hx : IsPar q x) (hy : IsPar r y) :
    IsPar (q + r) (x * y) := by
  unfold IsPar at *
  rw [map_mul, hx, hy, smul_mul_assoc, mul_smul_comm, smul_smul, pow_add]

theorem IsPar.sum {q : ℕ} {ι : Type*} (s : Finset ι) (x : ι → W) (hx : ∀ i ∈ s, IsPar q (x i)) :
    IsPar q (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsPar.zero q
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hx a (Finset.mem_insert_self a s)).add (ih fun i hi => hx i (Finset.mem_insert_of_mem hi))

theorem IsPar.parity_mod {q : ℕ} {x : W} (hx : IsPar q x) : IsPar (q % 2) x := by
  unfold IsPar at *
  rw [hx, ← Nat.mod_add_div q 2, pow_add, pow_mul]
  simp [Nat.mod_mod]

/-- A homogeneous element commutes with a generator up to the Koszul sign. -/
theorem IsPar.mul_gen {q : ℕ} {x : W} (hx : IsPar q x) (g : Gen) :
    x * g.elt = ((-1 : ℂ) ^ (q * g.par)) • (g.elt * x) := by
  cases g with
  | s g => simp [Gen.elt, Gen.par, sig_commute]
  | p m =>
    simp only [Gen.elt, Gen.par, mul_one]
    rw [mul_psi, hx, mul_smul_comm]

/-- Left multiplication by a homogeneous element has order zero. -/
theorem IsPar.isDiffOp_lmul {q : ℕ} {y : W} (hy : IsPar q y) : IsDiffOp 0 q (lmul y) := by
  intro g
  apply LinearMap.ext
  intro x
  rw [gcomm_apply, LinearMap.zero_apply, lmul_apply, lmul_apply, ← mul_assoc, ← mul_assoc,
    hy.mul_gen g, smul_mul_assoc, sub_self]

/-! ## Super-derivations -/

/-- `D` is a super-derivation of parity `p`. -/
def IsDer (p : ℕ) (D : Module.End ℂ W) : Prop :=
  ∀ x y, D (x * y) = D x * y + (parity^[p] x) * D y

theorem parity_iterate_gen (p : ℕ) (g : Gen) :
    parity^[p] g.elt = ((-1 : ℂ) ^ (p * g.par)) • g.elt := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Function.iterate_succ_apply', ih, map_smul, isPar_gen g, smul_smul, ← pow_add]
    congr 1
    ring

theorem parity_iterate_one (n : ℕ) : parity^[n] (1 : W) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; exact map_one parity

theorem IsDer.map_one {p : ℕ} {D : Module.End ℂ W} (hD : IsDer p D) : D 1 = 0 := by
  have h := hD 1 1
  rw [one_mul, mul_one, parity_iterate_one, one_mul] at h
  have h2 : D 1 + D 1 = D 1 + 0 := by rw [add_zero]; exact h.symm
  exact (add_left_cancel h2).symm.symm

/-- The graded commutator of a derivation with a generator is left multiplication. -/
theorem IsDer.gcomm_eq {p : ℕ} {D : Module.End ℂ W} (hD : IsDer p D) (g : Gen) :
    gcomm p D g = lmul (D g.elt) := by
  apply LinearMap.ext
  intro x
  rw [gcomm_apply, hD, parity_iterate_gen, smul_mul_assoc, lmul_apply]
  abel

/-- Derivations with homogeneous generator images have order at most one. -/
theorem IsDer.isDiffOp {p : ℕ} {D : Module.End ℂ W} (hD : IsDer p D)
    (himg : ∀ g : Gen, IsPar (p + g.par) (D g.elt)) : IsDiffOp 1 p D := by
  intro g
  rw [hD.gcomm_eq g]
  exact (himg g).isDiffOp_lmul

/-- Derivations of the same parity agreeing on generators agree. -/
theorem IsDer.ext {p : ℕ} {D E : Module.End ℂ W} (hD : IsDer p D) (hE : IsDer p E)
    (hgen : ∀ g : Gen, D g.elt = E g.elt) : D = E := by
  apply LinearMap.ext
  intro x
  refine induction_gen (P := fun x => D x = E x) ?_ ?_ ?_ ?_ ?_ ?_ x
  · simp
  · rw [hD.map_one, hE.map_one]
  · intro x y hx hy; rw [map_add, map_add, hx, hy]
  · intro r x hx; rw [map_smul, map_smul, hx]
  · intro g x hx
    rw [hD, hE, hx]
    exact congrArg (· * x + _) (hgen (.s g))
  · intro m x hx
    rw [hD, hE, hx]
    exact congrArg (· * x + _) (hgen (.p m))

theorem IsDer.add {p : ℕ} {D E : Module.End ℂ W} (hD : IsDer p D) (hE : IsDer p E) :
    IsDer p (D + E) := by
  intro x y
  simp only [LinearMap.add_apply, hD x y, hE x y, add_mul, mul_add]
  abel

theorem IsDer.smul {p : ℕ} (r : ℂ) {D : Module.End ℂ W} (hD : IsDer p D) : IsDer p (r • D) := by
  intro x y
  simp only [LinearMap.smul_apply, hD x y, smul_add, smul_mul_assoc, mul_smul_comm]

theorem IsDer.zero (p : ℕ) : IsDer p 0 := by
  intro x y; simp

theorem IsDer.sum {p : ℕ} {ι : Type*} (s : Finset ι) (D : ι → Module.End ℂ W)
    (hD : ∀ i ∈ s, IsDer p (D i)) : IsDer p (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsDer.zero p
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hD a (Finset.mem_insert_self a s)).add (ih fun i hi => hD i (Finset.mem_insert_of_mem hi))

end KhanSL2.StrongMacdonald
