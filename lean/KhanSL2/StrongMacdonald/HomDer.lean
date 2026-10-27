module

public import KhanSL2.StrongMacdonald.MkDer

@[expose] public section

/-!
# Homogeneous super-derivations

A homogeneous derivation of parity `p` is a super-derivation whose generator images have
parity `p + par g`. Such derivations commute with the parity automorphism up to `(-1)^p`,
form a super Lie algebra under graded commutators, and have order at most one.
-/

noncomputable section
open scoped BigOperators

namespace KhanSL2.StrongMacdonald

theorem IsPar.of_add_two {q : ℕ} {x : W} (hx : IsPar (q + 2) x) : IsPar q x := by
  unfold IsPar at *
  rw [hx, pow_add]
  simp

theorem IsPar.add_two {q : ℕ} {x : W} (hx : IsPar q x) : IsPar (q + 2) x := by
  unfold IsPar at *
  rw [hx, pow_add]
  simp

theorem IsPar.congr {q r : ℕ} {x : W} (hx : IsPar q x) (h : q % 2 = r % 2) : IsPar r x := by
  have h1 := hx.parity_mod
  rw [h] at h1
  unfold IsPar at *
  rw [h1, ← Nat.mod_add_div r 2, pow_add, pow_mul]
  simp

theorem IsPar.neg {q : ℕ} {x : W} (hx : IsPar q x) : IsPar q (-x) := by
  have := hx.smul (-1)
  simpa using this

theorem IsPar.sub {q : ℕ} {x y : W} (hx : IsPar q x) (hy : IsPar q y) : IsPar q (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem isPar_one (q : ℕ) (hq : q % 2 = 0) : IsPar q (1 : W) :=
  (show IsPar 0 (1 : W) by simp [IsPar]).congr (by omega)

/-- Homogeneous super-derivations of parity `p`. -/
def HomDer (p : ℕ) (D : Module.End ℂ W) : Prop :=
  IsDer p D ∧ ∀ g : Gen, IsPar (p + g.par) (D g.elt)

theorem HomDer.isDer {p : ℕ} {D : Module.End ℂ W} (h : HomDer p D) : IsDer p D := h.1

theorem HomDer.isDiffOp {p : ℕ} {D : Module.End ℂ W} (h : HomDer p D) : IsDiffOp 1 p D :=
  h.1.isDiffOp h.2

theorem HomDer.map_one {p : ℕ} {D : Module.End ℂ W} (h : HomDer p D) : D 1 = 0 := h.1.map_one

theorem neg_one_pow_add_self (p : ℕ) : (-1 : ℂ) ^ (p + p) = 1 := by
  rw [← two_mul, pow_mul]; simp

theorem neg_one_pow_add_self_succ (p : ℕ) : (-1 : ℂ) ^ (p + (p + 1)) = -1 := by
  rw [← add_assoc, pow_succ, neg_one_pow_add_self]; simp

/-- Homogeneous derivations commute with parity up to the sign `(-1)^p`. -/
theorem HomDer.parity_comm {p : ℕ} {D : Module.End ℂ W} (h : HomDer p D) (x : W) :
    D (parity x) = ((-1 : ℂ) ^ p) • parity (D x) := by
  refine induction_gen (P := fun x => D (parity x) = ((-1 : ℂ) ^ p) • parity (D x))
    ?_ ?_ ?_ ?_ ?_ ?_ x
  · simp
  · rw [show parity (1 : W) = 1 from _root_.map_one parity, h.map_one, map_zero, smul_zero]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy, map_add, map_add, smul_add]
  · intro r x hx
    rw [map_smul, map_smul, hx, map_smul, map_smul, smul_comm]
  · intro g x hx
    have hg := h.2 (.s g)
    simp only [Gen.elt, Gen.par, add_zero] at hg
    have hi : parity^[p] (sig g) = sig g := by
      simpa [Gen.elt, Gen.par] using parity_iterate_gen p (.s g)
    rw [map_mul, parity_sig, h.1, hx, h.1, map_add, map_mul, map_mul, hg, hi, parity_sig]
    simp only [smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, ← pow_add,
      neg_one_pow_add_self, one_smul]
  · intro m x hx
    have hg := h.2 (.p m)
    simp only [Gen.elt, Gen.par] at hg
    have hi : parity^[p] (psi m) = ((-1 : ℂ) ^ p) • psi m := by
      simpa [Gen.elt, Gen.par] using parity_iterate_gen p (.p m)
    rw [map_mul, parity_psi, neg_mul, map_neg, h.1, hx, h.1, map_add, map_mul, map_mul, hg, hi,
      map_smul, parity_psi]
    simp only [smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, ← pow_add,
      neg_one_pow_add_self, neg_one_pow_add_self_succ, one_smul, neg_mul, mul_neg, smul_neg,
      neg_smul, neg_add, neg_neg]

theorem HomDer.isPar_apply {p q : ℕ} {D : Module.End ℂ W} (h : HomDer p D) {x : W}
    (hx : IsPar q x) : IsPar (p + q) (D x) := by
  unfold IsPar at *
  have h1 := h.parity_comm x
  rw [hx, map_smul] at h1
  have h2 : parity (D x) = ((-1 : ℂ) ^ p) • ((-1 : ℂ) ^ q) • D x := by
    rw [h1, smul_smul, ← pow_add, ← two_mul, pow_mul]; simp
  rw [h2, smul_smul, ← pow_add]

theorem HomDer.add {p : ℕ} {A B : Module.End ℂ W} (hA : HomDer p A) (hB : HomDer p B) :
    HomDer p (A + B) :=
  ⟨hA.1.add hB.1, fun g => (hA.2 g).add (hB.2 g)⟩

theorem HomDer.smul {p : ℕ} (r : ℂ) {A : Module.End ℂ W} (hA : HomDer p A) :
    HomDer p (r • A) :=
  ⟨hA.1.smul r, fun g => (hA.2 g).smul r⟩

theorem HomDer.zero (p : ℕ) : HomDer p 0 := ⟨IsDer.zero p, fun _ => IsPar.zero _⟩

theorem HomDer.neg {p : ℕ} {A : Module.End ℂ W} (hA : HomDer p A) : HomDer p (-A) := by
  rw [← neg_one_smul ℂ A]; exact hA.smul (-1)

theorem HomDer.sub {p : ℕ} {A B : Module.End ℂ W} (hA : HomDer p A) (hB : HomDer p B) :
    HomDer p (A - B) := by
  rw [sub_eq_add_neg]; exact hA.add hB.neg

theorem HomDer.sum {p : ℕ} {ι : Type*} (s : Finset ι) (D : ι → Module.End ℂ W)
    (hD : ∀ i ∈ s, HomDer p (D i)) : HomDer p (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HomDer.zero p
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hD a (Finset.mem_insert_self a s)).add (ih fun i hi => hD i (Finset.mem_insert_of_mem hi))

theorem mkDer_homDer {p : ℕ} (fσ : SMode → W) (fψ : PMode → W) (hσ : ∀ g, IsPar p (fσ g))
    (hψ : ∀ m, IsPar (p + 1) (fψ m)) : HomDer p (mkDer fσ fψ) := by
  refine ⟨mkDer_isDer fσ fψ hσ hψ, fun g => ?_⟩
  cases g with
  | s g => simpa [Gen.elt, Gen.par, mkDer_sig] using hσ g
  | p m => simpa [Gen.elt, Gen.par, mkDer_psi] using hψ m

/-! ## Graded commutators -/

/-- The anticommutator of two odd derivations is an even derivation. -/
theorem HomDer.anticomm {A B : Module.End ℂ W} (hA : HomDer 1 A) (hB : HomDer 1 B) :
    HomDer 0 (A * B + B * A) := by
  refine ⟨fun x y => ?_, fun g => ?_⟩
  · have hA1 : ∀ x y, A (x * y) = A x * y + parity x * A y := fun x y => hA.1 x y
    have hB1 : ∀ x y, B (x * y) = B x * y + parity x * B y := fun x y => hB.1 x y
    show A (B (x * y)) + B (A (x * y)) = (A (B x) + B (A x)) * y + x * (A (B y) + B (A y))
    simp only [hA1, hB1, map_add, hA.parity_comm, hB.parity_comm, parity_parity, pow_one,
      neg_smul, one_smul, neg_mul, add_mul, mul_add]
    abel
  · have h1 := hA.isPar_apply (hB.2 g)
    have h2 := hB.isPar_apply (hA.2 g)
    exact (h1.add h2).congr (by omega)

theorem HomDer.parity_iterate_comm {B : Module.End ℂ W} (hB : HomDer 0 B) (p : ℕ) (z : W) :
    parity^[p] (B z) = B (parity^[p] z) := by
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hB.parity_comm]
    simp

/-- The commutator of a homogeneous derivation with an even one is homogeneous. -/
theorem HomDer.comm_even {p : ℕ} {A B : Module.End ℂ W} (hA : HomDer p A) (hB : HomDer 0 B) :
    HomDer p (A * B - B * A) := by
  refine ⟨fun x y => ?_, fun g => ?_⟩
  · have hB0 : ∀ x y, B (x * y) = B x * y + x * B y := fun x y => hB.1 x y
    have hAp : ∀ x y, A (x * y) = A x * y + parity^[p] x * A y := fun x y => hA.1 x y
    have hpar : ∀ z, parity^[p] (B z) = B (parity^[p] z) := hB.parity_iterate_comm p
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hB0, hAp, map_add, hpar, sub_mul,
      mul_sub]
    abel
  · have h1 := hA.isPar_apply (hB.2 g)
    have h2 := hB.isPar_apply (hA.2 g)
    show IsPar (p + g.par) (A (B g.elt) - B (A g.elt))
    exact (h1.sub (h2.congr (by omega))).congr (by omega)

/-- Left multiplication by an odd generator after an odd derivation is an even derivation. -/
theorem HomDer.psi_mul {D : Module.End ℂ W} (hD : HomDer 1 D) (n : PMode) :
    HomDer 0 (lmul (psi n) * D) := by
  refine ⟨fun x y => ?_, fun g => ?_⟩
  · simp only [Module.End.mul_apply, lmul_apply, hD.1 x y, Function.iterate_one,
      Function.iterate_zero, id_eq, mul_add, ← mul_assoc]
    rw [← mul_psi]
  · simp only [Module.End.mul_apply, lmul_apply]
    exact ((isPar_psi n).mul (hD.2 g)).congr (by omega)

/-! ## The primitive derivations -/

theorem iP_homDer (m : PMode) : HomDer 1 (iP m) := by
  refine ⟨isDer_of_gen (iP_one m) fun g x => ?_, fun g => ?_⟩
  · cases g with
    | s h => simp [Gen.elt, Gen.par, iP_sig_mul, iP_sig]
    | p n =>
      simp only [Gen.elt, Gen.par, iP_psi_mul, iP_psi, mul_one, pow_one, neg_smul, one_smul]
      split <;> simp [sub_eq_add_neg]
  · cases g with
    | s h => simpa [Gen.elt, Gen.par, iP_sig] using IsPar.zero 1
    | p n =>
      simp only [Gen.elt, Gen.par, iP_psi]
      split
      · exact isPar_one 2 rfl
      · exact IsPar.zero _

end KhanSL2.StrongMacdonald
