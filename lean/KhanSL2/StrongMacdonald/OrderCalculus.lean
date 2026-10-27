module

public import KhanSL2.StrongMacdonald.Derivation

@[expose] public section

/-!
# Order calculus for super-differential operators

* products add orders;
* the graded commutator of an operator of order `≤ l` with left multiplication by a
  product of generators has order `≤ l - 1`;
* the graded commutator of a super-derivation with an operator of order `≤ l` has
  order `≤ l`.

These are exactly what is needed to see that the Laplacian `[∂̄, ∂̄^*]` of the
Macdonald complex has order at most two.
-/

noncomputable section
open scoped BigOperators

namespace KhanSL2.StrongMacdonald

/-- The graded commutator `[P, Q] = PQ - (-1)^{pq} QP`. -/
def scomm (p q : ℕ) (P Q : Module.End ℂ W) : Module.End ℂ W :=
  P * Q - ((-1 : ℂ) ^ (p * q)) • (Q * P)

theorem gcomm_eq_scomm (p : ℕ) (P : Module.End ℂ W) (g : Gen) :
    gcomm p P g = scomm p g.par P (lmul g.elt) := rfl

theorem gcomm_mul (p q : ℕ) (P Q : Module.End ℂ W) (g : Gen) :
    gcomm (p + q) (P * Q) g =
      P * gcomm q Q g + ((-1 : ℂ) ^ (q * g.par)) • (gcomm p P g * Q) := by
  simp only [gcomm, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub, smul_smul,
    ← pow_add, mul_assoc]
  rw [show q * g.par + p * g.par = (p + q) * g.par by ring]
  abel

theorem IsDiffOp.congr_par {k p p' : ℕ} {P : Module.End ℂ W} (hP : IsDiffOp k p P)
    (h : p = p') : IsDiffOp k p' P := h ▸ hP

theorem isDiffOp_mul_aux (n : ℕ) : ∀ (k l p q : ℕ) (P Q : Module.End ℂ W), k + l = n →
    IsDiffOp k p P → IsDiffOp l q Q → IsDiffOp n (p + q) (P * Q) := by
  induction n with
  | zero =>
    intro k l p q P Q hkl hP hQ
    obtain ⟨rfl, rfl⟩ : k = 0 ∧ l = 0 := by omega
    intro g
    rw [gcomm_mul, hP g, hQ g]
    simp
  | succ n ih =>
    intro k l p q P Q hkl hP hQ g
    rw [gcomm_mul]
    apply IsDiffOp.add
    · cases l with
      | zero => rw [show gcomm q Q g = 0 from hQ g, mul_zero]; exact IsDiffOp.zero _ _
      | succ l => exact (ih k l p (q + g.par) P _ (by omega) hP (hQ g)).congr_par (by ring)
    · cases k with
      | zero => rw [show gcomm p P g = 0 from hP g, zero_mul, smul_zero]; exact IsDiffOp.zero _ _
      | succ k => exact ((ih k l (p + g.par) q _ Q (by omega) (hP g) hQ).smul _).congr_par (by ring)

/-- Products of differential operators add orders. -/
theorem IsDiffOp.mul {k l p q : ℕ} {P Q : Module.End ℂ W} (hP : IsDiffOp k p P)
    (hQ : IsDiffOp l q Q) : IsDiffOp (k + l) (p + q) (P * Q) :=
  isDiffOp_mul_aux (k + l) k l p q P Q rfl hP hQ

/-! ## Commutators with left multiplications -/

/-- Products of lists of generators. -/
def prodGen : List Gen → W
  | [] => 1
  | g :: gs => g.elt * prodGen gs

/-- Total parity of a list of generators. -/
def parGen : List Gen → ℕ
  | [] => 0
  | g :: gs => g.par + parGen gs

theorem isPar_prodGen (gs : List Gen) : IsPar (parGen gs) (prodGen gs) := by
  induction gs with
  | nil => simp [IsPar, prodGen, parGen]
  | cons g gs ih => exact (isPar_gen g).mul ih

/-- Linear combinations of products of generators of total parity `s`. -/
inductive SpanGP (s : ℕ) : W → Prop
  | prod (gs : List Gen) (h : parGen gs = s) : SpanGP s (prodGen gs)
  | zero : SpanGP s 0
  | add {x y : W} : SpanGP s x → SpanGP s y → SpanGP s (x + y)
  | smul (r : ℂ) {x : W} : SpanGP s x → SpanGP s (r • x)

theorem SpanGP.isPar {s : ℕ} {y : W} (h : SpanGP s y) : IsPar s y := by
  induction h with
  | prod gs h => exact h ▸ isPar_prodGen gs
  | zero => exact IsPar.zero s
  | add _ _ hx hy => exact hx.add hy
  | smul r _ hx => exact hx.smul r

theorem lmul_mul (x y : W) : lmul (x * y) = lmul x * lmul y := by
  apply LinearMap.ext; intro z; simp [mul_assoc]

theorem lmul_one : lmul (1 : W) = 1 := by
  apply LinearMap.ext; intro z; simp

theorem lmul_add (x y : W) : lmul (x + y) = lmul x + lmul y := by
  apply LinearMap.ext; intro z; simp [add_mul]

theorem lmul_smul (r : ℂ) (x : W) : lmul (r • x) = r • lmul x := by
  apply LinearMap.ext; intro z; simp

theorem lmul_zero : lmul (0 : W) = 0 := by
  apply LinearMap.ext; intro z; simp

theorem scomm_mul_right (q r s : ℕ) (B X Y : Module.End ℂ W) :
    scomm q (r + s) B (X * Y) =
      scomm q r B X * Y + ((-1 : ℂ) ^ (q * r)) • (X * scomm q s B Y) := by
  simp only [scomm, sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc, smul_sub, smul_smul,
    ← pow_add, mul_assoc]
  rw [show q * r + q * s = q * (r + s) by ring]
  abel

theorem scomm_add_right (q s : ℕ) (B X Y : Module.End ℂ W) :
    scomm q s B (X + Y) = scomm q s B X + scomm q s B Y := by
  simp only [scomm, mul_add, add_mul, smul_add]; abel

theorem scomm_smul_right (q s : ℕ) (r : ℂ) (B X : Module.End ℂ W) :
    scomm q s B (r • X) = r • scomm q s B X := by
  simp only [scomm, mul_smul_comm, smul_mul_assoc, smul_sub, smul_comm r]

theorem scomm_zero_right (q s : ℕ) (B : Module.End ℂ W) : scomm q s B 0 = 0 := by
  simp [scomm]

/-- An operator of order zero graded-commutes with left multiplication by any product of
generators. -/
theorem IsDiffOp.scomm_prodGen_zero {q : ℕ} {B : Module.End ℂ W} (hB : IsDiffOp 0 q B)
    (gs : List Gen) : scomm q (parGen gs) B (lmul (prodGen gs)) = 0 := by
  induction gs with
  | nil => simp [scomm, prodGen, parGen, lmul_one]
  | cons g gs ih =>
    rw [prodGen, parGen, lmul_mul, scomm_mul_right, ← gcomm_eq_scomm, hB g, ih]
    simp

theorem IsDiffOp.scomm_spanGP_zero {q s : ℕ} {B : Module.End ℂ W} (hB : IsDiffOp 0 q B)
    {y : W} (hy : SpanGP s y) : scomm q s B (lmul y) = 0 := by
  induction hy with
  | prod gs h => exact h ▸ hB.scomm_prodGen_zero gs
  | zero => rw [lmul_zero, scomm_zero_right]
  | add _ _ hx hy => rw [lmul_add, scomm_add_right, hx, hy, add_zero]
  | smul r _ hx => rw [lmul_smul, scomm_smul_right, hx, smul_zero]

/-- The L-lemma: commutators with products of generators lower the order by one. -/
theorem IsDiffOp.scomm_prodGen {l q : ℕ} {B : Module.End ℂ W} (hB : IsDiffOp (l + 1) q B)
    (gs : List Gen) : IsDiffOp l (q + parGen gs) (scomm q (parGen gs) B (lmul (prodGen gs))) := by
  induction gs with
  | nil =>
    rw [show scomm q (parGen []) B (lmul (prodGen [])) = 0 by simp [scomm, prodGen, parGen, lmul_one]]
    exact IsDiffOp.zero _ _
  | cons g gs ih =>
    rw [prodGen, parGen, lmul_mul, scomm_mul_right, ← gcomm_eq_scomm]
    apply IsDiffOp.add
    · have h := (hB g).mul ((isPar_prodGen gs).isDiffOp_lmul)
      rw [add_zero] at h
      exact h.congr_par (by ring)
    · have h := ((isPar_gen g).isDiffOp_lmul).mul ih
      rw [zero_add] at h
      exact (h.smul _).congr_par (by ring)

theorem IsDiffOp.scomm_spanGP {l q s : ℕ} {B : Module.End ℂ W} (hB : IsDiffOp (l + 1) q B)
    {y : W} (hy : SpanGP s y) : IsDiffOp l (q + s) (scomm q s B (lmul y)) := by
  induction hy with
  | prod gs h => exact h ▸ hB.scomm_prodGen gs
  | zero => rw [lmul_zero, scomm_zero_right]; exact IsDiffOp.zero _ _
  | add _ _ hx hy => rw [lmul_add, scomm_add_right]; exact hx.add hy
  | smul r _ hx => rw [lmul_smul, scomm_smul_right]; exact hx.smul r

/-! ## Commutators with derivations -/

theorem neg_one_pow_two_mul_add (a b : ℕ) : (-1 : ℂ) ^ (2 * a + b) = (-1 : ℂ) ^ b := by
  rw [pow_add, pow_mul]; simp

/-- Super-Jacobi for the graded commutator with a left multiplication. -/
theorem gcomm_scomm (p q : ℕ) (A B : Module.End ℂ W) (g : Gen) :
    gcomm (p + q) (scomm p q A B) g =
      scomm p (q + g.par) A (gcomm q B g) -
        ((-1 : ℂ) ^ (p * q)) • scomm q (p + g.par) B (gcomm p A g) := by
  set C := lmul g.elt
  set r := g.par
  simp only [gcomm_eq_scomm, scomm, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub,
    smul_smul, ← pow_add, mul_assoc]
  have e1 : (-1 : ℂ) ^ (p * q + (q * (p + r) + p * r)) = (-1 : ℂ) ^ (q * r + p * r) := by
    rw [show p * q + (q * (p + r) + p * r) = 2 * (p * q) + (q * r + p * r) by ring,
      neg_one_pow_two_mul_add]
  have e2 : (-1 : ℂ) ^ (p * q + q * (p + r)) = (-1 : ℂ) ^ (q * r) := by
    rw [show p * q + q * (p + r) = 2 * (p * q) + q * r by ring, neg_one_pow_two_mul_add]
  have e3 : (-1 : ℂ) ^ (p * q + p * r) = (-1 : ℂ) ^ (p * (q + r)) := by
    rw [show p * q + p * r = p * (q + r) by ring]
  have e4 : (-1 : ℂ) ^ (p * (q + r) + q * r) = (-1 : ℂ) ^ ((p + q) * r + p * q) := by
    rw [show p * (q + r) + q * r = (p + q) * r + p * q by ring]
  rw [e1, e2, e3, e4, show (p + q) * r = q * r + p * r by ring]
  abel

/-- The graded commutator of a derivation with an operator of order `≤ l` has order `≤ l`. -/
theorem IsDer.scomm_isDiffOp {p : ℕ} {D : Module.End ℂ W} (hD : IsDer p D)
    (himg : ∀ g : Gen, SpanGP (p + g.par) (D g.elt)) {l q : ℕ} {Q : Module.End ℂ W}
    (hQ : IsDiffOp l q Q) : IsDiffOp l (p + q) (scomm p q D Q) := by
  induction l generalizing q Q with
  | zero =>
    intro g
    rw [gcomm_scomm, hQ g, scomm_zero_right, hD.gcomm_eq g,
      (show IsDiffOp 0 q Q from hQ).scomm_spanGP_zero (himg g)]
    simp
  | succ l ih =>
    intro g
    rw [gcomm_scomm, hD.gcomm_eq g]
    apply IsDiffOp.sub
    · exact (ih (hQ g)).congr_par (by ring)
    · exact ((hQ.scomm_spanGP (himg g)).smul _).congr_par (by ring)

end KhanSL2.StrongMacdonald
