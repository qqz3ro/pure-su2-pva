module

public import KhanSL2.StrongMacdonald.Algebra

@[expose] public section

/-!
# Differential operators of bounded order on the super-polynomial algebra

An operator `P` of parity `p` has order at most `k` if its iterated graded commutators
with left multiplication by `k+1` generators vanish. Such operators are determined by
their values on products of at most `k` generators. This is the super-commutative
version of `BGG.ExteriorSecondOrder`, stated for all orders.
-/

noncomputable section
open scoped BigOperators

namespace KhanSL2.StrongMacdonald

/-- The generators of `W`, with their parity. -/
inductive Gen
  | s (g : SMode)
  | p (m : PMode)
  deriving DecidableEq

namespace Gen

def elt : Gen → W
  | .s g => sig g
  | .p m => psi m

def par : Gen → ℕ
  | .s _ => 0
  | .p _ => 1

end Gen

/-- Left multiplication. -/
def lmul (x : W) : Module.End ℂ W := LinearMap.mulLeft ℂ x

@[simp] theorem lmul_apply (x y : W) : lmul x y = x * y := rfl

/-- The graded commutator of an operator of parity `p` with a generator. -/
def gcomm (p : ℕ) (P : Module.End ℂ W) (g : Gen) : Module.End ℂ W :=
  P * lmul g.elt - ((-1 : ℂ) ^ (p * g.par)) • (lmul g.elt * P)

theorem gcomm_apply (p : ℕ) (P : Module.End ℂ W) (g : Gen) (x : W) :
    gcomm p P g x = P (g.elt * x) - ((-1 : ℂ) ^ (p * g.par)) • (g.elt * P x) := rfl

/-- Operators of parity `p` and order at most `k`. -/
def IsDiffOp : ℕ → ℕ → Module.End ℂ W → Prop
  | 0, p, P => ∀ g, gcomm p P g = 0
  | k + 1, p, P => ∀ g, IsDiffOp k (p + g.par) (gcomm p P g)

theorem gcomm_sub (p : ℕ) (P Q : Module.End ℂ W) (g : Gen) :
    gcomm p (P - Q) g = gcomm p P g - gcomm p Q g := by
  simp only [gcomm, sub_mul, mul_sub, smul_sub]
  abel

theorem gcomm_add (p : ℕ) (P Q : Module.End ℂ W) (g : Gen) :
    gcomm p (P + Q) g = gcomm p P g + gcomm p Q g := by
  simp only [gcomm, add_mul, mul_add, smul_add]
  abel

theorem gcomm_smul (p : ℕ) (r : ℂ) (P : Module.End ℂ W) (g : Gen) :
    gcomm p (r • P) g = r • gcomm p P g := by
  simp only [gcomm, smul_mul_assoc, mul_smul_comm, smul_sub, smul_comm r]

theorem gcomm_zero (p : ℕ) (g : Gen) : gcomm p 0 g = 0 := by
  simp [gcomm]

theorem IsDiffOp.sub {k p : ℕ} {P Q : Module.End ℂ W} (hP : IsDiffOp k p P)
    (hQ : IsDiffOp k p Q) : IsDiffOp k p (P - Q) := by
  induction k generalizing p P Q with
  | zero => intro g; rw [gcomm_sub, hP g, hQ g, sub_zero]
  | succ k ih => intro g; rw [gcomm_sub]; exact ih (hP g) (hQ g)

theorem IsDiffOp.add {k p : ℕ} {P Q : Module.End ℂ W} (hP : IsDiffOp k p P)
    (hQ : IsDiffOp k p Q) : IsDiffOp k p (P + Q) := by
  induction k generalizing p P Q with
  | zero => intro g; rw [gcomm_add, hP g, hQ g, add_zero]
  | succ k ih => intro g; rw [gcomm_add]; exact ih (hP g) (hQ g)

theorem IsDiffOp.smul {k p : ℕ} {P : Module.End ℂ W} (r : ℂ) (hP : IsDiffOp k p P) :
    IsDiffOp k p (r • P) := by
  induction k generalizing p P with
  | zero => intro g; rw [gcomm_smul, hP g, smul_zero]
  | succ k ih => intro g; rw [gcomm_smul]; exact ih (hP g)

theorem IsDiffOp.zero (k p : ℕ) : IsDiffOp k p 0 := by
  induction k generalizing p with
  | zero => intro g; exact gcomm_zero p g
  | succ k ih => intro g; rw [gcomm_zero]; exact ih _

theorem IsDiffOp.sum {k p : ℕ} {ι : Type*} (s : Finset ι) (P : ι → Module.End ℂ W)
    (hP : ∀ i ∈ s, IsDiffOp k p (P i)) : IsDiffOp k p (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsDiffOp.zero k p
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hP a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hP i (Finset.mem_insert_of_mem hi))

theorem IsDiffOp.mono {k p : ℕ} {P : Module.End ℂ W} (hP : IsDiffOp k p P) :
    IsDiffOp (k + 1) p P := by
  induction k generalizing p P with
  | zero => intro g; rw [hP g]; exact IsDiffOp.zero 0 _
  | succ k ih => intro g; exact ih (hP g)

theorem IsDiffOp.mono_le {k l p : ℕ} {P : Module.End ℂ W} (hP : IsDiffOp k p P)
    (hkl : k ≤ l) : IsDiffOp l p P := by
  induction hkl with
  | refl => exact hP
  | step _ ih => exact ih.mono

/-! ## Extensionality -/

/-- Elements that are products of at most `k` generators (in a fixed order). -/
def GenProduct : ℕ → W → Prop
  | 0, x => x = (1 : W)
  | k + 1, x => x = (1 : W) ∨ ∃ (g : Gen) (y : W), GenProduct k y ∧ x = g.elt * y

theorem GenProduct.one (k : ℕ) : GenProduct k 1 := by
  cases k with
  | zero => exact (rfl : (1 : W) = 1)
  | succ k => exact Or.inl rfl

theorem GenProduct.gen_mul {k : ℕ} (g : Gen) {y : W} (hy : GenProduct k y) :
    GenProduct (k + 1) (g.elt * y) :=
  Or.inr ⟨g, y, hy, rfl⟩

theorem GenProduct.mono {k : ℕ} {x : W} (hx : GenProduct k x) : GenProduct (k + 1) x := by
  induction k generalizing x with
  | zero => exact Or.inl hx
  | succ k ih =>
    rcases hx with hx | ⟨g, y, hy, rfl⟩
    · exact Or.inl hx
    · exact Or.inr ⟨g, y, ih hy, rfl⟩

/-- An operator that graded-commutes with every generator and kills `1` is zero. -/
theorem eq_zero_of_gcomm {p : ℕ} {P : Module.End ℂ W} (hP : ∀ g, gcomm p P g = 0)
    (h1 : P 1 = 0) : P = 0 := by
  apply LinearMap.ext
  intro x
  refine induction_gen (P := fun x => P x = 0) ?_ h1 ?_ ?_ ?_ ?_ x
  · simp
  · intro x y hx hy; simp [hx, hy]
  · intro r x hx; simp [hx]
  · intro g x hx
    have h := LinearMap.congr_fun (hP (.s g)) x
    rw [gcomm_apply, hx] at h
    simpa [Gen.elt] using h
  · intro m x hx
    have h := LinearMap.congr_fun (hP (.p m)) x
    rw [gcomm_apply, hx] at h
    simpa [Gen.elt] using h

/-- An operator of order `≤ k` vanishing on all products of at most `k` generators is zero. -/
theorem IsDiffOp.eq_zero {k p : ℕ} {P : Module.End ℂ W} (hP : IsDiffOp k p P)
    (hvan : ∀ x, GenProduct k x → P x = 0) : P = 0 := by
  induction k generalizing p P with
  | zero => exact eq_zero_of_gcomm hP (hvan 1 (GenProduct.one 0))
  | succ k ih =>
    apply eq_zero_of_gcomm (p := p) _ (hvan 1 (GenProduct.one _))
    intro g
    apply ih (hP g)
    intro x hx
    rw [gcomm_apply, hvan _ (hx.gen_mul g), hvan x hx.mono]
    simp

end KhanSL2.StrongMacdonald
