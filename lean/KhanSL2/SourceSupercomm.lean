module

public import KhanSL2.Source
public import KhanSL2.PVA
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Supercommutativity of the presented source algebra

The homogeneous commutation law follows from the generator relations.  No
normal-form assertion or assumption of a PVA structure is used.
-/

namespace KhanSL2

@[simp] theorem koszulSign_zero_left (d : Degree) :
    koszulSign 0 d = 1 := by
  simp [koszulSign]

@[simp] theorem koszulSign_zero_right (d : Degree) :
    koszulSign d 0 = 1 := by
  simp [koszulSign]

theorem koszulSign_add_left (d e f : Degree) :
    koszulSign (d + e) f = koszulSign d f * koszulSign e f := by
  have hd : (d.1 * f.1) % 2 = 0 ∨ (d.1 * f.1) % 2 = 1 := by omega
  have he : (e.1 * f.1) % 2 = 0 ∨ (e.1 * f.1) % 2 = 1 := by omega
  rcases hd with hd | hd <;> rcases he with he | he <;>
    norm_num [koszulSign, add_mul, Int.add_emod, hd, he]

theorem koszulSign_add_right (d e f : Degree) :
    koszulSign d (e + f) = koszulSign d e * koszulSign d f := by
  have he : (d.1 * e.1) % 2 = 0 ∨ (d.1 * e.1) % 2 = 1 := by omega
  have hf : (d.1 * f.1) % 2 = 0 ∨ (d.1 * f.1) % 2 = 1 := by omega
  rcases he with he | he <;> rcases hf with hf | hf <;>
    norm_num [koszulSign, mul_add, Int.add_emod, he, hf]

namespace Source

open SourcePresentation

attribute [local instance] FreeAlgebra.Pre.hasCoeGenerator
  FreeAlgebra.Pre.hasCoeSemiring FreeAlgebra.Pre.hasMul
  FreeAlgebra.Pre.hasAdd FreeAlgebra.Pre.hasZero FreeAlgebra.Pre.hasOne
  FreeAlgebra.Pre.hasSMul

private theorem commutation_mul_left {a b c : Source} {s t : ℂ}
    (ha : a * c = s • (c * a)) (hb : b * c = t • (c * b)) :
    (a * b) * c = (s * t) • (c * (a * b)) := by
  calc
    (a * b) * c = a * (b * c) := mul_assoc _ _ _
    _ = a * (t • (c * b)) := by rw [hb]
    _ = t • ((a * c) * b) := by rw [mul_smul_comm, mul_assoc]
    _ = t • ((s • (c * a)) * b) := by rw [ha]
    _ = (s * t) • (c * (a * b)) := by
      rw [smul_mul_assoc, smul_smul, mul_assoc, mul_comm t s]

private theorem commutation_mul_right {a b c : Source} {s t : ℂ}
    (hb : a * b = s • (b * a)) (hc : a * c = t • (c * a)) :
    a * (b * c) = (s * t) • ((b * c) * a) := by
  calc
    a * (b * c) = (a * b) * c := (mul_assoc _ _ _).symm
    _ = (s • (b * a)) * c := by rw [hb]
    _ = s • (b * (a * c)) := by rw [smul_mul_assoc, mul_assoc]
    _ = s • (b * (t • (c * a))) := by rw [hc]
    _ = (s * t) • ((b * c) * a) := by
      rw [mul_smul_comm, smul_smul, mul_assoc]

private theorem commutation_homogeneous_right (d : Degree) (a : Source)
    (hx : ∀ i, a * X i = koszulSign d (2, 1, (i : ℤ) + 2) • (X i * a))
    (hy : ∀ i, a * Y i = koszulSign d (3, 3, (i : ℤ) + 3) • (Y i * a))
    {e : Degree} {b : Expression} (hb : Homogeneous e b) :
    a * mk b = koszulSign d e • (mk b * a) := by
  induction hb with
  | zero e => simp
  | scalar r =>
    simp only [koszulSign_zero_right, one_smul]
    change a * algebraMap ℂ Source r = algebraMap ℂ Source r * a
    exact (Algebra.commutes r a).symm
  | x i => exact hx i
  | y i => exact hy i
  | add hb hc ib ic => simpa only [mk_add, mul_add, add_mul, smul_add] using congrArg₂ (· + ·) ib ic
  | @mul e f b c hb hc ib ic =>
    simpa only [mk_mul, koszulSign_add_right] using commutation_mul_right ib ic

theorem homogeneous_supercomm {d e : Degree} {a b : Expression}
    (ha : Homogeneous d a) (hb : Homogeneous e b) :
    mk a * mk b = koszulSign d e • (mk b * mk a) := by
  induction ha with
  | zero d => simp
  | scalar r =>
    simp only [koszulSign_zero_left, one_smul]
    change algebraMap ℂ Source r * mk b = mk b * algebraMap ℂ Source r
    exact Algebra.commutes r (mk b)
  | x i =>
    apply commutation_homogeneous_right _ (X i) _ _ hb
    · intro j
      simpa [koszulSign] using X_mul_X i j
    · intro j
      simpa [koszulSign] using X_mul_Y i j
  | y i =>
    apply commutation_homogeneous_right _ (Y i) _ _ hb
    · intro j
      simpa [koszulSign] using (X_mul_Y j i).symm
    · intro j
      simpa [koszulSign] using Y_mul_Y i j
  | add ha hc ia ic =>
    simpa only [mk_add, add_mul, mul_add, smul_add] using congrArg₂ (· + ·) ia ic
  | @mul d f a c ha hc ia ic =>
    simpa only [mk_mul, koszulSign_add_left] using commutation_mul_left ia ic

/-- The full homogeneous supercommutation law in the differential quotient. -/
theorem supercomm {d e : Degree} {a b : Source}
    (ha : a ∈ piece d) (hb : b ∈ piece e) :
    a * b = koszulSign d e • (b * a) := by
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  exact homogeneous_supercomm ha hb

end Source
end KhanSL2
