module

public import KhanSL2.SourceBracketOperatorParity
public import KhanSL2.SourceHamiltonianDegree

@[expose] public section

/-! Total degree of source-valued lambda polynomials and bracket operators. -/

noncomputable section

namespace KhanSL2.Source

open LambdaPolynomial SourceBracketOperators

/-- Lambda has degree `(0,0,1)`. -/
def PolynomialHomogeneous (d : Degree) (p : LambdaPolynomial Source) : Prop :=
  ∀ n : ℕ, p n ∈ piece (d - (0, 0, (n : ℤ)))

namespace PolynomialHomogeneous

theorem zero (d : Degree) : PolynomialHomogeneous d 0 := by
  intro n
  exact (piece _).zero_mem

theorem add {d : Degree} {p q : LambdaPolynomial Source}
    (hp : PolynomialHomogeneous d p) (hq : PolynomialHomogeneous d q) :
    PolynomialHomogeneous d (p + q) := by
  intro n
  exact (piece _).add_mem (hp n) (hq n)

theorem smul {d : Degree} {p : LambdaPolynomial Source}
    (hp : PolynomialHomogeneous d p) (r : ℂ) :
    PolynomialHomogeneous d (r • p) := by
  intro n
  exact (piece _).smul_mem r (hp n)

theorem neg {d : Degree} {p : LambdaPolynomial Source}
    (hp : PolynomialHomogeneous d p) : PolynomialHomogeneous d (-p) := by
  intro n
  exact (piece _).neg_mem (hp n)

theorem single {d : Degree} {a : Source} (n : ℕ)
    (ha : a ∈ piece (d - (0, 0, (n : ℤ)))) :
    PolynomialHomogeneous d (Finsupp.single n a) := by
  intro j
  by_cases h : n = j
  · subst j
    simpa using ha
  · simp [Finsupp.single_apply, h]

theorem translation_pow_mem {d : Degree} {a : Source}
    (ha : a ∈ piece d) (n : ℕ) :
    (translation ^ n) a ∈ piece (d + (0, 0, (n : ℤ))) := by
  induction n with
  | zero =>
    change a ∈ piece (d + 0)
    simpa only [add_zero] using ha
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using translation_mem ih

theorem skew_single {d : Degree} {a : Source} (n : ℕ)
    (ha : a ∈ piece (d - (0, 0, (n : ℤ)))) :
    PolynomialHomogeneous d (K (Finsupp.single n a)) := by
  intro j
  rw [K_apply, skew_single_apply]
  by_cases h : j ≤ n
  · have hd : d - (0, 0, (n : ℤ)) + (0, 0, ((n - j : ℕ) : ℤ)) =
        d - (0, 0, (j : ℤ)) := by
      ext <;> simp [Nat.cast_sub h]
    apply (piece _).smul_mem
    rw [← hd]
    exact translation_pow_mem ha (n - j)
  · simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)]

theorem skew {d : Degree} {p : LambdaPolynomial Source}
    (hp : PolynomialHomogeneous d p) : PolynomialHomogeneous d (K p) := by
  intro j
  rw [← p.sum_single]
  simp only [Finsupp.sum, map_sum, Finset.sum_apply']
  apply (piece _).sum_mem
  intro n _
  exact skew_single n (hp n) j

theorem shift {d : Degree} {p : LambdaPolynomial Source}
    (hp : PolynomialHomogeneous d p) :
    PolynomialHomogeneous (d + (0, 0, 1)) (LambdaPolynomial.shift p) := by
  intro n
  cases n with
  | zero => simp
  | succ n =>
    rw [shift_apply_succ]
    have hd : d + (0, 0, 1) - (0, 0, ((n + 1 : ℕ) : ℤ)) =
        d - (0, 0, (n : ℤ)) := by
      ext <;> simp
    rw [hd]
    exact hp n

theorem mulLeft {d e : Degree} {a : Source} {p : LambdaPolynomial Source}
    (ha : a ∈ piece d) (hp : PolynomialHomogeneous e p) :
    PolynomialHomogeneous (d + e) (LambdaPolynomial.mulLeft sourceData a p) := by
  intro n
  rw [mulLeft_apply]
  change a * p n ∈ _
  simpa only [add_sub_assoc] using mul_mem ha (hp n)

theorem mulRight {d e : Degree} {a : Source} {p : LambdaPolynomial Source}
    (hp : PolynomialHomogeneous d p) (ha : a ∈ piece e) :
    PolynomialHomogeneous (d + e) (LambdaPolynomial.mulRight sourceData p a) := by
  intro n
  rw [mulRight_apply]
  change p n * a ∈ _
  have hd : (d - (0, 0, (n : ℤ))) + e = d + e - (0, 0, (n : ℤ)) := by
    abel
  simpa only [hd] using mul_mem (hp n) ha

theorem left {d e : Degree} {a : Source} {p : LambdaPolynomial Source}
    (ha : a ∈ piece d) (hp : PolynomialHomogeneous e p) :
    PolynomialHomogeneous (d + e) (SourceBracketOperators.left a p) := by
  rw [left_apply]
  exact (mulLeft ha hp.skew).skew

theorem right {d e : Degree} {a : Source} {p : LambdaPolynomial Source}
    (hp : PolynomialHomogeneous d p) (ha : a ∈ piece e) :
    PolynomialHomogeneous (d + e) (SourceBracketOperators.right a p) := by
  rw [right_apply]
  exact (mulRight hp.skew ha).skew

end PolynomialHomogeneous

theorem evenPart_mem {d : Degree} {a : Source} (ha : a ∈ piece d) :
    evenPart a ∈ piece d := by
  rw [evenPart_apply]
  exact (piece d).smul_mem _ ((piece d).add_mem ha (parity_mem ha))

theorem oddPart_mem {d : Degree} {a : Source} (ha : a ∈ piece d) :
    oddPart a ∈ piece d := by
  rw [oddPart_apply]
  exact (piece d).smul_mem _ ((piece d).sub_mem ha (parity_mem ha))

end KhanSL2.Source
