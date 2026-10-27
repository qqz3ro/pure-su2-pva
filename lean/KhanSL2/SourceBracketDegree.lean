module

public import KhanSL2.SourceBracketQuotient
public import KhanSL2.SourcePolynomialDegree
public import KhanSL2.SourceGeneration

@[expose] public section

/-! The precise three-component degree of every source bracket coefficient. -/

noncomputable section

namespace KhanSL2.Source

open LambdaPolynomial SourceBracketOperators BracketAction

theorem bracket_degree_sub (d e : Degree) (n : ℕ) :
    d.bracket e 0 - (0, 0, (n : ℤ)) = d.bracket e n := by
  ext <;> simp [Degree.bracket]

theorem bracket_polynomialHomogeneous {d : Degree} {a : Source}
    (ha : a ∈ piece d) :
    ∀ e b, b ∈ piece e → PolynomialHomogeneous (d.bracket e 0) (bracket a b) := by
  have h : a ∈ piece d ∧
      ∀ e b, b ∈ piece e → PolynomialHomogeneous (d.bracket e 0) (bracket a b) := by
    apply homogeneous_induction (P := fun d a => a ∈ piece d ∧
      ∀ e b, b ∈ piece e → PolynomialHomogeneous (d.bracket e 0) (bracket a b))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha
    · intro d
      refine ⟨(piece d).zero_mem, ?_⟩
      intro e b _
      simpa using PolynomialHomogeneous.zero (d.bracket e 0)
    · intro r
      refine ⟨?_, ?_⟩
      · rw [Algebra.algebraMap_eq_smul_one]
        exact (piece 0).smul_mem r one_mem
      · intro e b _
        rw [← mk_scalar, bracket_mk, rawBracket_scalar]
        change PolynomialHomogeneous _ 0
        exact PolynomialHomogeneous.zero _
    · refine ⟨X_mem 0, ?_⟩
      intro e b hb n
      rw [bracket_X0, bracket_degree_sub]
      exact DX_degree hb n
    · refine ⟨Y_mem 0, ?_⟩
      intro e b hb n
      rw [bracket_Y0, bracket_degree_sub]
      exact DY_degree hb n
    · intro d a b ha hb
      refine ⟨(piece d).add_mem ha.1 hb.1, ?_⟩
      intro e c hc
      simpa only [map_add, LinearMap.add_apply] using (ha.2 e c hc).add (hb.2 e c hc)
    · intro d e a b ha hb
      refine ⟨mul_mem ha.1 hb.1, ?_⟩
      intro f c hc
      rw [bracket_mul_first]
      change PolynomialHomogeneous _ (right b (bracket a (evenPart c)) +
        right (parity b) (bracket a (oddPart c)) + left a (bracket b c))
      have hright : d.bracket f 0 + e = (d + e).bracket f 0 := by
        ext <;> simp [Degree.bracket] <;> omega
      have hleft : d + e.bracket f 0 = (d + e).bracket f 0 := by
        ext <;> simp [Degree.bracket] <;> omega
      apply PolynomialHomogeneous.add
      · apply PolynomialHomogeneous.add
        · rw [← hright]
          exact (ha.2 f _ (evenPart_mem hc)).right hb.1
        · rw [← hright]
          exact (ha.2 f _ (oddPart_mem hc)).right (parity_mem hb.1)
      · rw [← hleft]
        exact PolynomialHomogeneous.left ha.1 (hb.2 f c hc)
    · intro d a ha
      refine ⟨translation_mem ha.1, ?_⟩
      intro e b hb
      rw [bracket_left_translation]
      have hd : (d + (0, 0, 1)).bracket e 0 = d.bracket e 0 + (0, 0, 1) := by
        ext <;> simp [Degree.bracket]; omega
      rw [hd]
      exact (ha.2 e b hb).shift.neg
  exact h.2

/-- All lambda coefficients have the degree specified by the existing PVA
definition, including its cohomological and B-degree shifts. -/
theorem bracket_degree (d e : Degree) (a b : Source) (n : ℕ)
    (ha : a ∈ piece d) (hb : b ∈ piece e) :
    bracket a b n ∈ piece (d.bracket e n) := by
  have h := bracket_polynomialHomogeneous ha e b hb n
  rwa [bracket_degree_sub] at h

end KhanSL2.Source
