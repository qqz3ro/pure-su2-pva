module

public import KhanSL2.SourceHamiltonian
public import KhanSL2.SourceGrading

@[expose] public section

/-! # Grading and parity of the source generator Hamiltonians -/

noncomputable section

namespace KhanSL2.Source

open SourcePresentation LambdaPolynomial

attribute [local instance] FreeAlgebra.Pre.hasCoeGenerator
  FreeAlgebra.Pre.hasCoeSemiring FreeAlgebra.Pre.hasMul
  FreeAlgebra.Pre.hasAdd FreeAlgebra.Pre.hasZero FreeAlgebra.Pre.hasOne
  FreeAlgebra.Pre.hasSMul

theorem jetAction_degree (g : ℕ → Source) (k B s : ℤ)
    (hg : ∀ i : ℕ, g i ∈ piece (k, B, (i : ℤ) + s))
    (a b : ℂ) (i n : ℕ) :
    jetAction g a b i n ∈ piece (k, B, (i : ℤ) + s + 1 - (n : ℤ)) := by
  induction i generalizing n with
  | zero =>
    rcases n with _ | (_ | n)
    · simpa [jetAction, add_comm] using (piece (k, B, (1 : ℤ) + s)).smul_mem a (hg 1)
    · simpa [jetAction] using (piece (k, B, (0 : ℤ) + s)).smul_mem b (hg 0)
    · simp [jetAction]
  | succ i hi =>
    rw [jetAction_succ, rightTranslation_apply, Finsupp.add_apply, mapCoefficients_apply]
    cases n with
    | zero =>
      rw [shift_apply_zero, add_zero]
      have hdeg :
          (k, B, (i : ℤ) + s + 1 - (0 : ℤ)) + (0, 0, 1) =
            (k, B, ((i + 1 : ℕ) : ℤ) + s + 1 - (0 : ℤ)) := by
        ext <;> simp; omega
      simpa only [Nat.cast_zero, hdeg] using translation_mem (hi 0)
    | succ n =>
      rw [shift_apply_succ]
      have hleft :
          (k, B, (i : ℤ) + s + 1 - ((n + 1 : ℕ) : ℤ)) + (0, 0, 1) =
            (k, B, ((i + 1 : ℕ) : ℤ) + s + 1 - ((n + 1 : ℕ) : ℤ)) := by
        ext <;> simp; omega
      have hright :
          (k, B, (i : ℤ) + s + 1 - (n : ℤ)) =
            (k, B, ((i + 1 : ℕ) : ℤ) + s + 1 - ((n + 1 : ℕ) : ℤ)) := by
        ext <;> simp; omega
      apply (piece _).add_mem
      · rw [← hleft]
        exact translation_mem (hi (n + 1))
      · rw [← hright]
        exact hi n

theorem XX_degree (i n : ℕ) :
    XX i n ∈ piece (Degree.bracket (2, 1, 2) (2, 1, (i : ℤ) + 2) n) := by
  have hd : Degree.bracket (2, 1, 2) (2, 1, (i : ℤ) + 2) n =
      (2, 1, (i : ℤ) + 2 + 1 - (n : ℤ)) := by
    ext <;> simp [Degree.bracket]; omega
  rw [hd]
  exact jetAction_degree X 2 1 2 X_mem 1 2 i n

theorem XY_degree (i n : ℕ) :
    XY i n ∈ piece (Degree.bracket (2, 1, 2) (3, 3, (i : ℤ) + 3) n) := by
  have hd : Degree.bracket (2, 1, 2) (3, 3, (i : ℤ) + 3) n =
      (3, 3, (i : ℤ) + 3 + 1 - (n : ℤ)) := by
    ext <;> simp [Degree.bracket]; omega
  rw [hd]
  exact jetAction_degree Y 3 3 3 Y_mem 1 3 i n

theorem YX_degree (i n : ℕ) :
    YX i n ∈ piece (Degree.bracket (3, 3, 3) (2, 1, (i : ℤ) + 2) n) := by
  have hd : Degree.bracket (3, 3, 3) (2, 1, (i : ℤ) + 2) n =
      (3, 3, (i : ℤ) + 3 + 1 - (n : ℤ)) := by
    ext <;> simp [Degree.bracket]; omega
  rw [hd]
  exact jetAction_degree Y 3 3 3 Y_mem 2 3 i n

theorem bracket_degree_add_right (h d e : Degree) (n : ℕ) :
    h.bracket (d + e) n = h.bracket d n + e := by
  ext <;> simp [Degree.bracket] <;> omega

theorem bracket_degree_add_left (h d e : Degree) (n : ℕ) :
    h.bracket (d + e) n = d + h.bracket e n := by
  ext <;> simp [Degree.bracket] <;> omega

theorem parity_mem {d : Degree} {a : Source} (ha : a ∈ piece d) :
    parity a ∈ piece d := by
  rw [parity_of_mem ha]
  exact (piece d).smul_mem _ ha

@[simp] theorem DX_scalar (r : ℂ) : DX (algebraMap ℂ Source r) = 0 := by
  rfl

@[simp] theorem DY_scalar (r : ℂ) : DY (algebraMap ℂ Source r) = 0 := by
  rfl

theorem DX_homogeneous_degree {d : Degree} {a : Expression}
    (ha : Homogeneous d a) (n : ℕ) :
    DX (mk a) n ∈ piece (Degree.bracket (2, 1, 2) d n) := by
  induction ha with
  | zero d => simp
  | scalar _ => simp
  | x i => exact XX_degree i n
  | y i => exact XY_degree i n
  | @add d a b ha hb ia ib =>
    simpa only [mk_add, map_add, Finsupp.add_apply] using (piece _).add_mem ia ib
  | @mul d e a b ha hb ia ib =>
    rw [mk_mul, DX_mul, Finsupp.add_apply, mulRight_apply, mulLeft_apply]
    change DX (mk a) n * mk b + mk a * DX (mk b) n ∈ _
    apply (piece _).add_mem
    · rw [bracket_degree_add_right]
      exact mul_mem ia ⟨b, hb, rfl⟩
    · rw [bracket_degree_add_left]
      exact mul_mem ⟨a, ha, rfl⟩ ib

theorem DY_homogeneous_degree {d : Degree} {a : Expression}
    (ha : Homogeneous d a) (n : ℕ) :
    DY (mk a) n ∈ piece (Degree.bracket (3, 3, 3) d n) := by
  induction ha with
  | zero d => simp
  | scalar _ => simp
  | x i => exact YX_degree i n
  | y i => simpa only [mk_y, DY_Y, Finsupp.zero_apply] using (piece _).zero_mem
  | @add d a b ha hb ia ib =>
    simpa only [mk_add, map_add, Finsupp.add_apply] using (piece _).add_mem ia ib
  | @mul d e a b ha hb ia ib =>
    rw [mk_mul, DY_mul, Finsupp.add_apply, mulRight_apply, mulLeft_apply]
    change DY (mk a) n * mk b + parity (mk a) * DY (mk b) n ∈ _
    apply (piece _).add_mem
    · rw [bracket_degree_add_right]
      exact mul_mem ia ⟨b, hb, rfl⟩
    · rw [bracket_degree_add_left]
      exact mul_mem (parity_mem ⟨a, ha, rfl⟩) ib

/-- Every coefficient of the even generator Hamiltonian has the specified degree. -/
theorem DX_degree {d : Degree} {a : Source} (ha : a ∈ piece d) (n : ℕ) :
    DX a n ∈ piece (Degree.bracket (2, 1, 2) d n) := by
  obtain ⟨a, ha, rfl⟩ := ha
  exact DX_homogeneous_degree ha n

/-- Every coefficient of the odd generator Hamiltonian has the specified degree. -/
theorem DY_degree {d : Degree} {a : Source} (ha : a ∈ piece d) (n : ℕ) :
    DY a n ∈ piece (Degree.bracket (3, 3, 3) d n) := by
  obtain ⟨a, ha, rfl⟩ := ha
  exact DY_homogeneous_degree ha n

theorem koszulSign_bracket_X (d : Degree) (n : ℕ) :
    koszulSign (1, 0, 0) (Degree.bracket (2, 1, 2) d n) =
      koszulSign (1, 0, 0) d := by
  simp [koszulSign, Degree.bracket]

theorem koszulSign_bracket_Y (d : Degree) (n : ℕ) :
    koszulSign (1, 0, 0) (Degree.bracket (3, 3, 3) d n) =
      -koszulSign (1, 0, 0) d := by
  have hd : d.1 % 2 = 0 ∨ d.1 % 2 = 1 := by omega
  rcases hd with hd | hd <;>
    norm_num [koszulSign, Degree.bracket, Int.add_emod, Int.sub_emod, hd]

theorem DX_parity_of_mem {d : Degree} {a : Source} (ha : a ∈ piece d) :
    DX (parity a) = mapCoefficients parity.toLinearMap (DX a) := by
  ext n
  rw [parity_of_mem ha, map_smul, Finsupp.smul_apply, mapCoefficients_apply]
  change _ = parity (DX a n)
  rw [parity_of_mem (DX_degree ha n), koszulSign_bracket_X]

theorem DY_parity_of_mem {d : Degree} {a : Source} (ha : a ∈ piece d) :
    DY (parity a) = -mapCoefficients parity.toLinearMap (DY a) := by
  ext n
  rw [parity_of_mem ha, map_smul, Finsupp.smul_apply, Finsupp.neg_apply,
    mapCoefficients_apply]
  change _ = -parity (DY a n)
  rw [parity_of_mem (DY_degree ha n), koszulSign_bracket_Y, neg_smul, neg_neg]

/-- The even generator Hamiltonian preserves parity. -/
theorem DX_parity (a : Source) :
    DX (parity a) = mapCoefficients parity.toLinearMap (DX a) := by
  have ha : a ∈ ⨆ d, piece d := by rw [piece_iSup_eq_top]; trivial
  refine Submodule.iSup_induction piece
    (motive := fun a => DX (parity a) = mapCoefficients parity.toLinearMap (DX a))
    ha ?_ ?_ ?_
  · intro d a ha
    exact DX_parity_of_mem ha
  · simp
  · intro a b ha hb
    simp only [map_add, mapCoefficients_add, ha, hb]

/-- The odd generator Hamiltonian reverses parity. -/
theorem DY_parity (a : Source) :
    DY (parity a) = -mapCoefficients parity.toLinearMap (DY a) := by
  have ha : a ∈ ⨆ d, piece d := by rw [piece_iSup_eq_top]; trivial
  refine Submodule.iSup_induction piece
    (motive := fun a => DY (parity a) = -mapCoefficients parity.toLinearMap (DY a))
    ha ?_ ?_ ?_
  · intro d a ha
    exact DY_parity_of_mem ha
  · simp
  · intro a b ha hb
    simp only [map_add, mapCoefficients_add, ha, hb, neg_add]

end KhanSL2.Source
