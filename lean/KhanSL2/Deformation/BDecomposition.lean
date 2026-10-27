module

public import KhanSL2.Deformation.SplitGradings

@[expose] public section

/-!
# Decomposition of cochains along `b`-monomials

Every cochain is uniquely `Σ_s x_s · s` over `b`-monomials `s`, with pure-`c` coefficients
`x_s = coefB s x` (`sum_coefB`, `coefB_mul_single`). Derivations acting only on the `c` modes act
coefficientwise (`coefB_comm`). This is the Künneth decomposition used for `d_c`-exactness.
-/

noncomputable section

namespace KhanSL2

open Deformation

/-- The `b`-modes of a monomial. -/
def bPart (t : ExteriorMonomial) : ExteriorMonomial := t.filter (fun m => m.isB = true)

/-- The `c`-modes of a monomial. -/
def cPart (t : ExteriorMonomial) : ExteriorMonomial := t.filter (fun m => m.isC = true)

theorem Mode.isC_eq_false_iff (m : Mode) : m.isC = false ↔ m.isB = true := by
  cases m <;> simp [Mode.isC, Mode.isB]

theorem cPart_union_bPart (t : ExteriorMonomial) : cPart t ∪ bPart t = t := by
  ext m
  simp only [cPart, bPart, Finset.mem_union, Finset.mem_filter]
  cases m <;> simp [Mode.isB, Mode.isC]

theorem disjoint_cPart_bPart (t : ExteriorMonomial) : Disjoint (cPart t) (bPart t) := by
  rw [Finset.disjoint_left]
  intro m h1 h2
  simp only [cPart, bPart, Finset.mem_filter] at h1 h2
  cases m <;> simp_all [Mode.isB, Mode.isC]

theorem cPart_isC (t : ExteriorMonomial) : ∀ m ∈ cPart t, m.isC = true :=
  fun _ hm => (Finset.mem_filter.mp hm).2

theorem bPart_isB (t : ExteriorMonomial) : ∀ m ∈ bPart t, m.isB = true :=
  fun _ hm => (Finset.mem_filter.mp hm).2

theorem bPart_union {t s : ExteriorMonomial} (ht : ∀ m ∈ t, m.isC = true)
    (hs : ∀ m ∈ s, m.isB = true) : bPart (t ∪ s) = s := by
  ext m
  simp only [bPart, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨h | h, hb⟩
    · have := ht m h
      cases m <;> simp_all [Mode.isB, Mode.isC]
    · exact h
  · intro h; exact ⟨Or.inr h, hs m h⟩

theorem cPart_union {t s : ExteriorMonomial} (ht : ∀ m ∈ t, m.isC = true)
    (hs : ∀ m ∈ s, m.isB = true) : cPart (t ∪ s) = t := by
  ext m
  simp only [cPart, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨h | h, hc⟩
    · exact h
    · have := hs m h
      cases m <;> simp_all [Mode.isB, Mode.isC]
  · intro h; exact ⟨Or.inl h, ht m h⟩

theorem disjoint_of_pure {t s : ExteriorMonomial} (ht : ∀ m ∈ t, m.isC = true)
    (hs : ∀ m ∈ s, m.isB = true) : Disjoint t s := by
  rw [Finset.disjoint_left]
  intro m h1 h2
  have := ht m h1
  have := hs m h2
  cases m <;> simp_all [Mode.isB, Mode.isC]

/-- The sign of splitting a monomial into its `c` and `b` parts. -/
def cbSign (t : ExteriorMonomial) : ℂ := (-1) ^ inversionCount (cPart t) (bPart t)

theorem sign_mul_self (k : ℕ) : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; norm_num

theorem single_mul_single (s t : ExteriorMonomial) (r : ℂ) :
    Finsupp.single s r * Finsupp.single t 1 = r • monomialWedge s t := by
  rw [cochain_mul_eq_wedge]
  simp [wedge, wedgeLinear, Finsupp.linearCombination_single]

theorem single_eq_cbSign_mul (t : ExteriorMonomial) :
    Finsupp.single t (1 : ℂ) =
      cbSign t • (Finsupp.single (cPart t) 1 * Finsupp.single (bPart t) 1) := by
  rw [single_mul_single, monomialWedge, if_pos (disjoint_cPart_bPart t), cPart_union_bPart,
    one_smul, Finsupp.smul_single, smul_eq_mul, cbSign, sign_mul_self]

theorem single_mul_single_pure {t s : ExteriorMonomial} (ht : ∀ m ∈ t, m.isC = true)
    (hs : ∀ m ∈ s, m.isB = true) (r : ℂ) :
    Finsupp.single t r * Finsupp.single s 1 =
      (r * (-1) ^ inversionCount t s) • Finsupp.single (t ∪ s) 1 := by
  rw [single_mul_single, monomialWedge, if_pos (disjoint_of_pure ht hs), Finsupp.smul_single,
    Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one]

/-! ## The coefficients -/

/-- **The coefficient of the `b`-monomial `s`**, a pure-`c` cochain. -/
def coefB (s : ExteriorMonomial) : Cochain →ₗ[ℂ] Cochain :=
  Finsupp.linearCombination ℂ
    (fun t => if bPart t = s then cbSign t • Finsupp.single (cPart t) 1 else 0)

theorem coefB_single (s t : ExteriorMonomial) (r : ℂ) :
    coefB s (Finsupp.single t r) =
      if bPart t = s then (r * cbSign t) • Finsupp.single (cPart t) 1 else 0 := by
  simp only [coefB, Finsupp.linearCombination_single]
  split_ifs <;> simp [smul_smul]

theorem coefB_mem_pureC (s : ExteriorMonomial) (x : Cochain) : coefB s x ∈ pureIn Mode.isC := by
  rw [← x.sum_single]
  simp only [Finsupp.sum, map_sum]
  apply (pureIn _).sum_mem
  intro t _
  rw [coefB_single]
  split_ifs
  · exact (pureIn _).smul_mem _ (single_mem_pureIn (cPart_isC t) 1)
  · exact (pureIn _).zero_mem

theorem coefB_eq_zero {s : ExteriorMonomial} {x : Cochain} (h : ∀ t ∈ x.support, bPart t ≠ s) :
    coefB s x = 0 := by
  rw [← x.sum_single]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_eq_zero
  intro t ht
  rw [coefB_single, if_neg (h t ht)]

theorem coefB_single_mul {t s : ExteriorMonomial} (ht : ∀ m ∈ t, m.isC = true)
    (hs : ∀ m ∈ s, m.isB = true) (r : ℂ) (s' : ExteriorMonomial) :
    coefB s' (Finsupp.single t r * Finsupp.single s 1) =
      if s = s' then Finsupp.single t r else 0 := by
  rw [single_mul_single_pure ht hs, map_smul, coefB_single, bPart_union ht hs, cPart_union ht hs]
  split_ifs
  · rw [smul_smul, cbSign, cPart_union ht hs, bPart_union ht hs, one_mul, mul_assoc,
      sign_mul_self, mul_one, Finsupp.smul_single, smul_eq_mul, mul_one]
  · rw [smul_zero]

/-- **Uniqueness**: the coefficients of `u · s` for pure-`c` `u`. -/
theorem coefB_mul_single {u : Cochain} (hu : u ∈ pureIn Mode.isC) {s : ExteriorMonomial}
    (hs : ∀ m ∈ s, m.isB = true) (s' : ExteriorMonomial) :
    coefB s' (u * Finsupp.single s 1) = if s = s' then u else 0 := by
  conv_lhs => rw [← u.sum_single]
  simp only [Finsupp.sum, Finset.sum_mul, map_sum]
  rw [Finset.sum_congr rfl (fun t ht => coefB_single_mul (mem_pureIn_iff.mp hu t ht) hs (u t) s')]
  split_ifs
  · exact u.sum_single
  · simp

theorem sum_coefB_single (t : ExteriorMonomial) (r : ℂ) (I : Finset ExteriorMonomial)
    (hI : bPart t ∈ I) :
    ∑ s ∈ I, coefB s (Finsupp.single t r) * Finsupp.single s 1 = Finsupp.single t r := by
  rw [Finset.sum_eq_single (bPart t)]
  · rw [coefB_single, if_pos rfl, smul_mul_assoc, mul_smul, ← single_eq_cbSign_mul,
      Finsupp.smul_single, smul_eq_mul, mul_one]
  · intro s _ hs
    rw [coefB_single, if_neg (Ne.symm hs), zero_mul]
  · intro h; exact absurd hI h

/-- **Reconstruction** from the coefficients. -/
theorem sum_coefB (x : Cochain) (I : Finset ExteriorMonomial)
    (hI : ∀ t ∈ x.support, bPart t ∈ I) :
    ∑ s ∈ I, coefB s x * Finsupp.single s 1 = x := by
  conv_rhs => rw [← x.sum_single]
  conv_lhs => rw [← x.sum_single]
  simp only [Finsupp.sum, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t ht => sum_coefB_single t (x t) I (hI t ht)

theorem bPart_mem_image (x : Cochain) : ∀ t ∈ x.support, bPart t ∈ x.support.image bPart :=
  fun _ ht => Finset.mem_image_of_mem _ ht

theorem isB_of_mem_image {x : Cochain} {s : ExteriorMonomial} (hs : s ∈ x.support.image bPart) :
    ∀ m ∈ s, m.isB = true := by
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hs
  exact bPart_isB t

/-- **Coefficientwise action** of operators that act on the `c` modes only. -/
theorem coefB_comm (E : Cochain →ₗ[ℂ] Cochain) (hE : ∀ u ∈ pureIn Mode.isC, E u ∈ pureIn Mode.isC)
    (hmul : ∀ u (s : ExteriorMonomial), (∀ m ∈ s, m.isB = true) →
      E (u * Finsupp.single s 1) = E u * Finsupp.single s 1)
    (s : ExteriorMonomial) (x : Cochain) : coefB s (E x) = E (coefB s x) := by
  set I := x.support.image bPart
  have hx := sum_coefB x I (bPart_mem_image x)
  conv_lhs => rw [← hx]
  rw [map_sum, Finset.sum_congr rfl (fun s' hs' => hmul _ s' (isB_of_mem_image hs')), map_sum,
    Finset.sum_congr rfl (fun s' hs' =>
      coefB_mul_single (hE _ (coefB_mem_pureC s' x)) (isB_of_mem_image hs') s)]
  rw [Finset.sum_ite_eq']
  split_ifs with hs
  · rfl
  · rw [coefB_eq_zero (fun t ht h => hs (by rw [← h]; exact bPart_mem_image x t ht)), map_zero]

/-! ## Derivations on the `c` modes -/

theorem extendDerivation_mul_bmonomial_odd (f : Mode → Cochain)
    (hD : IsOddDer (extendDerivation f)) (hf : ∀ m, m.isB = true → f m = 0) (u : Cochain)
    {s : ExteriorMonomial} (hs : ∀ m ∈ s, m.isB = true) :
    extendDerivation f (u * Finsupp.single s 1) = extendDerivation f u * Finsupp.single s 1 := by
  rw [hD.mul, extendDerivation_pureIn_zero f hf (single_mem_pureIn hs 1), mul_zero, add_zero]

theorem extendDerivation_mul_bmonomial_even (f : Mode → Cochain)
    (hE : IsEvenDer (extendDerivation f)) (hf : ∀ m, m.isB = true → f m = 0) (u : Cochain)
    {s : ExteriorMonomial} (hs : ∀ m ∈ s, m.isB = true) :
    extendDerivation f (u * Finsupp.single s 1) = extendDerivation f u * Finsupp.single s 1 := by
  rw [hE.mul, extendDerivation_pureIn_zero f hf (single_mem_pureIn hs 1), mul_zero, add_zero]

theorem dCGen_of_isB (m : Mode) (h : m.isB = true) : dCGen m = 0 :=
  dCGen_of_not m ((Mode.isC_eq_false_iff m).mpr h)

theorem coefB_dC (s : ExteriorMonomial) (x : Cochain) : coefB s (dC x) = dC (coefB s x) :=
  coefB_comm dC (fun _ hu => extendDerivation_mem_pureIn dCGen (fun m _ => dCGen_mem_pureIn m) hu)
    (fun u _ hs => extendDerivation_mul_bmonomial_odd dCGen isOddDer_dC dCGen_of_isB u hs) s x

theorem coefB_LC (e : Fin 3) (s : ExteriorMonomial) (x : Cochain) :
    coefB s (LC e x) = LC e (coefB s x) :=
  coefB_comm (LC e) (fun _ hu => colorActionOn_mem_pureIn colorStable_isC e hu)
    (fun u _ hs => extendDerivation_mul_bmonomial_even _ (isEvenDer_colorActionOn _ e)
      (fun m hm => by simp [((Mode.isC_eq_false_iff m).mpr hm)]) u hs) s x

/-! ## Degrees -/

theorem coefB_mem_fine {D : ℤ × ℤ × ℤ × ℤ} {x : Cochain} (hx : x ∈ gPiece fine D)
    (s : ExteriorMonomial) : coefB s x ∈ gPiece fine (D - gdeg fine s) := by
  rw [← x.sum_single]
  simp only [Finsupp.sum, map_sum]
  apply (gPiece _ _).sum_mem
  intro t ht
  rw [coefB_single]
  split_ifs with h
  · apply (gPiece _ _).smul_mem
    have hD : gdeg fine t = D := (mem_gPiece_iff fine).mp hx t ht
    have hsplit := gdeg_union fine (disjoint_cPart_bPart t)
    rw [cPart_union_bPart, h] at hsplit
    have : D - gdeg fine s = gdeg fine (cPart t) := by rw [← hD, hsplit]; abel
    rw [this]
    exact single_mem_gPiece fine _ 1
  · exact (gPiece _ _).zero_mem

theorem gdeg_fine_pureC {t : ExteriorMonomial} (ht : ∀ m ∈ t, m.isC = true) :
    gdeg fine t = ((t.card : ℤ), 0, ((monomialDegree t).2.2), 0) := by
  simp only [gdeg, monomialDegree]
  rw [Finset.sum_congr rfl (fun m hm => show fine m = (1, 0, (m.weight : ℤ), 0) by
    have := ht m hm
    cases m with
    | b j a => simp [Mode.isC] at this
    | c j a => simp [fine, Mode.bCount, Mode.tcDeg, Mode.tbDeg, Mode.weight])]
  simp only [Prod.ext_iff, Prod.fst_sum, Prod.snd_sum, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.sum_const_zero, true_and, and_true, Nat.cast_sum, mul_zero]

theorem monomialDegree_pureC {t : ExteriorMonomial} (ht : ∀ m ∈ t, m.isC = true) :
    monomialDegree t = ((t.card : ℤ), 0, (monomialDegree t).2.2) := by
  simp only [monomialDegree, Prod.mk.injEq, true_and, and_true]
  rw [Finset.sum_eq_zero (fun m hm => by
    have := ht m hm
    cases m with
    | b j a => simp [Mode.isC] at this
    | c j a => rfl)]
  simp

/-- A pure-`c` cochain of fine degree `(N, B, S, T_b)` lies in `cochainPiece (N, 0, S)`. -/
theorem pureC_mem_cochainPiece {u : Cochain} (hu : u ∈ pureIn Mode.isC)
    {D : ℤ × ℤ × ℤ × ℤ} (hD : u ∈ gPiece fine D) : u ∈ cochainPiece (D.1, 0, D.2.2.1) := by
  intro t ht
  have hc := mem_pureIn_iff.mp hu t ht
  have hfine : gdeg fine t = D := (mem_gPiece_iff fine).mp hD t ht
  rw [gdeg_fine_pureC hc] at hfine
  change monomialDegree t = _
  rw [monomialDegree_pureC hc, ← hfine]

/-- A cochain with no `b`-modes is pure-`c`, of fine degree `(N, 0, S, 0)`. -/
theorem pureC_of_cochainPiece {u : Cochain} {N S : ℤ} (hu : u ∈ cochainPiece (N, 0, S)) :
    u ∈ pureIn Mode.isC ∧ u ∈ gPiece fine (N, 0, S, 0) := by
  have hc : ∀ t ∈ u.support, ∀ m ∈ t, m.isC = true := by
    intro t ht m hm
    have h := hu ht
    simp only [Set.mem_setOf_eq, monomialDegree, Prod.mk.injEq] at h
    have h0 : (∑ m ∈ t, m.bCount : ℕ) = 0 := by exact_mod_cast h.2.1
    have := (Finset.sum_eq_zero_iff.mp h0) m hm
    cases m with
    | b j a => simp [Mode.bCount] at this
    | c j a => rfl
  refine ⟨mem_pureIn_iff.mpr hc, (mem_gPiece_iff fine).mpr fun t ht => ?_⟩
  rw [gdeg_fine_pureC (hc t ht)]
  have h := hu ht
  change monomialDegree t = _ at h
  have h1 : (t.card : ℤ) = N := by
    have := congrArg Prod.fst h
    simpa [monomialDegree] using this
  rw [h, h1]

end KhanSL2
