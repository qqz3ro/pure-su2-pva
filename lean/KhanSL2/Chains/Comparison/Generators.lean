module

public import KhanSL2.Chains.Comparison.Transfer

@[expose] public section

/-!
# Structure constants on generators

The four generator identities that feed `transfer`. In words: on generators, `q` is
minus the transpose of the bracket of `𝔩₊` with `𝔩₊ ⋉ ε𝔩`, and the color action is
minus the transpose of the adjoint action of the constants.
-/

noncomputable section

namespace KhanSL2.Current

open FiniteExterior

/-! ## The Levi-Civita symbol -/

theorem epsilon_cyclic (a b c : Fin 3) : epsilon a b c = epsilon b c a := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [epsilon]

theorem epsilon_swap23 (a b c : Fin 3) : epsilon a c b = -epsilon a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [epsilon]

/-! ## Pairings of generators -/

theorem pairing_generator_generator (m n : Mode) :
    pairing (generator m) (generator n) = if m = n then 1 else 0 := by
  rw [show generator m = Finsupp.single {m} (1 : ℂ) from rfl,
    show generator n = Finsupp.single {n} (1 : ℂ) from rfl, pairing_single_single]
  by_cases h : m = n
  · subst h; simp
  · simp [h, Finset.singleton_inj]

theorem generator_mul_generator (x y : Mode) :
    generator x * generator y =
      if x = y then 0 else
        Finsupp.single {x, y} (if y.code < x.code then (-1 : ℂ) else 1) := by
  change FiniteExterior.wedge GeneratorOrder.code (FiniteExterior.generator x)
    (FiniteExterior.generator y) = _
  rw [FiniteExterior.generator, FiniteExterior.generator, FiniteExterior.wedge_monomial,
    FiniteExterior.monomialWedge]
  by_cases hxy : x = y
  · subst hxy; simp
  · have hd : Disjoint ({x} : Finset Mode) {y} := Finset.disjoint_singleton.mpr hxy
    rw [if_pos hd, if_neg hxy, Finset.singleton_union]
    congr 1
    simp only [FiniteExterior.inversionCount, Finset.sum_singleton, Finset.filter_singleton]
    change (-1 : ℂ) ^ (if y.code < x.code then ({y} : Finset Mode) else ∅).card = _
    split_ifs <;> simp

/-- `⟨e^x e^y, e_u e_v⟩ = δ_xu δ_yv - δ_xv δ_yu`. -/
theorem pairing_generator_mul (x y u v : Mode) :
    pairing (generator x * generator y) (generator u * generator v) =
      (if x = u ∧ y = v then 1 else 0) - (if x = v ∧ y = u then 1 else 0) := by
  have hcode : Function.Injective Mode.code := GeneratorOrder.code_injective
  rw [generator_mul_generator, generator_mul_generator]
  by_cases hxy : x = y
  · subst hxy
    simp only [if_true, map_zero, LinearMap.zero_apply]
    by_cases h1 : x = u <;> by_cases h2 : x = v <;> simp_all
  by_cases huv : u = v
  · subst huv
    simp only [if_neg hxy, if_true, map_zero]
    by_cases h1 : x = u <;> by_cases h2 : y = u <;> simp_all
  simp only [if_neg hxy, if_neg huv, pairing_single_single]
  by_cases hset : ({x, y} : Finset Mode) = {u, v}
  · rw [if_pos hset]
    have hset' : ({x, y} : Set Mode) = {u, v} := by
      rw [← Finset.coe_pair, ← Finset.coe_pair, hset]
    rcases Set.pair_eq_pair_iff.mp hset' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have : ¬(x = y ∧ y = x) := fun h => hxy h.1
      split_ifs <;> simp_all
    · have hne : x.code ≠ y.code := fun h => hxy (hcode h)
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · simp [hlt, not_lt.mpr hlt.le, hxy, Ne.symm hxy]
      · simp [hlt, not_lt.mpr hlt.le, hxy, Ne.symm hxy]
  · rw [if_neg hset]
    have h1 : ¬(x = u ∧ y = v) := by rintro ⟨rfl, rfl⟩; exact hset rfl
    have h2 : ¬(x = v ∧ y = u) := by rintro ⟨rfl, rfl⟩; exact hset (Finset.pair_comm _ _)
    simp [h1, h2]

/-! ## The color action on generators -/

theorem pairing_colorGenerator_c (a : Fin 3) (m : Mode) (i : ℕ) (b : Fin 3) :
    pairing (colorGenerator a m) (generator (.c i b)) =
      -∑ c : Fin 3, epsilon a b c * pairing (generator m) (generator (.c i c)) := by
  cases m with
  | c J d =>
    simp only [colorGenerator, Mode.color, Mode.recolor, map_sum, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, pairing_generator_generator, Mode.c.injEq,
      smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hJ : J = i
    · subst hJ
      simp [epsilon_swap23 a d b, eq_comm]
    · simp [hJ]
  | b J d =>
    simp [colorGenerator, Mode.color, Mode.recolor, pairing_generator_generator]

theorem pairing_colorGenerator_b (a : Fin 3) (m : Mode) (i : ℕ) (b : Fin 3) :
    pairing (colorGenerator a m) (generator (.b i b)) =
      -∑ c : Fin 3, epsilon a b c * pairing (generator m) (generator (.b i c)) := by
  cases m with
  | b J d =>
    simp only [colorGenerator, Mode.color, Mode.recolor, map_sum, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, pairing_generator_generator, Mode.b.injEq,
      smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hJ : J = i
    · subst hJ
      simp [epsilon_swap23 a d b, eq_comm]
    · simp [hJ]
  | c J d =>
    simp [colorGenerator, Mode.color, Mode.recolor, pairing_generator_generator]

/-! ## The differential on generators -/

theorem range_sum_aux (J i j : ℕ) (e e' : ℂ) :
    ((-(1 / 2) * if j < J then if J - 1 - j = i then e else 0 else 0) -
        -(1 / 2) * if i < J then if J - 1 - i = j then e' else 0 else 0) =
      if J = i + j + 1 then -(1 / 2) * e + (1 / 2) * e' else 0 := by
  by_cases hJ : J = i + j + 1
  · have h1 : j < J := by omega
    have h2 : J - 1 - j = i := by omega
    have h3 : i < J := by omega
    have h4 : J - 1 - i = j := by omega
    rw [if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos hJ]
    ring
  · rw [if_neg hJ]
    split_ifs <;> first | (exfalso; omega) | ring

/-- `q` on generators against two `𝔩₊` generators. -/
theorem pairing_qGenerator_cc (m : Mode) (j i : ℕ) (a b : Fin 3) :
    pairing (qGenerator m) (generator (.c j a) * generator (.c i b)) =
      -∑ c : Fin 3, epsilon a b c * pairing (generator m) (generator (.c (i + j + 1) c)) := by
  cases m with
  | c J d =>
    simp only [qGenerator, ← cochain_mul_eq_wedge, map_sum, map_smul, map_neg,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.neg_apply, pairing_generator_mul,
      pairing_generator_generator, Mode.c.injEq, smul_eq_mul, mul_sub, mul_ite, mul_one,
      mul_zero, Finset.sum_sub_distrib]
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.sum_const_zero, Finset.mem_univ, if_true, Finset.mem_range]
    rw [range_sum_aux]
    split_ifs
    · rw [epsilon_swap23 d a b, epsilon_cyclic d a b]; ring
    · simp
  | b J d =>
    simp [qGenerator, ← cochain_mul_eq_wedge, map_sum, map_smul, pairing_generator_mul,
      pairing_generator_generator]

/-- `q` on generators against an `𝔩₊` generator and an `ε𝔩` generator. -/
theorem pairing_qGenerator_cb (m : Mode) (j i : ℕ) (a b : Fin 3) :
    pairing (qGenerator m) (generator (.c j a) * generator (.b i b)) =
      -∑ c : Fin 3, epsilon a b c * pairing (generator m) (generator (.b (i + j + 1) c)) := by
  cases m with
  | b J d =>
    simp only [qGenerator, ← cochain_mul_eq_wedge, map_sum, map_smul, map_neg,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.neg_apply, pairing_generator_mul,
      pairing_generator_generator, Mode.c.injEq, Mode.b.injEq, smul_eq_mul, mul_sub, mul_ite,
      mul_one, mul_zero, Finset.sum_sub_distrib, reduceCtorEq, and_false, false_and, if_false,
      Finset.sum_const_zero, sub_zero]
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.sum_const_zero, Finset.mem_univ, if_true, Finset.mem_range]
    by_cases hJ : J = i + j + 1
    · have h1 : j < J := by omega
      have h2 : J - 1 - j = i := by omega
      rw [if_pos h1, if_pos h2, if_pos hJ, epsilon_cyclic d a b]
    · have : ¬(j < J ∧ J - 1 - j = i) := by omega
      rw [if_neg hJ]
      split_ifs <;> first | (exfalso; omega) | simp
  | c J d =>
    simp [qGenerator, ← cochain_mul_eq_wedge, map_sum, map_smul, pairing_generator_mul,
      pairing_generator_generator]

end KhanSL2.Current
