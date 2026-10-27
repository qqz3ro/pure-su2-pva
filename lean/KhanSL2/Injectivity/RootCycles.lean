module

public import KhanSL2.Injectivity.NewtonPolynomials
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Separating Cartan cycles with polynomial root coefficients

All constructions take place over an arbitrary commutative rational algebra.
The two root alphabets may therefore be the universal polynomial variables.
-/

@[expose] public section

noncomputable section

namespace KhanSL2.Injectivity

open Finset MvPolynomial

variable {σ R : Type*} [Fintype σ] [CommRing R] [Algebra ℚ R]

/-- Signed elementary coefficients evaluated on an alphabet of roots. -/
def rootElementary (u : σ → R) (k : ℕ) : R :=
  MvPolynomial.aeval u (signedElementary σ ℚ k)

/-- Power sums evaluated on an alphabet of roots. -/
def rootPowerSum (u : σ → R) (k : ℕ) : R :=
  MvPolynomial.aeval u (MvPolynomial.psum σ ℚ k)

@[simp] theorem rootElementary_zero (u : σ → R) : rootElementary u 0 = 1 := by
  simp [rootElementary]

theorem rootElementary_eq_zero (u : σ → R) {k : ℕ} (hk : Fintype.card σ < k) :
    rootElementary u k = 0 := by
  simp [rootElementary, signedElementary_eq_zero σ ℚ hk]

theorem rootPowerSum_eq_sum (u : σ → R) (k : ℕ) :
    rootPowerSum u k = ∑ i, u i ^ k := by
  simp [rootPowerSum, MvPolynomial.psum]

theorem rootElementary_eq_sum (u : σ → R) (k : ℕ) :
    rootElementary u k = (-1) ^ k * ∑ t ∈ univ.powersetCard k, ∏ i ∈ t, u i := by
  classical
  simp [rootElementary, signedElementary, MvPolynomial.esymm]

section Specialization

variable {S : Type*} [CommRing S] [Algebra ℚ S]

@[simp] theorem rootElementary_map (f : R →+* S) (u : σ → R) (k : ℕ) :
    f (rootElementary u k) = rootElementary (fun i => f (u i)) k := by
  classical
  simp [rootElementary_eq_sum, map_sum, map_prod]

@[simp] theorem rootPowerSum_map (f : R →+* S) (u : σ → R) (k : ℕ) :
    f (rootPowerSum u k) = rootPowerSum (fun i => f (u i)) k := by
  simp [rootPowerSum_eq_sum, map_sum]

/-- Scalar specialization of finite Cartan coefficient chains. -/
def mapCartanCoefficients (f : R →+* S) : (ℕ →₀ R) →ₛₗ[f] (ℕ →₀ S) where
  toFun := Finsupp.mapRange f (map_zero f)
  map_add' c d := by ext i; simp
  map_smul' r c := by ext i; simp [smul_eq_mul]

omit [Algebra ℚ R] [Algebra ℚ S] in
@[simp] theorem mapCartanCoefficients_apply (f : R →+* S) (c : ℕ →₀ R) (i : ℕ) :
    mapCartanCoefficients f c i = f (c i) := rfl

omit [Algebra ℚ R] [Algebra ℚ S] in
@[simp] theorem mapCartanCoefficients_single (f : R →+* S) (i : ℕ) :
    mapCartanCoefficients f (Finsupp.single i 1) = Finsupp.single i 1 := by
  ext j
  simp [Finsupp.single_apply]

end Specialization

theorem rootElementary_satisfiesNewton (u : σ → R) :
    SatisfiesNewton (rootElementary u) (rootPowerSum u) :=
  (signedElementary_satisfiesNewton σ ℚ).map (MvPolynomial.aeval u).toRingHom

/-- The finite Cartan coefficient chain for two alphabets. -/
def rootCycle (u v : σ → R) (k : ℕ) : ℕ →₀ R :=
  newtonCycle (rootElementary u) (rootPowerSum v) (fun j => Finsupp.single j 1) k

/-- The degree-one Koszul differential of the two root alphabets. -/
def rootDifferential (u v : σ → R) : (ℕ →₀ R) →ₗ[R] R :=
  Finsupp.linearCombination R (fun j => rootPowerSum u j - rootPowerSum v j)

/-- Every Newton cycle uses only the finitely many positive Cartan indices
`1, ..., k`, before any specialization of its coefficient variables. -/
theorem rootCycle_apply_eq_zero (u v : σ → R) (k i : ℕ) (hi : i = 0 ∨ k < i) :
    rootCycle u v k i = 0 := by
  let P : Submodule R (ℕ →₀ R) := LinearMap.ker (Finsupp.lapply i)
  have hmem : rootCycle u v k ∈ P := by
    apply newtonCycle_mem
    intro j hj hjk
    have hji : j ≠ i := by omega
    simp [P, Finsupp.single_apply, hji]
  exact hmem

@[simp] theorem rootCycle_apply_zero (u v : σ → R) (k : ℕ) :
    rootCycle u v k 0 = 0 := rootCycle_apply_eq_zero u v k 0 (Or.inl rfl)

/-- Evaluating the coefficient variables evaluates the actual finite cycle. -/
theorem rootCycle_map {S : Type*} [CommRing S] [Algebra ℚ S]
    (f : R →+* S) (u v : σ → R) (k : ℕ) :
    mapCartanCoefficients f (rootCycle u v k) =
      rootCycle (fun i => f (u i)) (fun i => f (v i)) k := by
  unfold rootCycle
  rw [semilinearMap_newtonCycle]
  simp

@[simp] theorem rootDifferential_single (u v : σ → R) (j : ℕ) :
    rootDifferential u v (Finsupp.single j 1) = rootPowerSum u j - rootPowerSum v j := by
  simp [rootDifferential]

/-- The exact differential identity, before diagonal specialization. -/
theorem rootDifferential_rootCycle (u v : σ → R) (k : ℕ) :
    rootDifferential u v (rootCycle u v k) = rootElementary u k - rootElementary v k := by
  apply map_newtonCycle
  · exact rootElementary_satisfiesNewton u
  · exact rootElementary_satisfiesNewton v
  · simp
  · intro j
    simp

/-- Every coefficient above the number of roots gives an actual closed chain. -/
theorem rootCycle_closed (u v : σ → R) {k : ℕ} (hk : Fintype.card σ < k) :
    rootDifferential u v (rootCycle u v k) = 0 := by
  rw [rootDifferential_rootCycle, rootElementary_eq_zero u hk,
    rootElementary_eq_zero v hk, sub_self]

/-- The coefficient identity used to insert these finite cycles into any
current-equivariant family of closed exterior chains. -/
theorem rootCycle_current_sum_eq_zero (u v : σ → R) {k : ℕ}
    (hk : Fintype.card σ < k) :
    (∑ j ∈ (rootCycle u v k).support,
      (rootPowerSum u j - rootPowerSum v j) * rootCycle u v k j) = 0 := by
  simpa [rootDifferential, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul,
    mul_comm] using rootCycle_closed u v hk

/-- Exact diagonal coefficients; the vanishing condition is proved before specialization. -/
theorem rootCycle_diagonal_apply (w : σ → R) (k i : ℕ) :
    rootCycle w w k i =
      if i = 0 then 0 else if i ≤ k then -rationalInvNat i * rootElementary w (k - i) else 0 :=
  newtonCycle_single_apply _ _ (rootElementary_satisfiesNewton w) k i

/-- Vieta's formula in the signed elementary convention used by the cycles. -/
theorem rootElementary_sum_eq_prod (w : σ → R) (z : R) :
    (∑ j ∈ range (Fintype.card σ + 1), rootElementary w j * z ^ (Fintype.card σ - j)) =
      ∏ i, (z - w i) := by
  classical
  let roots : Multiset R := univ.val.map w
  have hv := congrArg (Polynomial.eval z) (Multiset.prod_X_sub_X_eq_sum_esymm roots)
  have he (j : ℕ) : rootElementary w j = (-1 : R) ^ j * roots.esymm j := by
    simp [rootElementary, signedElementary, MvPolynomial.aeval_esymm_eq_multiset_esymm, roots]
  simp only [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_apply,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one] at hv
  simp only [roots, Multiset.card_map, ← Finset.card_def, Finset.card_univ,
    Multiset.map_map, Function.comp_apply] at hv
  calc
    _ = ∑ j ∈ range (Fintype.card σ + 1),
          (-1 : R) ^ j * ((univ.val.map w).esymm j * z ^ (Fintype.card σ - j)) := by
      apply sum_congr rfl
      intro j _hj
      rw [he]
      dsimp [roots]
      ring
    _ = _ := by simpa only [← Finset.prod_eq_multiset_prod] using hv.symm

/-- The separating-cycle pairing, including its exact normalization. -/
theorem rootCycle_pairing (w : σ → R) (z : R) (n : ℕ) :
    cartanModePairing z (rootCycle w w (Fintype.card σ + 1 + n)) =
      -(z ^ n * ∏ i, (z - w i)) := by
  classical
  let k := Fintype.card σ + 1 + n
  change cartanModePairing z (rootCycle w w k) = _
  rw [rootCycle, cartanModePairing_newtonCycle _ _ (rootElementary_satisfiesNewton w)]
  congr 1
  have hreflect :
      (∑ j ∈ range k, rootElementary w (k - 1 - j) * z ^ j) =
        ∑ j ∈ range k, rootElementary w j * z ^ (k - 1 - j) := by
    calc
      _ = ∑ j ∈ range k,
            (fun l => rootElementary w l * z ^ (k - 1 - l)) (k - 1 - j) := by
        apply sum_congr rfl
        intro j hj
        have hj' := mem_range.mp hj
        dsimp only
        rw [show k - 1 - (k - 1 - j) = j by omega]
      _ = _ := sum_range_reflect (fun l => rootElementary w l * z ^ (k - 1 - l)) k
  rw [hreflect]
  have hsub : range (Fintype.card σ + 1) ⊆ range k := range_mono (by dsimp [k]; omega)
  rw [← sum_subset hsub]
  · rw [← rootElementary_sum_eq_prod w z, mul_sum]
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    have hexp : k - 1 - j = n + (Fintype.card σ - j) := by dsimp [k]; omega
    rw [hexp, pow_add]
    ring
  · intro j _hj hj'
    have hj' : Fintype.card σ < j := by
      simp only [mem_range] at hj'
      omega
    rw [rootElementary_eq_zero w hj', zero_mul]

end KhanSL2.Injectivity
