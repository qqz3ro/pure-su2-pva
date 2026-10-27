module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.LinearAlgebra.Matrix.Reindex

@[expose] public section

/-!
# Splitting a monic polynomial along a coprime factorization, by norms

Let `g ∈ R[u]` be monic of degree `n` over a commutative ring `R`, and `E ∈ R[u]` idempotent
modulo `g` (for `g ∣ f₁ f₂` and `α f₁ + β f₂ = 1`, take `E = β f₂`). With the norm
`N_g(h) = det(h · : R[u]/(g) → R[u]/(g))` (`normMod`, computed in the basis `1, …, u^{n-1}`):

* `c(y) = N_g((1 - E) + y E) ∈ R[y]` (`cpoly`). From `c(y) c(y') = c(y y')` and `c(1) = 1`, its
  coefficients are orthogonal idempotents summing to `1` (`cpoly_coeff_mul`, `cpoly_sum_coeff`).
* `G(t) = N_g((1 - E) + (t - u) E)` (`Gpoly`), the "characteristic polynomial of `u` on the
  `E`-part". If `c(y) = y^k`, then `G` is monic of degree `k` and `g ∣ G E`
  (Cayley–Hamilton for `μ (1 - E) + u E`, `split_core`), and `G_E G_{1-E} = g`.
* Consequently, on the component where `c(y) = y^k`, `g = g₁ g₂` with `g₁ ∣ α f₁`, `g₂ ∣ β f₂`
  (`split_one`), and this splitting is unique (`cpoly_of_split`).
* For the weighted pair `A W³ = f₁ f₂`, the splittings of `A` and `W` combine to
  `A₁ W₁³ = f₁`, `A₂ W₂³ = f₂`, and the degrees add up (`pair_split`).

This is the coefficient-coordinate form of the weighted-root splitting lemma of the depth paper
(§6): no roots and no symmetric-group invariants are needed.
-/

noncomputable section

open Polynomial

namespace KhanSL2.Collision.NormSplit

variable {R : Type*} [CommRing R]

/-- The matrix of multiplication by `h` on `C[u]/(g)` in the basis `1, u, …, u^{n-1}`. -/
def mulMat (n : ℕ) (g h : R[X]) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => ((h * X ^ (j : ℕ)) %ₘ g).coeff i

theorem mulMat_map {R' : Type*} [CommRing R'] (φ : R →+* R') (n : ℕ) {g : R[X]} (hg : g.Monic)
    (h : R[X]) : (mulMat n g h).map φ = mulMat n (g.map φ) (h.map φ) := by
  ext i j
  simp only [mulMat, Matrix.map_apply, Matrix.of_apply]
  rw [← Polynomial.coeff_map, Polynomial.map_modByMonic φ hg, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X]

/-- The `C`-algebra embedding `C[u]/(g) → Mat_n(C)`. -/
def mulMatHom {n : ℕ} {g : R[X]} (hg : g.Monic) (hn : g.natDegree = n) :
    AdjoinRoot g →ₐ[R] Matrix (Fin n) (Fin n) R :=
  (Matrix.reindexAlgEquiv R R (finCongr hn)).toAlgHom.comp
    (Algebra.leftMulMatrix (AdjoinRoot.powerBasisAux' hg))

theorem powerBasisAux'_apply {g : R[X]} (hg : g.Monic) (j : Fin g.natDegree) :
    AdjoinRoot.powerBasisAux' hg j = AdjoinRoot.root g ^ (j : ℕ) :=
  (AdjoinRoot.powerBasis' hg).basis_eq_pow j

theorem mulMatHom_mk {n : ℕ} {g : R[X]} (hg : g.Monic) (hn : g.natDegree = n) (h : R[X]) :
    mulMatHom hg hn (AdjoinRoot.mk g h) = mulMat n g h := by
  ext i j
  change (Matrix.reindex (finCongr hn) (finCongr hn)
    (Algebra.leftMulMatrix (AdjoinRoot.powerBasisAux' hg) (AdjoinRoot.mk g h))) i j = _
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [Algebra.leftMulMatrix_eq_repr_mul, AdjoinRoot.powerBasisAux'_repr_apply_to_fun,
    powerBasisAux'_apply, ← AdjoinRoot.mk_X, ← map_pow, ← map_mul, AdjoinRoot.modByMonicHom_mk]
  rfl


theorem mulMatHom_injective {n : ℕ} {g : R[X]} (hg : g.Monic) (hn : g.natDegree = n) :
    Function.Injective (mulMatHom hg hn) :=
  (Matrix.reindexAlgEquiv R R (finCongr hn)).injective.comp
    (Algebra.leftMulMatrix_injective (AdjoinRoot.powerBasisAux' hg))

section Basic

variable {n : ℕ} {g : R[X]} (hg : g.Monic) (hn : g.natDegree = n)
include hg hn

theorem mulMat_eq_hom (h : R[X]) : mulMat n g h = mulMatHom hg hn (AdjoinRoot.mk g h) :=
  (mulMatHom_mk hg hn h).symm

theorem mulMat_mul (a b : R[X]) : mulMat n g (a * b) = mulMat n g a * mulMat n g b := by
  simp only [mulMat_eq_hom hg hn, map_mul]

theorem mulMat_add (a b : R[X]) : mulMat n g (a + b) = mulMat n g a + mulMat n g b := by
  simp only [mulMat_eq_hom hg hn, map_add]

theorem mulMat_sub (a b : R[X]) : mulMat n g (a - b) = mulMat n g a - mulMat n g b := by
  simp only [mulMat_eq_hom hg hn, map_sub]

theorem mulMat_C (c : R) : mulMat n g (C c) = Matrix.scalar (Fin n) c := by
  rw [mulMat_eq_hom hg hn, AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq, AlgHom.commutes]
  rfl

theorem mulMat_one : mulMat n g 1 = 1 := by
  simp only [mulMat_eq_hom hg hn, map_one]

theorem mulMat_eq_of_dvd {a b : R[X]} (h : g ∣ a - b) : mulMat n g a = mulMat n g b := by
  rw [mulMat_eq_hom hg hn, mulMat_eq_hom hg hn, AdjoinRoot.mk_eq_mk.mpr h]

/-- **Cayley–Hamilton** for multiplication operators: `g ∣ χ_h(h)`. -/
theorem dvd_aeval_charpoly (h : R[X]) : g ∣ aeval h (mulMat n g h).charpoly := by
  rw [← AdjoinRoot.mk_eq_zero]
  apply mulMatHom_injective hg hn
  have hcomm : AdjoinRoot.mk g (aeval h (mulMat n g h).charpoly) =
      aeval (AdjoinRoot.mk g h) (mulMat n g h).charpoly := by
    rw [aeval_def, aeval_def, Polynomial.hom_eval₂, AdjoinRoot.algebraMap_eq]
    rfl
  rw [hcomm, ← Polynomial.aeval_algHom_apply, ← mulMat_eq_hom hg hn, Matrix.aeval_self_charpoly,
    map_zero]

end Basic

/-! ## The norm `N_g(h) = det (h · : R[u]/(g) → R[u]/(g))` -/

/-- The norm of `h` modulo `g`, computed in the basis `1, u, …, u^{n-1}`. -/
def normMod (n : ℕ) (g h : R[X]) : R := (mulMat n g h).det

section Norm

variable {n : ℕ} {g : R[X]}

theorem normMod_map {R' : Type*} [CommRing R'] (φ : R →+* R') (hg : g.Monic) (h : R[X]) :
    φ (normMod n g h) = normMod n (g.map φ) (h.map φ) := by
  rw [normMod, normMod, RingHom.map_det, RingHom.mapMatrix_apply, mulMat_map φ n hg]

variable (hg : g.Monic) (hn : g.natDegree = n)
include hg hn

theorem normMod_mul (a b : R[X]) : normMod n g (a * b) = normMod n g a * normMod n g b := by
  rw [normMod, mulMat_mul hg hn, Matrix.det_mul, normMod, normMod]

theorem normMod_C (c : R) : normMod n g (C c) = c ^ n := by
  rw [normMod, mulMat_C hg hn, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem normMod_one : normMod n g 1 = 1 := by
  rw [normMod, mulMat_one hg hn, Matrix.det_one]

theorem normMod_eq_of_dvd {a b : R[X]} (h : g ∣ a - b) : normMod n g a = normMod n g b := by
  rw [normMod, normMod, mulMat_eq_of_dvd hg hn h]

/-- The characteristic polynomial of multiplication by `h` is the norm of `t - h`. -/
theorem charpoly_mulMat (h : R[X]) :
    (mulMat n g h).charpoly = normMod n (g.map C) (C X - h.map C) := by
  have hg' : (g.map C).Monic := hg.map C
  have hn' : (g.map C).natDegree = n := by
    rw [natDegree_map_eq_of_injective Polynomial.C_injective, hn]
  rw [normMod, mulMat_sub hg' hn', mulMat_C hg' hn', ← mulMat_map C n hg, Matrix.charpoly]
  rfl

/-- The characteristic polynomial of `u` on `R[u]/(g)` is `g`. -/
theorem charpoly_mulMat_X : (mulMat n g X).charpoly = g := by
  nontriviality R
  have hP := Matrix.charpoly_monic (mulMat n g X)
  have hdvd := dvd_aeval_charpoly hg hn X
  rw [aeval_X_left_apply] at hdvd
  obtain ⟨q, hq⟩ := hdvd
  have hqm : q.Monic := hg.of_mul_monic_left (hq ▸ hP)
  have hdeg := congrArg natDegree hq
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hg.natDegree_mul hqm, hn] at hdeg
  have hq1 : q = 1 := hqm.natDegree_eq_zero.mp (by omega)
  rw [hq, hq1, mul_one]

end Norm


/-! ## Elements `x (1 - E) + y E` -/

/-- `x (1 - E) + y E`. -/
def pe (E x y : R[X]) : R[X] := x * (1 - E) + y * E

theorem pe_mul_pe_sub (E x y x' y' : R[X]) :
    pe E x y * pe E x' y' - pe E (x * x') (y * y') = (x - y) * (x' - y') * (E * E - E) := by
  unfold pe; ring

theorem pe_same (E x : R[X]) : pe E x x = x := by unfold pe; ring

theorem pe_compl (E x y : R[X]) : pe (1 - E) x y = pe E y x := by unfold pe; ring

theorem pe_map {S : Type*} [CommRing S] (φ : R →+* S) (E x y : R[X]) :
    (pe E x y).map φ = pe (E.map φ) (x.map φ) (y.map φ) := by
  simp only [pe, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one]

theorem map_idem_dvd {S : Type*} [CommRing S] (φ : R →+* S) {g E : R[X]} (hE : g ∣ E * E - E) :
    g.map φ ∣ E.map φ * E.map φ - E.map φ := by
  have := Polynomial.map_dvd φ hE
  rwa [Polynomial.map_sub, Polynomial.map_mul] at this

section PE

variable {n : ℕ} {g : R[X]} (hg : g.Monic) (hn : g.natDegree = n)
include hg hn

theorem normMod_pe_mul {E : R[X]} (hE : g ∣ E * E - E) (x y x' y' : R[X]) :
    normMod n g (pe E x y) * normMod n g (pe E x' y') = normMod n g (pe E (x * x') (y * y')) := by
  rw [← normMod_mul hg hn]
  apply normMod_eq_of_dvd hg hn
  rw [pe_mul_pe_sub]
  exact Dvd.dvd.mul_left hE _

end PE

/-! ## The idempotent polynomial `c(y) = N((1 - E) + y E)` and the factor `G(t)` -/

/-- `c(y) = N_g((1 - E) + y E)`; its coefficients are the orthogonal idempotents. -/
def cpoly (n : ℕ) (g E : R[X]) : R[X] := normMod n (g.map C) (pe (E.map C) 1 (C X))

/-- `G(t) = N_g((1 - E) + (t - u) E)`, the "characteristic polynomial of `u` on `E`". -/
def Gpoly (n : ℕ) (g E : R[X]) : R[X] := normMod n (g.map C) (pe (E.map C) 1 (C X - X))

section Apply

variable {n : ℕ} {g E : R[X]}

theorem cpoly_apply {S : Type*} [CommRing S] (ψ : R[X] →+* S) (θ : R →+* S) (hθ : ψ.comp C = θ)
    (hg : g.Monic) : ψ (cpoly n g E) = normMod n (g.map θ) (pe (E.map θ) 1 (C (ψ X))) := by
  rw [cpoly, normMod_map ψ (hg.map C), Polynomial.map_map, pe_map, Polynomial.map_map,
    Polynomial.map_one, Polynomial.map_C, hθ]

theorem Gpoly_apply {S : Type*} [CommRing S] (ψ : R[X] →+* S) (θ : R →+* S) (hθ : ψ.comp C = θ)
    (hg : g.Monic) : ψ (Gpoly n g E) = normMod n (g.map θ) (pe (E.map θ) 1 (C (ψ X) - X)) := by
  rw [Gpoly, normMod_map ψ (hg.map C), Polynomial.map_map, pe_map, Polynomial.map_map,
    Polynomial.map_one, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X, hθ]

theorem cpoly_map {S : Type*} [CommRing S] (φ : R →+* S) (hg : g.Monic) :
    (cpoly n g E).map φ = cpoly n (g.map φ) (E.map φ) := by
  have h := cpoly_apply (n := n) (E := E) (mapRingHom φ) (C.comp φ) (by ext; simp) hg
  rw [coe_mapRingHom] at h
  rw [h, cpoly, Polynomial.map_X, Polynomial.map_map, Polynomial.map_map]

theorem Gpoly_map {S : Type*} [CommRing S] (φ : R →+* S) (hg : g.Monic) :
    (Gpoly n g E).map φ = Gpoly n (g.map φ) (E.map φ) := by
  have h := Gpoly_apply (n := n) (E := E) (mapRingHom φ) (C.comp φ) (by ext; simp) hg
  rw [coe_mapRingHom] at h
  rw [h, Gpoly, Polynomial.map_X, Polynomial.map_map, Polynomial.map_map]

end Apply

omit [CommRing R] in
theorem natDegree_mapC {R : Type*} [CommRing R] {n : ℕ} {g : R[X]} (hn : g.natDegree = n) :
    (g.map (C : R →+* R[X])).natDegree = n := by
  rw [natDegree_map_eq_of_injective Polynomial.C_injective, hn]

section CPoly

variable {n : ℕ} {g E : R[X]} (hg : g.Monic) (hn : g.natDegree = n) (hE : g ∣ E * E - E)
include hg hn hE

theorem cpoly_mul_compl : cpoly n g E * cpoly n g (1 - E) = X ^ n := by
  have hE' := map_idem_dvd (C : R →+* R[X]) hE
  rw [cpoly, cpoly, Polynomial.map_sub, Polynomial.map_one, pe_compl,
    normMod_pe_mul (hg.map C) (natDegree_mapC hn) hE', one_mul, mul_one, pe_same,
    normMod_C (hg.map C) (natDegree_mapC hn)]

theorem Gpoly_mul_compl : Gpoly n g E * Gpoly n g (1 - E) = g := by
  have hE' := map_idem_dvd (C : R →+* R[X]) hE
  rw [Gpoly, Gpoly, Polynomial.map_sub, Polynomial.map_one, pe_compl,
    normMod_pe_mul (hg.map C) (natDegree_mapC hn) hE', one_mul, mul_one, pe_same]
  have h1 := charpoly_mulMat hg hn X
  rw [charpoly_mulMat_X hg hn, Polynomial.map_X] at h1
  exact h1.symm

omit hE in
theorem cpoly_eval_one : (cpoly n g E).eval 1 = 1 := by
  have h := cpoly_apply (n := n) (E := E) (evalRingHom 1) (RingHom.id R) (by ext; simp) hg
  rw [coe_evalRingHom] at h
  rw [h, Polynomial.map_id, Polynomial.map_id, eval_X, map_one, pe_same, normMod_one hg hn]


omit hE in
theorem cpoly_natDegree_le : (cpoly n g E).natDegree ≤ n := by
  have hg' := hg.map (C : R →+* R[X])
  have hn' := natDegree_mapC hn
  have hM : mulMat n (g.map C) (pe (E.map C) 1 (C X)) =
      (X : R[X]) • (mulMat n g E).map C + (mulMat n g (1 - E)).map C := by
    rw [pe, mulMat_add hg' hn', mulMat_mul hg' hn', mulMat_mul hg' hn', mulMat_C hg' hn',
      mulMat_one hg' hn', one_mul, mulMat_map C n hg, mulMat_map C n hg, Polynomial.map_sub,
      Polynomial.map_one, add_comm, Matrix.smul_eq_diagonal_mul]
    rfl
  have := natDegree_det_X_add_C_le (mulMat n g E) (mulMat n g (1 - E))
  rwa [← hM, Fintype.card_fin] at this

omit hE in
theorem cpoly_sum_coeff : ∑ k ∈ Finset.range (n + 1), (cpoly n g E).coeff k = 1 := by
  have := cpoly_eval_one hg hn (E := E)
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le (cpoly_natDegree_le hg hn))] at this
  simpa using this

end CPoly

theorem coeff_eval₂_CX_mul_X (c : R[X]) (l : ℕ) :
    (eval₂ ((C : R[X] →+* R[X][X]).comp C) (C X * X) c).coeff l = C (c.coeff l) * X ^ l := by
  rw [eval₂_eq_sum, Polynomial.sum, finsetSum_coeff]
  have : ∀ i ∈ c.support, (((C : R[X] →+* R[X][X]).comp C) (c.coeff i) * (C X * X) ^ i).coeff l =
      if l = i then C (c.coeff i) * X ^ i else 0 := by
    intro i _
    rw [mul_pow, ← C_pow, RingHom.comp_apply, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, map_zero, zero_mul]

section Orth

variable {n : ℕ} {g E : R[X]} (hg : g.Monic) (hn : g.natDegree = n) (hE : g ∣ E * E - E)
include hg hn hE

/-- **The coefficients of `c` are orthogonal idempotents**, from `c(y) c(y') = c(y y')`. -/
theorem cpoly_coeff_mul (k l : ℕ) :
    (cpoly n g E).coeff k * (cpoly n g E).coeff l =
      if k = l then (cpoly n g E).coeff k else 0 := by
  set c := cpoly n g E with hc
  have hinj : Function.Injective ((C : R[X] →+* R[X][X]).comp (C : R →+* R[X])) :=
    Polynomial.C_injective.comp Polynomial.C_injective
  have hg2 : (g.map ((C : R[X] →+* R[X][X]).comp C)).Monic := hg.map _
  have hn2 : (g.map ((C : R[X] →+* R[X][X]).comp C)).natDegree = n := by
    rw [natDegree_map_eq_of_injective hinj, hn]
  have hE2 := map_idem_dvd ((C : R[X] →+* R[X][X]).comp C) hE
  have h₁ := cpoly_apply (n := n) (E := E) (C : R[X] →+* R[X][X]) (C.comp C) rfl hg
  have h₂ := cpoly_apply (n := n) (E := E) (mapRingHom (C : R →+* R[X])) (C.comp C)
    (by ext; simp) hg
  have h₃ := cpoly_apply (n := n) (E := E) (eval₂RingHom (C.comp C) (C X * X)) (C.comp C)
    (by ext; simp) hg
  rw [coe_mapRingHom, Polynomial.map_X] at h₂
  rw [coe_eval₂RingHom, eval₂_X] at h₃
  have key : (C c : R[X][X]) * c.map C = eval₂ ((C : R[X] →+* R[X][X]).comp C) (C X * X) c := by
    rw [h₁, h₂, h₃, normMod_pe_mul hg2 hn2 hE2, mul_one, map_mul]
  have hl := congrArg (fun p : R[X][X] => (p.coeff l).coeff k) key
  simp only [coeff_C_mul, coeff_map, coeff_mul_C, coeff_eval₂_CX_mul_X, coeff_C_mul_X_pow] at hl
  rw [hl]
  split_ifs <;> simp_all

end Orth

/-! ## Existence of the factor on a component -/

theorem X_pow_mul_eq_X_pow {k m : ℕ} {q : R[X]} (h : X ^ k * q = X ^ m) :
    q = X ^ (m - k) ∧ (Nontrivial R → k ≤ m) := by
  have hkm : Nontrivial R → k ≤ m := by
    intro _
    by_contra hlt
    have := congrArg (fun p : R[X] => p.coeff m) h
    simp only [coeff_X_pow_mul', coeff_X_pow_self] at this
    rw [if_neg hlt] at this
    exact zero_ne_one this
  refine ⟨?_, hkm⟩
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  · have hk := hkm ‹_›
    have h2 : X ^ k * (q - X ^ (m - k)) = 0 := by
      rw [mul_sub, h, ← pow_add, Nat.add_sub_cancel' hk, sub_self]
    exact sub_eq_zero.mp ((monic_X_pow k).mul_right_eq_zero_iff.mp h2)

theorem mk_aeval {g : R[X]} (x P : R[X]) :
    AdjoinRoot.mk g (aeval x P) = aeval (AdjoinRoot.mk g x) P := by
  rw [aeval_def, aeval_def, Polynomial.hom_eval₂, AdjoinRoot.algebraMap_eq]
  rfl

theorem aeval_mul_idem {S : Type*} [CommRing S] [Algebra R S] {e : S} (he : e * e = e) (z : S)
    (P : R[X]) : aeval z P * e = aeval (z * e) P * e := by
  induction P using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, add_mul, hp, hq]
  | monomial m a _ =>
    have hpow : e ^ (m + 1 + 1) = e := IsIdempotentElem.pow_succ_eq (m + 1) he
    simp only [map_mul, aeval_C, map_pow, aeval_X]
    linear_combination (-(algebraMap R S a * z ^ (m + 1))) * hpow

theorem isCoprime_X_X_sub_one : IsCoprime (X : R[X]) (X - C 1) :=
  ⟨1, -1, by rw [map_one]; ring⟩

section Core

variable {n : ℕ} {g E : R[X]} (hg : g.Monic) (hn : g.natDegree = n) (hE : g ∣ E * E - E)
include hg hn hE

theorem cpoly_compl_of_eq {k : ℕ} (hc : cpoly n g E = X ^ k) :
    cpoly n g (1 - E) = X ^ (n - k) ∧ (Nontrivial R → k ≤ n) :=
  X_pow_mul_eq_X_pow (by rw [← hc]; exact cpoly_mul_compl hg hn hE)

/-- The characteristic polynomial of `x_μ = μ (1 - E) + u E` on a component. -/
theorem charpoly_pe {k : ℕ} (hc : cpoly n g E = X ^ k) (μ : R) :
    (mulMat n g (pe E (C μ) X)).charpoly = (X - C μ) ^ (n - k) * Gpoly n g E := by
  have hg' := hg.map (C : R →+* R[X])
  have hn' := natDegree_mapC hn
  have hE' := map_idem_dvd (C : R →+* R[X]) hE
  rw [charpoly_mulMat hg hn]
  have h1 : C X - (pe E (C μ) X).map C =
      pe (E.map C) ((C X - C (C μ)) * 1) (1 * (C X - X)) := by
    simp only [pe, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one,
      Polynomial.map_C, Polynomial.map_X]
    ring
  rw [h1, ← normMod_pe_mul hg' hn' hE', Gpoly]
  congr 1
  have h3 := cpoly_apply (n := n) (E := 1 - E) (aeval (X - C μ) : R[X] →ₐ[R] R[X]).toRingHom C
    (by ext; simp) hg
  rw [(cpoly_compl_of_eq hg hn hE hc).1] at h3
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_sub,
    Polynomial.map_one, pe_compl, map_sub] at h3
  rw [h3]

theorem split_core {k : ℕ} (hc : cpoly n g E = X ^ k) :
    (Gpoly n g E).Monic ∧ (Nontrivial R → (Gpoly n g E).natDegree = k) ∧
      g ∣ Gpoly n g E * E := by
  have hkn := (cpoly_compl_of_eq hg hn hE hc).2
  have hP0 := charpoly_pe hg hn hE hc 0
  rw [map_zero, sub_zero] at hP0
  have hmon : (X ^ (n - k) * Gpoly n g E).Monic := hP0 ▸ Matrix.charpoly_monic _
  have hGm : (Gpoly n g E).Monic := (monic_X_pow _).of_mul_monic_left hmon
  refine ⟨hGm, fun _ => ?_, ?_⟩
  · have := congrArg natDegree hP0
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, (monic_X_pow _).natDegree_mul hGm,
      natDegree_X_pow] at this
    have := hkn ‹_›
    omega
  · set G := Gpoly n g E
    have hdiv : ∀ μ : R, g ∣ (X - C μ) ^ (n - k) * (G * E) := by
      intro μ
      have hCH := dvd_aeval_charpoly hg hn (pe E (C μ) X)
      rw [charpoly_pe hg hn hE hc μ] at hCH
      rw [← AdjoinRoot.mk_eq_zero] at hCH ⊢
      rw [mk_aeval] at hCH
      set e := AdjoinRoot.mk g E with he_def
      set u := AdjoinRoot.root g
      have he : e * e = e := by
        rw [← map_mul, ← sub_eq_zero, ← map_sub, AdjoinRoot.mk_eq_zero]
        exact hE
      have hz : AdjoinRoot.mk g (pe E (C μ) X) = algebraMap R _ μ * (1 - e) + u * e := by
        simp only [pe, map_add, map_mul, map_sub, map_one, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
          AdjoinRoot.algebraMap_eq, u, he_def]
      rw [hz] at hCH
      set z := algebraMap R (AdjoinRoot g) μ * (1 - e) + u * e
      have hze : z * e = u * e := by linear_combination (u - algebraMap R _ μ) * he
      have h1 : z - algebraMap R _ μ = (u - algebraMap R _ μ) * e := by ring
      simp only [map_mul, map_pow, map_sub, aeval_X, aeval_C] at hCH
      have key := congrArg (· * e) hCH
      simp only [zero_mul] at key
      rw [mul_assoc, aeval_mul_idem he z G, hze, ← aeval_mul_idem he u G, h1, mul_pow,
        AdjoinRoot.aeval_eq] at key
      have hpe : e ^ (n - k) * e = e := by
        rw [← pow_succ]; exact IsIdempotentElem.pow_succ_eq _ he
      simp only [map_mul, map_pow, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
      rw [← key, ← AdjoinRoot.algebraMap_eq]
      linear_combination (-((u - algebraMap R _ μ) ^ (n - k) * AdjoinRoot.mk g G)) * hpe
    have h0 := hdiv 0
    have h1 := hdiv 1
    rw [map_zero, sub_zero] at h0
    obtain ⟨a, b, hab⟩ := (isCoprime_X_X_sub_one (R := R)).pow (m := n - k) (n := n - k)
    have : G * E = a * (X ^ (n - k) * (G * E)) + b * ((X - C 1) ^ (n - k) * (G * E)) := by
      linear_combination (-(G * E)) * hab
    rw [this]
    exact dvd_add (h0.mul_left a) (h1.mul_left b)

end Core

/-! ## Splitting along a coprime factorization -/

theorem dvd_of_mul_dvd_mul_monic {p q r : R[X]} (hp : p.Monic) (h : p * q ∣ p * r) : q ∣ r := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  have h2 : p * (r - q * c) = 0 := by rw [mul_sub, hc]; ring
  exact sub_eq_zero.mp (hp.mul_right_eq_zero_iff.mp h2)

theorem monic_dvd_antisymm {p q : R[X]} (hp : p.Monic) (hq : q.Monic) (h₁ : p ∣ q) (h₂ : q ∣ p) :
    p = q := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  have hab : a * b = 1 := by
    have h3 : p * (a * b - 1) = 0 := by
      rw [mul_sub, mul_one, ← mul_assoc, ← ha, ← hb, sub_self]
    exact sub_eq_zero.mp (hp.mul_right_eq_zero_iff.mp h3)
  exact eq_of_monic_of_associated hp hq ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha.symm⟩

section Coprime

variable {f₁ f₂ α β : R[X]} (hαβ : α * f₁ + β * f₂ = 1)
include hαβ

theorem isCoprime_of_dvd_left {G : R[X]} (h : G ∣ α * f₁) : IsCoprime G f₂ := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, β, by linear_combination hαβ - ha⟩

theorem isCoprime_of_dvd_right {G : R[X]} (h : G ∣ β * f₂) : IsCoprime G f₁ := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, α, by linear_combination hαβ - hb⟩

theorem idem_dvd {g : R[X]} (hgf : g ∣ f₁ * f₂) : g ∣ β * f₂ * (β * f₂) - β * f₂ := by
  have : β * f₂ * (β * f₂) - β * f₂ = -(α * β) * (f₁ * f₂) := by
    linear_combination (β * f₂) * hαβ
  rw [this]
  exact hgf.mul_left _

/-- **Splitting of a monic divisor of `f₁ f₂` on a component.** -/
theorem split_one {n : ℕ} {g : R[X]} (hg : g.Monic) (hn : g.natDegree = n) (hgf : g ∣ f₁ * f₂)
    {k : ℕ} (hc : cpoly n g (β * f₂) = X ^ k) :
    Gpoly n g (β * f₂) * Gpoly n g (1 - β * f₂) = g ∧ (Gpoly n g (β * f₂)).Monic ∧
      (Gpoly n g (1 - β * f₂)).Monic ∧
      (Nontrivial R → (Gpoly n g (β * f₂)).natDegree = k ∧ k ≤ n) ∧
      Gpoly n g (β * f₂) ∣ α * f₁ ∧ Gpoly n g (1 - β * f₂) ∣ β * f₂ := by
  have hE := idem_dvd hαβ hgf
  have hE' : g ∣ (1 - β * f₂) * (1 - β * f₂) - (1 - β * f₂) := by
    have : (1 - β * f₂) * (1 - β * f₂) - (1 - β * f₂) = β * f₂ * (β * f₂) - β * f₂ := by ring
    rw [this]; exact hE
  obtain ⟨hc', hkn⟩ := cpoly_compl_of_eq hg hn hE hc
  obtain ⟨m₁, d₁, h₁⟩ := split_core hg hn hE hc
  obtain ⟨m₂, -, h₂⟩ := split_core hg hn hE' hc'
  have hprod := Gpoly_mul_compl hg hn hE
  refine ⟨hprod, m₁, m₂, fun h => ⟨d₁ h, hkn h⟩, ?_, ?_⟩
  · have : α * f₁ = 1 - β * f₂ := by linear_combination hαβ
    rw [this]
    refine dvd_of_mul_dvd_mul_monic m₂ ?_
    rw [mul_comm]
    exact (dvd_of_eq hprod).trans h₂
  · exact dvd_of_mul_dvd_mul_monic m₁ ((dvd_of_eq hprod).trans h₁)

/-- **Uniqueness of the splitting.** -/
theorem eq_of_split {G₁ G₂ g' g'' : R[X]} (hG₁ : G₁.Monic) (hg' : g'.Monic)
    (hprod : G₁ * G₂ = g' * g'') (h₁ : G₁ ∣ α * f₁) (h₂ : G₂ ∣ β * f₂) (h₁' : g' ∣ f₁)
    (h₂' : g'' ∣ f₂) : G₁ = g' ∧ G₂ = g'' := by
  have c₁ := isCoprime_of_dvd_left hαβ h₁
  have c₂ := isCoprime_of_dvd_right hαβ h₂
  have d₁ : G₁ ∣ g' :=
    (c₁.of_isCoprime_of_dvd_right h₂').dvd_of_dvd_mul_right (hprod ▸ dvd_mul_right _ _)
  have d₂ : g' ∣ G₁ :=
    (c₂.of_isCoprime_of_dvd_right h₁').symm.dvd_of_dvd_mul_right (hprod ▸ dvd_mul_right _ _)
  have e₁ := monic_dvd_antisymm hG₁ hg' d₁ d₂
  refine ⟨e₁, ?_⟩
  rw [e₁] at hprod
  have h3 : g' * (G₂ - g'') = 0 := by rw [mul_sub, hprod, sub_self]
  exact sub_eq_zero.mp (hg'.mul_right_eq_zero_iff.mp h3)

end Coprime

section Component

variable {n : ℕ} {g E : R[X]} (hg : g.Monic) (hn : g.natDegree = n) (hE : g ∣ E * E - E)
include hg hn hE

/-- Base change to a ring where the `j`-th idempotent becomes `1`. -/
theorem cpoly_map_eq_X_pow {S : Type*} [CommRing S] (φ : R →+* S) {j : ℕ}
    (hφ : φ ((cpoly n g E).coeff j) = 1) : cpoly n (g.map φ) (E.map φ) = X ^ j := by
  rw [← cpoly_map φ hg]
  ext l
  rw [coeff_map, coeff_X_pow]
  split_ifs with hl
  · subst hl; exact hφ
  · have h := cpoly_coeff_mul hg hn hE l j
    rw [if_neg hl] at h
    calc φ ((cpoly n g E).coeff l) = φ ((cpoly n g E).coeff l) * φ ((cpoly n g E).coeff j) := by
          rw [hφ, mul_one]
      _ = 0 := by rw [← map_mul, h, map_zero]

theorem cpoly_coeff_idem (j : ℕ) :
    (cpoly n g E).coeff j * (cpoly n g E).coeff j = (cpoly n g E).coeff j := by
  have h := cpoly_coeff_mul hg hn hE j j
  rwa [if_pos rfl] at h

end Component

/-- In `R ⧸ (1 - e)`, the idempotent `e` becomes `1`. -/
theorem quot_idem_eq_one (e : R) :
    Ideal.Quotient.mk (Ideal.span {1 - e}) e = 1 := by
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  have : e - 1 = (-1) * (1 - e) := by ring
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- If `R ⧸ (1 - e)` is trivial for an idempotent `e`, then `e = 0`. -/
theorem idem_eq_zero_of_quot {e : R} (he : e * e = e)
    (h : ¬ Nontrivial (R ⧸ Ideal.span {1 - e})) : e = 0 := by
  rw [Ideal.Quotient.nontrivial_iff, not_not] at h
  have h1 : (1 : R) ∈ Ideal.span {1 - e} := h ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
  linear_combination (-e) * ha - a * he


section Unique

variable {f₁ f₂ α β : R[X]} (hαβ : α * f₁ + β * f₂ = 1)
include hαβ

/-- **The idempotents and factors are determined by an existing splitting.** If
`g = g' g''` with `g' ∣ f₁`, `g'' ∣ f₂` and `g'` of degree `k`, then `c(y) = y^k` and the
constructed factors are `g'` and `g''`. -/
theorem cpoly_of_split {n : ℕ} {g g' g'' : R[X]} (hg : g.Monic) (hn : g.natDegree = n)
    (hg' : g'.Monic) (hgg : g = g' * g'') (h₁ : g' ∣ f₁) (h₂ : g'' ∣ f₂)
    {k : ℕ} (hk : Nontrivial R → g'.natDegree = k) :
    cpoly n g (β * f₂) = X ^ k ∧ Gpoly n g (β * f₂) = g' ∧ Gpoly n g (1 - β * f₂) = g'' := by
  have hgf : g ∣ f₁ * f₂ := hgg ▸ mul_dvd_mul h₁ h₂
  have hE := idem_dvd hαβ hgf
  set c := cpoly n g (β * f₂) with hc_def
  have hzero : ∀ j, j ≠ k → c.coeff j = 0 := by
    intro j hj
    by_contra hne
    set I := Ideal.span {1 - c.coeff j}
    have hnt : Nontrivial (R ⧸ I) := by
      by_contra hnt
      exact hne (idem_eq_zero_of_quot (cpoly_coeff_idem hg hn hE j) hnt)
    have hR : Nontrivial R := (Ideal.Quotient.mk I).domain_nontrivial
    let π := Ideal.Quotient.mk I
    have hcj := cpoly_map_eq_X_pow hg hn hE π (quot_idem_eq_one _)
    rw [Polynomial.map_mul] at hcj
    have hαβ' : α.map π * f₁.map π + β.map π * f₂.map π = 1 := by
      have := congrArg (Polynomial.map π) hαβ
      simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one] using this
    have hgf' : g.map π ∣ f₁.map π * f₂.map π := by
      rw [← Polynomial.map_mul]; exact Polynomial.map_dvd π hgf
    have hn' : (g.map π).natDegree = n := by rw [hg.natDegree_map, hn]
    obtain ⟨hprod, hm1, -, hdeg, hd1, hd2⟩ := split_one hαβ' (hg.map π) hn' hgf' hcj
    have he := eq_of_split hαβ' hm1 (hg'.map π)
      (by rw [hprod, hgg, Polynomial.map_mul]) hd1 hd2 (Polynomial.map_dvd π h₁)
      (Polynomial.map_dvd π h₂)
    have hdj := (hdeg hnt).1
    rw [he.1, hg'.natDegree_map, hk hR] at hdj
    exact hj hdj.symm
  have hck : c.coeff k = 1 := by
    have h1 := cpoly_eval_one hg hn (E := β * f₂)
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le (cpoly_natDegree_le hg hn))] at h1
    rw [Finset.sum_eq_single k (fun b _ hb => by rw [hzero b hb, zero_mul])
      (fun hk' => by
        rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (cpoly_natDegree_le hg hn)
          (by simpa using hk')), zero_mul])] at h1
    rwa [one_pow, mul_one] at h1
  have hc : c = X ^ k := by
    ext j
    rw [coeff_X_pow]
    split_ifs with h
    · subst h; exact hck
    · exact hzero j h
  obtain ⟨hprod, hm1, -, -, hd1, hd2⟩ := split_one hαβ hg hn hgf hc
  obtain ⟨e1, e2⟩ := eq_of_split hαβ hm1 hg' (hprod.trans hgg) hd1 hd2 h₁ h₂
  exact ⟨hc, e1, e2⟩

/-- **The weighted pair `(A, W)` with `A W³ = f₁ f₂` splits on each component.** -/
theorem pair_split {r s d₁ : ℕ} {A W : R[X]} (hA : A.Monic) (hAr : A.natDegree = r)
    (hW : W.Monic) (hWs : W.natDegree = s) (hf₁ : f₁.Monic) (hd₁ : f₁.natDegree = d₁)
    (hf₂ : f₂.Monic) (hAW : A * W ^ 3 = f₁ * f₂) {k t : ℕ}
    (hcA : cpoly r A (β * f₂) = X ^ k) (hcW : cpoly s W (β * f₂) = X ^ t) :
    Gpoly r A (β * f₂) * Gpoly s W (β * f₂) ^ 3 = f₁ ∧
      Gpoly r A (1 - β * f₂) * Gpoly s W (1 - β * f₂) ^ 3 = f₂ ∧
      (Nontrivial R → k + 3 * t = d₁) := by
  have hAf : A ∣ f₁ * f₂ := ⟨W ^ 3, hAW.symm⟩
  have hWf : W ∣ f₁ * f₂ := ⟨A * W ^ 2, by rw [← hAW]; ring⟩
  obtain ⟨pA, mA1, mA2, dA, dA1, dA2⟩ := split_one hαβ hA hAr hAf hcA
  obtain ⟨pW, mW1, mW2, dW, dW1, dW2⟩ := split_one hαβ hW hWs hWf hcW
  set A₁ := Gpoly r A (β * f₂)
  set A₂ := Gpoly r A (1 - β * f₂)
  set W₁ := Gpoly s W (β * f₂)
  set W₂ := Gpoly s W (1 - β * f₂)
  have key : f₁ * f₂ = (A₁ * W₁ ^ 3) * (A₂ * W₂ ^ 3) := by rw [← hAW, ← pA, ← pW]; ring
  have cf₁ : IsCoprime f₁ (A₂ * W₂ ^ 3) :=
    (isCoprime_of_dvd_right hαβ dA2).symm.mul_right
      (isCoprime_of_dvd_right hαβ dW2).symm.pow_right
  have cf₂ : IsCoprime f₂ (A₁ * W₁ ^ 3) :=
    (isCoprime_of_dvd_left hαβ dA1).symm.mul_right
      (isCoprime_of_dvd_left hαβ dW1).symm.pow_right
  have df₁ : f₁ ∣ A₁ * W₁ ^ 3 := cf₁.dvd_of_dvd_mul_right (key ▸ dvd_mul_right f₁ f₂)
  have df₂ : f₂ ∣ A₂ * W₂ ^ 3 := cf₂.dvd_of_dvd_mul_left (key ▸ dvd_mul_left f₂ f₁)
  obtain ⟨h, hh⟩ := df₁
  obtain ⟨h', hh'⟩ := df₂
  have hhm : h.Monic := hf₁.of_mul_monic_left (hh ▸ mA1.mul (mW1.pow 3))
  have hh'm : h'.Monic := hf₂.of_mul_monic_left (hh' ▸ mA2.mul (mW2.pow 3))
  have hhh' : h * h' = 1 := by
    have h3 : (f₁ * f₂) * (h * h' - 1) = 0 := by
      rw [mul_sub, mul_one]
      nth_rewrite 2 [key]
      rw [hh, hh']
      ring
    exact sub_eq_zero.mp ((hf₁.mul hf₂).mul_right_eq_zero_iff.mp h3)
  have h1 : h = 1 := monic_dvd_antisymm hhm monic_one ⟨h', hhh'.symm⟩ (one_dvd h)
  have h1' : h' = 1 := monic_dvd_antisymm hh'm monic_one ⟨h, by rw [mul_comm]; exact hhh'.symm⟩
    (one_dvd h')
  rw [h1, mul_one] at hh
  rw [h1', mul_one] at hh'
  refine ⟨hh, hh', fun hnt => ?_⟩
  have := congrArg natDegree hh
  rw [mA1.natDegree_mul (mW1.pow 3), (mW1).natDegree_pow, (dA hnt).1, (dW hnt).1, hd₁] at this
  omega

end Unique


/-! ## Versions allowing the zero ring

In the zero ring every polynomial has degree `0`; the following versions only assume the degree
conditions when the ring is nontrivial. -/

section Nontriv

variable {n : ℕ} {g E : R[X]} (hg : g.Monic) (hn : Nontrivial R → g.natDegree = n)
include hg hn

theorem cpoly_coeff_mul' (hE : g ∣ E * E - E) (k l : ℕ) :
    (cpoly n g E).coeff k * (cpoly n g E).coeff l =
      if k = l then (cpoly n g E).coeff k else 0 := by
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  · exact cpoly_coeff_mul hg (hn ‹_›) hE k l

theorem cpoly_coeff_idem' (hE : g ∣ E * E - E) (j : ℕ) :
    (cpoly n g E).coeff j * (cpoly n g E).coeff j = (cpoly n g E).coeff j := by
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  · exact cpoly_coeff_idem hg (hn ‹_›) hE j

theorem cpoly_sum_coeff' : ∑ k ∈ Finset.range (n + 1), (cpoly n g E).coeff k = 1 := by
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  · exact cpoly_sum_coeff hg (hn ‹_›)

theorem cpoly_map_eq_X_pow' (hE : g ∣ E * E - E) {S : Type*} [CommRing S] (φ : R →+* S)
    {j : ℕ} (hφ : φ ((cpoly n g E).coeff j) = 1) : cpoly n (g.map φ) (E.map φ) = X ^ j := by
  cases subsingleton_or_nontrivial R
  · have : Subsingleton S := by
      refine ⟨fun a b => ?_⟩
      rw [← mul_one a, ← mul_one b, ← hφ, Subsingleton.elim ((cpoly n g E).coeff j) 0, map_zero,
        mul_zero, mul_zero]
    exact Subsingleton.elim _ _
  · exact cpoly_map_eq_X_pow hg (hn ‹_›) hE φ hφ

end Nontriv

section Nontriv2

variable {f₁ f₂ α β : R[X]} (hαβ : α * f₁ + β * f₂ = 1)
include hαβ

theorem split_one' {n : ℕ} {g : R[X]} (hg : g.Monic) (hn : Nontrivial R → g.natDegree = n)
    (hgf : g ∣ f₁ * f₂) {k : ℕ} (hc : cpoly n g (β * f₂) = X ^ k) :
    Gpoly n g (β * f₂) * Gpoly n g (1 - β * f₂) = g ∧ (Gpoly n g (β * f₂)).Monic ∧
      (Gpoly n g (1 - β * f₂)).Monic ∧
      (Nontrivial R → (Gpoly n g (β * f₂)).natDegree = k ∧ k ≤ n) ∧
      Gpoly n g (β * f₂) ∣ α * f₁ ∧ Gpoly n g (1 - β * f₂) ∣ β * f₂ := by
  cases subsingleton_or_nontrivial R
  · refine ⟨Subsingleton.elim _ _, ?_, ?_, fun h => absurd h (not_nontrivial R), ?_, ?_⟩
    · exact Subsingleton.elim (α := R) _ _
    · exact Subsingleton.elim (α := R) _ _
    · exact ⟨0, Subsingleton.elim _ _⟩
    · exact ⟨0, Subsingleton.elim _ _⟩
  · exact split_one hαβ hg (hn ‹_›) hgf hc

theorem cpoly_of_split' {n : ℕ} {g g' g'' : R[X]} (hg : g.Monic)
    (hn : Nontrivial R → g.natDegree = n) (hg' : g'.Monic) (hgg : g = g' * g'') (h₁ : g' ∣ f₁)
    (h₂ : g'' ∣ f₂) {k : ℕ} (hk : Nontrivial R → g'.natDegree = k) :
    cpoly n g (β * f₂) = X ^ k ∧ Gpoly n g (β * f₂) = g' ∧ Gpoly n g (1 - β * f₂) = g'' := by
  cases subsingleton_or_nontrivial R
  · exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · exact cpoly_of_split hαβ hg (hn ‹_›) hg' hgg h₁ h₂ hk

theorem pair_split' {r s d₁ : ℕ} {A W : R[X]} (hA : A.Monic) (hAr : Nontrivial R → A.natDegree = r)
    (hW : W.Monic) (hWs : Nontrivial R → W.natDegree = s) (hf₁ : f₁.Monic)
    (hd₁ : Nontrivial R → f₁.natDegree = d₁) (hf₂ : f₂.Monic) (hAW : A * W ^ 3 = f₁ * f₂)
    {k t : ℕ} (hcA : cpoly r A (β * f₂) = X ^ k) (hcW : cpoly s W (β * f₂) = X ^ t) :
    Gpoly r A (β * f₂) * Gpoly s W (β * f₂) ^ 3 = f₁ ∧
      Gpoly r A (1 - β * f₂) * Gpoly s W (1 - β * f₂) ^ 3 = f₂ ∧
      (Nontrivial R → k + 3 * t = d₁) := by
  cases subsingleton_or_nontrivial R
  · exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, fun h => absurd h (not_nontrivial R)⟩
  · exact pair_split hαβ hA (hAr ‹_›) hW (hWs ‹_›) hf₁ (hd₁ ‹_›) hf₂ hAW hcA hcW

end Nontriv2

end KhanSL2.Collision.NormSplit
