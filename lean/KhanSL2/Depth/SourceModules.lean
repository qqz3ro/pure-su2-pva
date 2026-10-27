module

public import KhanSL2.Depth.SourceCoords
public import KhanSL2.Depth.TwoBlock
public import Mathlib.RingTheory.Polynomial.Vieta

@[expose] public section

/-!
# The source modules `J_{B,p}` (blueprint `def:nu`, `lem:divisibility`)

Let `B = r + 3s`. In `ℂ[z, w] = ℂ[z₁, …, z_r, w₁, …, w_s]`:
* `S_{r,s} = symmBoth r s` is the algebra of polynomials symmetric in `z` and in `w`;
* `F_{r,s} = Δ(z)² Δ(w)³ ∏(zᵢ - w_a)²` (`Fpoly`);
* `ν* : R_B → ℂ[z, w]` substitutes `(t₁, …, t_B) ↦ (z, w, w, w)`:
  `ν*(e_k) = e_k(z₁, …, z_r, w₁, w₁, w₁, …, w_s, w_s, w_s)` (`nuStar`);
* `J_{r,s} = F_{r,s} · S_{r,s}`, an `R_B`-module through `ν*` (`J`), and `J_{B,p}` is
  `J_{p,s}` if `B = p + 3s`, and `0` otherwise (`JB`).

The paper identifies `J_{r,s}` with the graded dual of the `(r, s)` sector of the source
(Lemma 3.1, blueprint `lem:functional`); that identification is not part of this file.

This file also builds the coordinate map `Φ` (`coordToRoots`): the coefficients of
`A = ∏(u - zᵢ)` and `W = ∏(u - w_a)` are signed elementary symmetric functions. It is injective
with image `S_{r,s}` (two-block fundamental theorem), and `A W³ = ∏(u - tⱼ)` turns `ν` into
`ν*` (Vieta, `coordToRoots_comp_nu`). `SourceDepth` uses it to identify `J_{r,s}` with the
coefficient coordinates.
-/

noncomputable section

open MvPolynomial

namespace KhanSL2.Depth

variable (B r s : ℕ)

/-! ## The substitution `ν*` -/

/-- The multiset `(z₁, …, z_r, w₁, w₁, w₁, …, w_s, w_s, w_s)` as a map of index types. -/
def tupleMap : Fin r ⊕ Fin s × Fin 3 → Fin r ⊕ Fin s
  | Sum.inl i => Sum.inl i
  | Sum.inr (a, _) => Sum.inr a

/-- **`ν*`**: `e_{j+1} ↦ e_{j+1}(z, w, w, w)`. -/
def nuStar : RB B →ₐ[ℂ] ZW r s :=
  aeval fun j => rename (tupleMap r s) (esymm (Fin r ⊕ Fin s × Fin 3) ℂ ((j : ℕ) + 1))

theorem nuStar_X (j : Fin B) :
    nuStar B r s (X j) = rename (tupleMap r s) (esymm (Fin r ⊕ Fin s × Fin 3) ℂ ((j : ℕ) + 1)) :=
  aeval_X _ _

theorem nuStar_mem_symmBoth (c : RB B) : nuStar B r s c ∈ symmBoth r s := by
  induction c using MvPolynomial.induction_on with
  | C a =>
    rw [nuStar, aeval_C]
    exact (symmBoth r s).algebraMap_mem a
  | add p q hp hq =>
    rw [map_add]
    exact (symmBoth r s).add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul]
    refine (symmBoth r s).mul_mem hp ?_
    rw [nuStar_X]
    intro σ τ
    rw [rename_rename]
    let π : Equiv.Perm (Fin r ⊕ Fin s × Fin 3) :=
      Equiv.sumCongr σ (Equiv.prodCongr τ (Equiv.refl (Fin 3)))
    have hπ : (Sum.map σ τ ∘ tupleMap r s) = tupleMap r s ∘ π := by
      funext t
      rcases t with i | ⟨a, c⟩ <;> rfl
    rw [hπ, ← rename_rename]
    congr 1
    exact (esymm_isSymmetric _ ℂ _) π

/-! ## Coefficients of `∏(u - zᵢ)` -/

/-- Signed reversal of coordinates: the coefficient of `u^k` in a monic polynomial of degree `n`
is `(-1)^{n-k} e_{n-k}` of its roots. -/
def coordSign : MvPolynomial (Fin r ⊕ Fin s) ℂ →ₐ[ℂ] MvPolynomial (Fin r ⊕ Fin s) ℂ :=
  aeval fun v => match v with
    | Sum.inl k => (-1) ^ (r - (k : ℕ)) * X (Sum.inl k.rev)
    | Sum.inr k => (-1) ^ (s - (k : ℕ)) * X (Sum.inr k.rev)

/-- The inverse of `coordSign`. -/
def coordSignInv : MvPolynomial (Fin r ⊕ Fin s) ℂ →ₐ[ℂ] MvPolynomial (Fin r ⊕ Fin s) ℂ :=
  aeval fun v => match v with
    | Sum.inl j => (-1) ^ ((j : ℕ) + 1) * X (Sum.inl j.rev)
    | Sum.inr j => (-1) ^ ((j : ℕ) + 1) * X (Sum.inr j.rev)

theorem neg_one_pow_mul_self (a : ℕ) : ((-1 : MvPolynomial (Fin r ⊕ Fin s) ℂ) ^ a) *
    (-1) ^ a = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

theorem coordSignInv_coordSign : (coordSignInv r s).comp (coordSign r s) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  rintro (k | k)
  · simp only [AlgHom.comp_apply, coordSign, coordSignInv, aeval_X, map_mul, map_pow, map_neg,
      map_one, Fin.rev_rev, AlgHom.id_apply, Fin.val_rev]
    rw [← mul_assoc, ← pow_add, show r - (k : ℕ) + (r - ((k : ℕ) + 1) + 1) = 2 * (r - k) by omega,
      pow_mul, neg_one_sq, one_pow, one_mul]
  · simp only [AlgHom.comp_apply, coordSign, coordSignInv, aeval_X, map_mul, map_pow, map_neg,
      map_one, Fin.rev_rev, AlgHom.id_apply, Fin.val_rev]
    rw [← mul_assoc, ← pow_add, show s - (k : ℕ) + (s - ((k : ℕ) + 1) + 1) = 2 * (s - k) by omega,
      pow_mul, neg_one_sq, one_pow, one_mul]

theorem coordSign_coordSignInv : (coordSign r s).comp (coordSignInv r s) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  rintro (k | k)
  · simp only [AlgHom.comp_apply, coordSign, coordSignInv, aeval_X, map_mul, map_pow, map_neg,
      map_one, Fin.rev_rev, AlgHom.id_apply, Fin.val_rev]
    rw [← mul_assoc, ← pow_add, show (k : ℕ) + 1 + (r - (r - ((k : ℕ) + 1))) = 2 * ((k : ℕ) + 1) by
      omega, pow_mul, neg_one_sq, one_pow, one_mul]
  · simp only [AlgHom.comp_apply, coordSign, coordSignInv, aeval_X, map_mul, map_pow, map_neg,
      map_one, Fin.rev_rev, AlgHom.id_apply, Fin.val_rev]
    rw [← mul_assoc, ← pow_add, show (k : ℕ) + 1 + (s - (s - ((k : ℕ) + 1))) = 2 * ((k : ℕ) + 1) by
      omega, pow_mul, neg_one_sq, one_pow, one_mul]

/-- **The coordinate map** `Φ`: coefficients of `(A, W)` ↦ signed elementary symmetric functions
of the roots. -/
def coordToRoots : Src r s →ₐ[ℂ] ZW r s := (blockE r s).comp (coordSign r s)

theorem coordToRoots_injective : Function.Injective (coordToRoots r s) := by
  intro f g h
  have h1 : coordSign r s f = coordSign r s g := blockE_injective r s h
  have h2 := congrArg (coordSignInv r s) h1
  rwa [← AlgHom.comp_apply, coordSignInv_coordSign, ← AlgHom.comp_apply,
    coordSignInv_coordSign, AlgHom.id_apply, AlgHom.id_apply] at h2

theorem mem_symmBoth_iff_coordToRoots (f : ZW r s) :
    f ∈ symmBoth r s ↔ ∃ g, coordToRoots r s g = f := by
  rw [mem_symmBoth_iff]
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨coordSignInv r s g, ?_⟩
    rw [coordToRoots, AlgHom.comp_apply, ← AlgHom.comp_apply (coordSign r s),
      coordSign_coordSignInv, AlgHom.id_apply]
  · rintro ⟨g, rfl⟩
    exact ⟨coordSign r s g, rfl⟩

theorem coordToRoots_inl (k : Fin r) :
    coordToRoots r s (X (Sum.inl k)) =
      (-1) ^ (r - (k : ℕ)) * rename Sum.inl (esymm (Fin r) ℂ (r - (k : ℕ))) := by
  simp only [coordToRoots, AlgHom.comp_apply, coordSign, aeval_X, map_mul, map_pow, map_neg,
    map_one, blockE, blockEsymm, Fin.val_rev]
  rw [show r - ((k : ℕ) + 1) + 1 = r - k by omega]

theorem coordToRoots_inr (k : Fin s) :
    coordToRoots r s (X (Sum.inr k)) =
      (-1) ^ (s - (k : ℕ)) * rename Sum.inr (esymm (Fin s) ℂ (s - (k : ℕ))) := by
  simp only [coordToRoots, AlgHom.comp_apply, coordSign, aeval_X, map_mul, map_pow, map_neg,
    map_one, blockE, blockEsymm, Fin.val_rev]
  rw [show s - ((k : ℕ) + 1) + 1 = s - k by omega]

/-! ## Vieta -/

/-- Vieta for `∏(u - Xᵢ)`. -/
theorem coeff_prod_X_sub_C_X (σ : Type) [Fintype σ] {k : ℕ} (hk : k ≤ Fintype.card σ) :
    (∏ i : σ, (Polynomial.X - Polynomial.C (X i : MvPolynomial σ ℂ))).coeff k =
      (-1) ^ (Fintype.card σ - k) * esymm σ ℂ (Fintype.card σ - k) := by
  have h := Multiset.prod_X_sub_C_coeff (Finset.univ.val.map fun i : σ => (X i : MvPolynomial σ ℂ))
    (k := k) (by simpa using hk)
  rw [Multiset.map_map] at h
  simp only [Multiset.card_map, Finset.card_val, Finset.card_univ] at h
  rw [← congrFun (esymm_eq_multiset_esymm σ ℂ)] at h
  rw [Finset.prod_eq_multiset_prod]
  exact h

theorem prod_X_sub_C_X_monic (σ : Type) [Fintype σ] :
    (∏ i : σ, (Polynomial.X - Polynomial.C (X i : MvPolynomial σ ℂ))).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem natDegree_prod_X_sub_C_X (σ : Type) [Fintype σ] :
    (∏ i : σ, (Polynomial.X - Polynomial.C (X i : MvPolynomial σ ℂ))).natDegree =
      Fintype.card σ := by
  rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
  simp

/-- Two monic polynomials of the same degree with the same lower coefficients are equal. -/
theorem eq_of_monic_of_coeff_lt {R : Type*} [CommRing R] {p q : Polynomial R} {n : ℕ}
    (hp : p.Monic) (hq : q.Monic) (hpn : p.natDegree = n) (hqn : q.natDegree = n)
    (h : ∀ k < n, p.coeff k = q.coeff k) : p = q := by
  ext k
  rcases lt_trichotomy k n with hk | rfl | hk
  · exact h k hk
  · have h1 := hp.leadingCoeff
    have h2 := hq.leadingCoeff
    rw [Polynomial.leadingCoeff, hpn] at h1
    rw [Polynomial.leadingCoeff, hqn] at h2
    rw [h1, h2]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hpn ▸ hk),
      Polynomial.coeff_eq_zero_of_natDegree_lt (hqn ▸ hk)]

/-- `Φ(A) = ∏(u - zᵢ)`. -/
theorem genA_map_coordToRoots :
    (genA r s).map (coordToRoots r s : Src r s →+* ZW r s) =
      ∏ i : Fin r, (Polynomial.X - Polynomial.C (X (Sum.inl i) : ZW r s)) := by
  have hprod : (∏ i : Fin r, (Polynomial.X - Polynomial.C (X (Sum.inl i) : ZW r s))) =
      (∏ i : Fin r, (Polynomial.X - Polynomial.C (X i : MvPolynomial (Fin r) ℂ))).map
        (rename Sum.inl : MvPolynomial (Fin r) ℂ →ₐ[ℂ] ZW r s) := by
    simp [Polynomial.map_prod]
  rw [hprod]
  apply eq_of_monic_of_coeff_lt ((genA_monic r s).map _)
    ((prod_X_sub_C_X_monic (Fin r)).map _) (n := r)
  · rw [(genA_monic r s).natDegree_map, genA, natDegree_monicOf]
  · rw [(prod_X_sub_C_X_monic (Fin r)).natDegree_map, natDegree_prod_X_sub_C_X, Fintype.card_fin]
  · intro k hk
    rw [Polynomial.coeff_map, Polynomial.coeff_map, genA,
      show k = ((⟨k, hk⟩ : Fin r) : ℕ) from rfl, coeff_monicOf, coeff_prod_X_sub_C_X _ (by simp; omega)]
    simp only [RingHom.coe_coe, coordToRoots_inl, Fintype.card_fin, map_mul, map_pow, map_neg,
      map_one]

/-- `Φ(W) = ∏(u - w_a)`. -/
theorem genW_map_coordToRoots :
    (genW r s).map (coordToRoots r s : Src r s →+* ZW r s) =
      ∏ a : Fin s, (Polynomial.X - Polynomial.C (X (Sum.inr a) : ZW r s)) := by
  have hprod : (∏ a : Fin s, (Polynomial.X - Polynomial.C (X (Sum.inr a) : ZW r s))) =
      (∏ a : Fin s, (Polynomial.X - Polynomial.C (X a : MvPolynomial (Fin s) ℂ))).map
        (rename Sum.inr : MvPolynomial (Fin s) ℂ →ₐ[ℂ] ZW r s) := by
    simp [Polynomial.map_prod]
  rw [hprod]
  apply eq_of_monic_of_coeff_lt ((genW_monic r s).map _)
    ((prod_X_sub_C_X_monic (Fin s)).map _) (n := s)
  · rw [(genW_monic r s).natDegree_map, genW, natDegree_monicOf]
  · rw [(prod_X_sub_C_X_monic (Fin s)).natDegree_map, natDegree_prod_X_sub_C_X, Fintype.card_fin]
  · intro k hk
    rw [Polynomial.coeff_map, Polynomial.coeff_map, genW,
      show k = ((⟨k, hk⟩ : Fin s) : ℕ) from rfl, coeff_monicOf, coeff_prod_X_sub_C_X _ (by simp; omega)]
    simp only [RingHom.coe_coe, coordToRoots_inr, Fintype.card_fin, map_mul, map_pow, map_neg,
      map_one]

/-- `Φ(A W³) = ∏ⱼ (u - tⱼ)` over the tuple `(z, w, w, w)`. -/
theorem genF_map_coordToRoots :
    (genF r s).map (coordToRoots r s : Src r s →+* ZW r s) =
      (∏ t : Fin r ⊕ Fin s × Fin 3,
        (Polynomial.X - Polynomial.C (X t : MvPolynomial (Fin r ⊕ Fin s × Fin 3) ℂ))).map
        (rename (tupleMap r s) : MvPolynomial (Fin r ⊕ Fin s × Fin 3) ℂ →ₐ[ℂ] ZW r s) := by
  rw [genF, Polynomial.map_mul, Polynomial.map_pow, genA_map_coordToRoots, genW_map_coordToRoots,
    Polynomial.map_prod, Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.coe_coe, rename_X,
    tupleMap, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_pow]

/-- **Vieta: `Φ ∘ ν = ν*`.** -/
theorem coordToRoots_comp_nu :
    (coordToRoots r s).comp (nu r s) = nuStar (r + 3 * s) r s := by
  apply MvPolynomial.algHom_ext
  intro j
  rw [AlgHom.comp_apply, nu_X, map_mul, map_pow, map_neg, map_one, nuStar_X]
  have hc := congrArg (fun p => Polynomial.coeff p (r + 3 * s - ((j : ℕ) + 1)))
    (genF_map_coordToRoots r s)
  simp only [Polynomial.coeff_map, RingHom.coe_coe] at hc
  rw [hc, coeff_prod_X_sub_C_X _ (by simp; omega)]
  have hcard : Fintype.card (Fin r ⊕ Fin s × Fin 3) = r + 3 * s := by simp; ring
  rw [hcard, show r + 3 * s - (r + 3 * s - ((j : ℕ) + 1)) = (j : ℕ) + 1 by omega, map_mul,
    map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

/-! ## `F_{r,s}` and `J_{r,s}` -/

/-- `Δ(z) = ∏_{i<j} (zᵢ - zⱼ)`. -/
def vandermondeZ : ZW r s := ∏ i : Fin r, ∏ j ∈ Finset.Ioi i, (X (Sum.inl i) - X (Sum.inl j))

/-- `Δ(w) = ∏_{a<b} (w_a - w_b)`. -/
def vandermondeW : ZW r s := ∏ a : Fin s, ∏ b ∈ Finset.Ioi a, (X (Sum.inr a) - X (Sum.inr b))

/-- **`F_{r,s} = Δ(z)² Δ(w)³ ∏(zᵢ - w_a)²`.** -/
def Fpoly : ZW r s :=
  vandermondeZ r s ^ 2 * vandermondeW r s ^ 3 *
    ∏ i : Fin r, ∏ a : Fin s, (X (Sum.inl i) - X (Sum.inr a)) ^ 2

theorem X_sub_X_ne_zero {v w : Fin r ⊕ Fin s} (h : v ≠ w) : (X v - X w : ZW r s) ≠ 0 :=
  sub_ne_zero.mpr fun h' => h (X_injective h')

theorem Fpoly_ne_zero : Fpoly r s ≠ 0 := by
  rw [Fpoly]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)) ?_
  · rw [vandermondeZ, Finset.prod_ne_zero_iff]
    intro i _
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    exact X_sub_X_ne_zero r s fun h => (ne_of_lt (Finset.mem_Ioi.mp hj)) (Sum.inl_injective h)
  · rw [vandermondeW, Finset.prod_ne_zero_iff]
    intro a _
    rw [Finset.prod_ne_zero_iff]
    intro b hb
    exact X_sub_X_ne_zero r s fun h => (ne_of_lt (Finset.mem_Ioi.mp hb)) (Sum.inr_injective h)
  · rw [Finset.prod_ne_zero_iff]
    intro i _
    rw [Finset.prod_ne_zero_iff]
    intro a _
    exact pow_ne_zero _ (X_sub_X_ne_zero r s Sum.inl_ne_inr)

/-- `ℂ[z, w]` as an `R_B`-module through `ν*`. -/
def RootsMod (_B r s : ℕ) : Type := ZW r s

instance : CommRing (RootsMod B r s) := inferInstanceAs (CommRing (ZW r s))

instance : Algebra (RB B) (RootsMod B r s) := (nuStar B r s).toRingHom.toAlgebra

theorem RootsMod.smul_def (c : RB B) (f : RootsMod B r s) :
    c • f = (nuStar B r s c : ZW r s) * (show ZW r s from f) := rfl

/-- **`J_{r,s} = F_{r,s} · S_{r,s}`**, an `R_B`-module through `ν*`. -/
def J : Submodule (RB B) (RootsMod B r s) where
  carrier := {f | ∃ g : ZW r s, g ∈ symmBoth r s ∧ @Eq (ZW r s) f (Fpoly r s * g)}
  add_mem' := by
    rintro f f' ⟨g, hg, hf⟩ ⟨g', hg', hf'⟩
    refine ⟨g + g', (symmBoth r s).add_mem hg hg', ?_⟩
    change (show ZW r s from f) + (show ZW r s from f') = Fpoly r s * (g + g')
    rw [hf, hf', mul_add]
  zero_mem' := ⟨0, (symmBoth r s).zero_mem, (mul_zero (Fpoly r s)).symm⟩
  smul_mem' := by
    rintro c f ⟨g, hg, hf⟩
    refine ⟨nuStar B r s c * g, (symmBoth r s).mul_mem (nuStar_mem_symmBoth B r s c) hg, ?_⟩
    change (nuStar B r s c : ZW r s) * (show ZW r s from f) = Fpoly r s * (nuStar B r s c * g)
    rw [hf]
    ring

/-- **`J_{B,p}`**: `J_{p,s}` if `B = p + 3s`, and `0` otherwise. -/
def JB (B p : ℕ) : Submodule (RB B) (RootsMod B p ((B - p) / 3)) :=
  if p ≤ B ∧ 3 ∣ B - p then J B p ((B - p) / 3) else ⊥

end KhanSL2.Depth
