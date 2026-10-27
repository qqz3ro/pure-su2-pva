module

public import KhanSL2.Collision.NormSplit
public import KhanSL2.Collision.Statements

@[expose] public section

/-!
# Coefficient coordinates over a chart

`CMod B r s` is the polynomial ring of coefficients `(a, w)` of a pair of monic polynomials
`(A, W)` of degrees `r, s`, made an `R_B`-algebra by `A W³ = ∏ (u - t_i)` (`nuB`). For an
`R_B`-algebra `A`, the ring `A ⊗_{R_B} CMod B r s` is the universal `A`-algebra carrying such a
pair with `A W³ = F_B` (`liftT`, `liftT_ext`).
-/

noncomputable section

open Polynomial TensorProduct

namespace KhanSL2.Collision.CoordSplit

open Depth

/-- `ν_B : R_B → ℂ[a, w]`, `e_{j+1} ↦ (-1)^{j+1} [u^{B-j-1}] A W³`. -/
def nuB (B r s : ℕ) : RB B →ₐ[ℂ] Src r s :=
  MvPolynomial.aeval fun j => (-1) ^ ((j : ℕ) + 1) * (genF r s).coeff (B - ((j : ℕ) + 1))

/-- The coefficient coordinates of `(A, W)` as an `R_B`-algebra through `ν_B`. -/
def CMod (_B r s : ℕ) : Type := Src r s

instance (B r s : ℕ) : CommRing (CMod B r s) := inferInstanceAs (CommRing (Src r s))

instance (B r s : ℕ) : Algebra (RB B) (CMod B r s) := (nuB B r s).toRingHom.toAlgebra

theorem CMod.algebraMap_eq (B r s : ℕ) :
    (algebraMap (RB B) (CMod B r s) : RB B →+* Src r s) = (nuB B r s : RB B →+* Src r s) := rfl

/-! ## The universal polynomial -/

theorem univPoly_monic (B : ℕ) : (univPoly B).Monic := monicOf_monic _ _

theorem univPoly_coeff (B : ℕ) (j : Fin B) :
    (univPoly B).coeff (B - 1 - (j : ℕ)) =
      MvPolynomial.C ((-1 : ℂ) ^ ((j : ℕ) + 1)) * MvPolynomial.X j := by
  have h := coeff_monicOf B (fun k : Fin B => ((-1 : ℂ) ^ (B - (k : ℕ))) •
    (MvPolynomial.X (⟨B - 1 - (k : ℕ), by omega⟩ : Fin B) : RB B)) ⟨B - 1 - (j : ℕ), by omega⟩
  rw [univPoly]
  refine h.trans ?_
  rw [MvPolynomial.smul_eq_C_mul]
  have e1 : B - ((⟨B - 1 - (j : ℕ), by omega⟩ : Fin B) : ℕ) = (j : ℕ) + 1 := by
    simp only; omega
  have e2 : (⟨B - 1 - ((⟨B - 1 - (j : ℕ), by omega⟩ : Fin B) : ℕ), by omega⟩ : Fin B) = j := by
    ext; simp only; omega
  rw [e1, e2]

/-- A ring map out of `R_B` is determined by its values on constants and its image of the
universal polynomial. -/
theorem ringHom_eq_of_univPoly {B : ℕ} {S : Type*} [CommRing S] {ρ ρ' : RB B →+* S}
    (h : (univPoly B).map ρ = (univPoly B).map ρ')
    (hC : ∀ z : ℂ, ρ (MvPolynomial.C z) = ρ' (MvPolynomial.C z)) : ρ = ρ' := by
  apply MvPolynomial.ringHom_ext hC
  intro j
  have hc := congrArg (fun P => P.coeff (B - 1 - (j : ℕ))) h
  simp only [coeff_map, univPoly_coeff, map_mul] at hc
  have hunit : ρ (MvPolynomial.C ((-1 : ℂ) ^ ((j : ℕ) + 1))) *
      ρ (MvPolynomial.C ((-1 : ℂ) ^ ((j : ℕ) + 1))) = 1 := by
    rw [← map_mul, ← MvPolynomial.C_mul, ← mul_pow, neg_one_mul, neg_neg, one_pow,
      MvPolynomial.C_1, map_one]
  rw [← hC] at hc
  calc ρ (MvPolynomial.X j) = ρ (MvPolynomial.C ((-1 : ℂ) ^ ((j : ℕ) + 1))) *
        (ρ (MvPolynomial.C ((-1 : ℂ) ^ ((j : ℕ) + 1))) * ρ (MvPolynomial.X j)) := by
        rw [← mul_assoc, hunit, one_mul]
    _ = ρ' (MvPolynomial.X j) := by
        rw [hc, ← mul_assoc, hunit, one_mul]

/-- `ν_B` sends the universal polynomial to `A W³`. -/
theorem univPoly_map_nuB {B r s : ℕ} (hB : B = r + 3 * s) :
    (univPoly B).map (nuB B r s : RB B →+* Src r s) = genF r s := by
  subst hB
  apply eq_of_monic_of_coeff_lt ((univPoly_monic _).map _) (genF_monic r s) (n := r + 3 * s)
  · rw [(univPoly_monic _).natDegree_map, univPoly, natDegree_monicOf]
  · exact natDegree_genF r s
  · intro k hk
    have hk' : k = r + 3 * s - 1 - ((⟨r + 3 * s - 1 - k, by omega⟩ : Fin (r + 3 * s)) : ℕ) := by
      simp only; omega
    rw [coeff_map, hk', univPoly_coeff, map_mul, AlgHom.coe_toRingHom, nuB, MvPolynomial.aeval_C,
      MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq, ← mul_assoc]
    set m := ((⟨r + 3 * s - 1 - k, by omega⟩ : Fin (r + 3 * s)) : ℕ)
    have hu : (MvPolynomial.C ((-1 : ℂ) ^ (m + 1)) : Src r s) * (-1) ^ (m + 1) = 1 := by
      rw [map_pow, map_neg, map_one, ← mul_pow, neg_one_mul, neg_neg, one_pow]
    rw [hu, one_mul]
    congr 1
    simp only [m]
    omega

/-! ## Maps out of `CMod` and `A ⊗_{R_B} CMod` -/

section Lift

variable {B r s : ℕ}

/-- The `R_B`-algebra map `CMod B r s → S` sending the coordinates to `x`, when the pair with
coefficients `x` satisfies `A W³ = F_B`. -/
def coordLift (hB : B = r + 3 * s) {S : Type*} [CommRing S] [Algebra (RB B) S]
    (x : Fin r ⊕ Fin s → S)
    (hx : (genF r s).map (MvPolynomial.eval₂Hom ((algebraMap (RB B) S).comp MvPolynomial.C) x) =
      (univPoly B).map (algebraMap (RB B) S)) :
    CMod B r s →ₐ[RB B] S where
  toRingHom := MvPolynomial.eval₂Hom ((algebraMap (RB B) S).comp MvPolynomial.C) x
  commutes' a := by
    have h : (MvPolynomial.eval₂Hom ((algebraMap (RB B) S).comp MvPolynomial.C) x).comp
        (nuB B r s : RB B →+* Src r s) = algebraMap (RB B) S := by
      apply ringHom_eq_of_univPoly
      · rw [← Polynomial.map_map, univPoly_map_nuB hB, hx]
      · intro z
        simp [nuB]
    exact congrArg (fun φ : RB B →+* S => φ a) h

theorem coordLift_X (hB : B = r + 3 * s) {S : Type*} [CommRing S] [Algebra (RB B) S]
    (x : Fin r ⊕ Fin s → S) (hx) (v : Fin r ⊕ Fin s) :
    coordLift hB x hx (MvPolynomial.X v) = x v :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- The coordinate `X v` as an element of `CMod B r s`. -/
def cX (B : ℕ) {r s : ℕ} (v : Fin r ⊕ Fin s) : CMod B r s := MvPolynomial.X v

/-- The constant `z` as an element of `CMod B r s`. -/
def cC (B : ℕ) {r s : ℕ} (z : ℂ) : CMod B r s := MvPolynomial.C z

theorem cC_eq_algebraMap (z : ℂ) :
    cC B (r := r) (s := s) z = algebraMap (RB B) (CMod B r s) (MvPolynomial.C z) := by
  change MvPolynomial.C z = nuB B r s (MvPolynomial.C z)
  rw [nuB, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

variable {A : Type*} [CommRing A] [Algebra (RB B) A]

/-- The structure map `ℂ → S` through `R_B → A → S`. -/
abbrev cmap (B : ℕ) (A S : Type*) [CommRing A] [Algebra (RB B) A] [CommRing S] [Algebra A S] :
    ℂ →+* S :=
  (algebraMap A S).comp ((algebraMap (RB B) A).comp MvPolynomial.C)

/-- The lift, with the `R_B`-algebra structure on the target given. -/
def liftT' (hB : B = r + 3 * s) {S : Type*} [CommRing S] [Algebra A S] [Algebra (RB B) S]
    [IsScalarTower (RB B) A S] (x : Fin r ⊕ Fin s → S)
    (hx : (genF r s).map (MvPolynomial.eval₂Hom ((algebraMap (RB B) S).comp MvPolynomial.C) x) =
      (univPoly B).map (algebraMap (RB B) S)) :
    A ⊗[RB B] CMod B r s →ₐ[A] S :=
  Algebra.TensorProduct.lift (Algebra.ofId A S) (coordLift hB x hx) fun _ _ => Commute.all _ _

theorem liftT'_tmul (hB : B = r + 3 * s) {S : Type*} [CommRing S] [Algebra A S]
    [Algebra (RB B) S] [IsScalarTower (RB B) A S] (x : Fin r ⊕ Fin s → S) (hx) (a : A)
    (m : CMod B r s) :
    liftT' hB x hx (a ⊗ₜ m) = algebraMap A S a * coordLift hB x hx m :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- **Universal property of `A ⊗_{R_B} CMod B r s`.** -/
def liftT (hB : B = r + 3 * s) {S : Type*} [CommRing S] [Algebra A S] (x : Fin r ⊕ Fin s → S)
    (hx : (genF r s).map (MvPolynomial.eval₂Hom (cmap B A S) x) =
      ((univPoly B).map (algebraMap (RB B) A)).map (algebraMap A S)) :
    A ⊗[RB B] CMod B r s →ₐ[A] S :=
  letI : Algebra (RB B) S := ((algebraMap A S).comp (algebraMap (RB B) A)).toAlgebra
  haveI : IsScalarTower (RB B) A S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  liftT' hB x (by rw [Polynomial.map_map] at hx; exact hx)

theorem liftT_X (hB : B = r + 3 * s) {S : Type*} [CommRing S] [Algebra A S]
    (x : Fin r ⊕ Fin s → S) (hx) (v : Fin r ⊕ Fin s) :
    liftT hB x hx ((1 : A) ⊗ₜ cX B v) = x v := by
  let _ : Algebra (RB B) S := ((algebraMap A S).comp (algebraMap (RB B) A)).toAlgebra
  have _ : IsScalarTower (RB B) A S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  change liftT' hB x _ ((1 : A) ⊗ₜ cX B v) = x v
  rw [liftT'_tmul, map_one, one_mul]
  exact coordLift_X hB x _ v

/-- The ring map `ℂ[a, w] = CMod → A ⊗ CMod`. -/
abbrev incl (B r s : ℕ) (A : Type*) [CommRing A] [Algebra (RB B) A] :
    Src r s →+* A ⊗[RB B] CMod B r s :=
  (Algebra.TensorProduct.includeRight : CMod B r s →ₐ[RB B] A ⊗[RB B] CMod B r s).toRingHom

theorem incl_apply (m : Src r s) : incl B r s A m = (1 : A) ⊗ₜ (show CMod B r s from m) := rfl

/-- Maps out of `A ⊗_{R_B} CMod` are determined by the images of the coordinates. -/
theorem liftT_ext {S : Type*} [CommRing S] [Algebra A S] {F G : A ⊗[RB B] CMod B r s →ₐ[A] S}
    (h : ∀ v, F ((1 : A) ⊗ₜ cX B v) = G ((1 : A) ⊗ₜ cX B v)) : F = G := by
  have hR : (F : A ⊗[RB B] CMod B r s →+* S).comp (incl B r s A) =
      (G : A ⊗[RB B] CMod B r s →+* S).comp (incl B r s A) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      have hz : (1 : A) ⊗ₜ[RB B] cC B (r := r) (s := s) z =
          algebraMap A (A ⊗[RB B] CMod B r s) (algebraMap (RB B) A (MvPolynomial.C z)) := by
        rw [cC_eq_algebraMap, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply, Algebra.algebraMap_eq_smul_one (R := RB B) (A := A),
          Algebra.algebraMap_eq_smul_one (R := RB B) (A := CMod B r s), TensorProduct.smul_tmul]
      calc _ = F ((1 : A) ⊗ₜ cC B z) := rfl
        _ = G ((1 : A) ⊗ₜ cC B z) := by rw [hz, AlgHom.commutes, AlgHom.commutes]
        _ = _ := rfl
    · intro v
      exact h v
  ext x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a m =>
  have hm := congrArg (fun φ : Src r s →+* S => φ m) hR
  simp only [RingHom.coe_comp, Function.comp_apply, incl_apply, RingHom.coe_coe] at hm
  have hsplit : a ⊗ₜ[RB B] m = algebraMap A (A ⊗[RB B] CMod B r s) a * ((1 : A) ⊗ₜ m) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul]
    rfl
  rw [hsplit, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes]
  exact congrArg _ hm

end Lift

end KhanSL2.Collision.CoordSplit
