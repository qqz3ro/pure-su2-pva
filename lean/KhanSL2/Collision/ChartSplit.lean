module

public import KhanSL2.Collision.CoordSplit

@[expose] public section

/-!
# Splitting the coefficient coordinates on a chart

Let `A` be an `R_B`-algebra with `F_B = f₁ f₂`, `f₁, f₂` coprime monic of degrees `B₁, B₂`, the
`R_{Bᵢ}`-structures on `A` being given by the coefficients of `fᵢ`. Put
`T = A ⊗_{R_B} CMod B p s` (`B = p + 3s`): the universal `A`-algebra with a pair `(A, W)` of
monic polynomials of degrees `p, s` with `A W³ = f₁ f₂`.

The norm construction of `NormSplit` gives orthogonal idempotents `cA k`, `cW t` of `T`. On the
component `cA q · cW s₁ = 1` the pair splits as `(A' A'', W' W'')` with `A' W'³ = f₁` and
`A'' W''³ = f₂`, and this identifies the component with
`(A ⊗_{R_{B₁}} CMod B₁ q s₁) ⊗_A (A ⊗_{R_{B₂}} CMod B₂ r₂ s₂)` (`quotEquiv`).
-/

noncomputable section

open Polynomial TensorProduct

namespace KhanSL2.Collision.CoordSplit

open Depth NormSplit

/-! ## Generic facts -/

theorem monicOf_coeff {S : Type*} [CommRing S] {P : S[X]} {n : ℕ} (hP : P.Monic)
    (hd : Nontrivial S → P.natDegree = n) : monicOf n (fun k : Fin n => P.coeff k) = P := by
  cases subsingleton_or_nontrivial S
  · exact Subsingleton.elim _ _
  · exact eq_of_monic_of_coeff_lt (monicOf_monic _ _) hP (natDegree_monicOf _ _) (hd ‹_›)
      (fun k hk => coeff_monicOf n _ ⟨k, hk⟩)

theorem monicOf_monic' {S : Type*} [CommRing S] (n : ℕ) (f : Fin n → S) :
    (monicOf n f).Monic := by
  cases subsingleton_or_nontrivial S
  · exact Subsingleton.elim _ _
  · exact monicOf_monic n f

theorem genA_map_eq {r s : ℕ} {S : Type*} [CommRing S] (ψ : Src r s →+* S) :
    (genA r s).map ψ = monicOf r (fun k => ψ (MvPolynomial.X (Sum.inl k))) := by
  rw [genA, map_monicOf]; rfl

theorem genW_map_eq {r s : ℕ} {S : Type*} [CommRing S] (ψ : Src r s →+* S) :
    (genW r s).map ψ = monicOf s (fun k => ψ (MvPolynomial.X (Sum.inr k))) := by
  rw [genW, map_monicOf]; rfl

theorem genF_map_eval₂ {r s : ℕ} {S : Type*} [CommRing S] (f : ℂ →+* S)
    (x : Fin r ⊕ Fin s → S) :
    (genF r s).map (MvPolynomial.eval₂Hom f x) =
      monicOf r (fun k => x (Sum.inl k)) * monicOf s (fun k => x (Sum.inr k)) ^ 3 := by
  rw [genF, Polynomial.map_mul, Polynomial.map_pow, genA_map_eq, genW_map_eq]
  simp only [MvPolynomial.eval₂Hom_X']

section Incl

variable {B r s : ℕ} {A : Type*} [CommRing A] [Algebra (RB B) A]

theorem incl_nuB (c : RB B) :
    incl B r s A (nuB B r s c) =
      algebraMap A (A ⊗[RB B] CMod B r s) (algebraMap (RB B) A c) := by
  change (1 : A) ⊗ₜ[RB B] (algebraMap (RB B) (CMod B r s) c) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, Algebra.algebraMap_eq_smul_one (R := RB B) (A := A),
    Algebra.algebraMap_eq_smul_one (R := RB B) (A := CMod B r s), TensorProduct.smul_tmul]

/-- `A W³ = F_B` for the generic pair, pushed along any `A`-algebra map. -/
theorem genF_map_comp (hB : B = r + 3 * s) {S : Type*} [CommRing S] [Algebra A S]
    (φ : A ⊗[RB B] CMod B r s →ₐ[A] S) :
    (genF r s).map ((φ : A ⊗[RB B] CMod B r s →+* S).comp (incl B r s A)) =
      ((univPoly B).map (algebraMap (RB B) A)).map (algebraMap A S) := by
  rw [← univPoly_map_nuB hB, Polynomial.map_map, Polynomial.map_map]
  congr 1
  refine RingHom.ext fun c => ?_
  change φ (incl B r s A (nuB B r s c)) = _
  rw [incl_nuB, AlgHom.commutes]
  rfl

theorem liftT_comp_incl_X (hB : B = r + 3 * s) {S : Type*} [CommRing S] [Algebra A S]
    (x : Fin r ⊕ Fin s → S) (hx) (v : Fin r ⊕ Fin s) :
    ((liftT (A := A) hB x hx : A ⊗[RB B] CMod B r s →+* S).comp (incl B r s A))
      (MvPolynomial.X v) = x v :=
  liftT_X hB x hx v

theorem genA_map_liftT (hB : B = r + 3 * s) {S : Type*} [CommRing S] [Algebra A S]
    (x : Fin r ⊕ Fin s → S) (hx) :
    (genA r s).map ((liftT (A := A) hB x hx : A ⊗[RB B] CMod B r s →+* S).comp (incl B r s A)) =
      monicOf r (fun k => x (Sum.inl k)) := by
  rw [genA_map_eq]
  simp only [liftT_comp_incl_X]

theorem genW_map_liftT (hB : B = r + 3 * s) {S : Type*} [CommRing S] [Algebra A S]
    (x : Fin r ⊕ Fin s → S) (hx) :
    (genW r s).map ((liftT (A := A) hB x hx : A ⊗[RB B] CMod B r s →+* S).comp (incl B r s A)) =
      monicOf s (fun k => x (Sum.inr k)) := by
  rw [genW_map_eq]
  simp only [liftT_comp_incl_X]

end Incl

/-! ## Chart data -/

/-- A coprime factorization `F_B = f₁ f₂` on an `R_B`-algebra `A`, whose `R_{Bᵢ}`-algebra
structures are given by the coefficients of `fᵢ`. -/
structure Setup (B B₁ B₂ : ℕ) (A : Type*) [CommRing A] [Algebra (RB B) A] [Algebra (RB B₁) A]
    [Algebra (RB B₂) A] where
  f₁ : A[X]
  f₂ : A[X]
  α : A[X]
  β : A[X]
  monic₁ : f₁.Monic
  monic₂ : f₂.Monic
  deg₁ : f₁.natDegree = B₁
  deg₂ : f₂.natDegree = B₂
  factor : (univPoly B).map (algebraMap (RB B) A) = f₁ * f₂
  univ₁ : (univPoly B₁).map (algebraMap (RB B₁) A) = f₁
  univ₂ : (univPoly B₂).map (algebraMap (RB B₂) A) = f₂
  bezout : α * f₁ + β * f₂ = 1

namespace Setup

variable {B B₁ B₂ : ℕ} {A : Type*} [CommRing A] [Algebra (RB B) A] [Algebra (RB B₁) A]
  [Algebra (RB B₂) A] (D : Setup B B₁ B₂ A)

section Over

variable (S : Type*) [CommRing S] [Algebra A S]

/-- `f₁` over `S`. -/
def F₁ : S[X] := D.f₁.map (algebraMap A S)

/-- `f₂` over `S`. -/
def F₂ : S[X] := D.f₂.map (algebraMap A S)

/-- `α` over `S`. -/
def Ga : S[X] := D.α.map (algebraMap A S)

/-- `β` over `S`. -/
def Gb : S[X] := D.β.map (algebraMap A S)

theorem bezout_over : D.Ga S * D.F₁ S + D.Gb S * D.F₂ S = 1 := by
  simp only [F₁, F₂, Ga, Gb, ← Polynomial.map_mul, ← Polynomial.map_add, D.bezout,
    Polynomial.map_one]

theorem F₁_monic : (D.F₁ S).Monic := D.monic₁.map _

theorem F₂_monic : (D.F₂ S).Monic := D.monic₂.map _

theorem F₁_natDegree [Nontrivial S] : (D.F₁ S).natDegree = B₁ := by
  rw [F₁, D.monic₁.natDegree_map, D.deg₁]

theorem factor_over :
    ((univPoly B).map (algebraMap (RB B) A)).map (algebraMap A S) = D.F₁ S * D.F₂ S := by
  rw [D.factor, Polynomial.map_mul]; rfl

theorem univ₁_over :
    ((univPoly B₁).map (algebraMap (RB B₁) A)).map (algebraMap A S) = D.F₁ S := by
  rw [D.univ₁]; rfl

theorem univ₂_over :
    ((univPoly B₂).map (algebraMap (RB B₂) A)).map (algebraMap A S) = D.F₂ S := by
  rw [D.univ₂]; rfl

variable {S} {S' : Type*} [CommRing S'] [Algebra A S'] (φ : S →ₐ[A] S')

theorem F₁_map : (D.F₁ S).map (φ : S →+* S') = D.F₁ S' := by
  rw [F₁, F₁, Polynomial.map_map, AlgHom.comp_algebraMap]

theorem F₂_map : (D.F₂ S).map (φ : S →+* S') = D.F₂ S' := by
  rw [F₂, F₂, Polynomial.map_map, AlgHom.comp_algebraMap]

theorem Gb_map : (D.Gb S).map (φ : S →+* S') = D.Gb S' := by
  rw [Gb, Gb, Polynomial.map_map, AlgHom.comp_algebraMap]

theorem E_map : (D.Gb S * D.F₂ S).map (φ : S →+* S') = D.Gb S' * D.F₂ S' := by
  rw [Polynomial.map_mul, Gb_map, F₂_map]

end Over

/-! ## The ring `T = A ⊗_{R_B} CMod B p s` and its idempotents -/

variable (p s : ℕ)

/-- The generic `A` over `T`. -/
def AT : (A ⊗[RB B] CMod B p s)[X] := (genA p s).map (incl B p s A)

/-- The generic `W` over `T`. -/
def WT : (A ⊗[RB B] CMod B p s)[X] := (genW p s).map (incl B p s A)

/-- The idempotent `E = β f₂` over `T`. -/
def ET : (A ⊗[RB B] CMod B p s)[X] := D.Gb _ * D.F₂ _

/-- The idempotents attached to `A`. -/
def cA (k : ℕ) : A ⊗[RB B] CMod B p s := (cpoly p (AT p s) (D.ET p s)).coeff k

/-- The idempotents attached to `W`. -/
def cW (t : ℕ) : A ⊗[RB B] CMod B p s := (cpoly s (WT p s) (D.ET p s)).coeff t

omit [Algebra (RB B₁) A] [Algebra (RB B₂) A] in
theorem AT_monic : (AT (B := B) (A := A) p s).Monic := (genA_monic p s).map _

omit [Algebra (RB B₁) A] [Algebra (RB B₂) A] in
theorem WT_monic : (WT (B := B) (A := A) p s).Monic := (genW_monic p s).map _

omit [Algebra (RB B₁) A] [Algebra (RB B₂) A] in
theorem AT_natDegree [Nontrivial (A ⊗[RB B] CMod B p s)] :
    (AT (B := B) (A := A) p s).natDegree = p := by
  rw [AT, genA_map_eq, natDegree_monicOf]

omit [Algebra (RB B₁) A] [Algebra (RB B₂) A] in
theorem WT_natDegree [Nontrivial (A ⊗[RB B] CMod B p s)] :
    (WT (B := B) (A := A) p s).natDegree = s := by
  rw [WT, genW_map_eq, natDegree_monicOf]

omit [Algebra (RB B₁) A] [Algebra (RB B₂) A] in
theorem natDegree_eq_of_monicOf {S : Type*} [CommRing S] {P : S[X]} {n : ℕ} {f : Fin n → S}
    (h : P = monicOf n f) : Nontrivial S → P.natDegree = n := by
  intro _; rw [h, natDegree_monicOf]

variable {p s}

theorem AT_mul_WT (hB : B = p + 3 * s) :
    AT p s * WT p s ^ 3 = D.F₁ (A ⊗[RB B] CMod B p s) * D.F₂ _ := by
  have h := genF_map_comp hB (AlgHom.id A (A ⊗[RB B] CMod B p s))
  rw [D.factor_over] at h
  rw [← h, genF, Polynomial.map_mul, Polynomial.map_pow]
  rfl

theorem AT_map {S : Type*} [CommRing S] [Algebra A S] (φ : A ⊗[RB B] CMod B p s →ₐ[A] S) :
    (AT p s).map (φ : A ⊗[RB B] CMod B p s →+* S) =
      (genA p s).map ((φ : A ⊗[RB B] CMod B p s →+* S).comp (incl B p s A)) := by
  rw [AT, Polynomial.map_map]

theorem WT_map {S : Type*} [CommRing S] [Algebra A S] (φ : A ⊗[RB B] CMod B p s →ₐ[A] S) :
    (WT p s).map (φ : A ⊗[RB B] CMod B p s →+* S) =
      (genW p s).map ((φ : A ⊗[RB B] CMod B p s →+* S).comp (incl B p s A)) := by
  rw [WT, Polynomial.map_map]

end Setup

/-! ## The components -/

/-- The factorized side of a component. -/
abbrev TQ (B₁ B₂ q s₁ r₂ s₂ : ℕ) (A : Type*) [CommRing A] [Algebra (RB B₁) A]
    [Algebra (RB B₂) A] : Type _ :=
  (A ⊗[RB B₁] CMod B₁ q s₁) ⊗[A] (A ⊗[RB B₂] CMod B₂ r₂ s₂)

section TQ

variable {B₁ B₂ q s₁ r₂ s₂ : ℕ} {A : Type*} [CommRing A] [Algebra (RB B₁) A] [Algebra (RB B₂) A]

variable (B₁ B₂ q s₁ r₂ s₂ A) in
/-- `ℂ[a', w'] → TQ`. -/
abbrev ι₁ : Src q s₁ →+* TQ B₁ B₂ q s₁ r₂ s₂ A :=
  ((Algebra.TensorProduct.includeLeft :
    (A ⊗[RB B₁] CMod B₁ q s₁) →ₐ[A] TQ B₁ B₂ q s₁ r₂ s₂ A) :
      (A ⊗[RB B₁] CMod B₁ q s₁) →+* TQ B₁ B₂ q s₁ r₂ s₂ A).comp (incl B₁ q s₁ A)

variable (B₁ B₂ q s₁ r₂ s₂ A) in
/-- `ℂ[a'', w''] → TQ`. -/
abbrev ι₂ : Src r₂ s₂ →+* TQ B₁ B₂ q s₁ r₂ s₂ A :=
  ((Algebra.TensorProduct.includeRight :
    (A ⊗[RB B₂] CMod B₂ r₂ s₂) →ₐ[A] TQ B₁ B₂ q s₁ r₂ s₂ A) :
      (A ⊗[RB B₂] CMod B₂ r₂ s₂) →+* TQ B₁ B₂ q s₁ r₂ s₂ A).comp (incl B₂ r₂ s₂ A)

variable (B₁ B₂ q s₁ r₂ s₂ A) in
/-- The generic `A'`. -/
def A1 : (TQ B₁ B₂ q s₁ r₂ s₂ A)[X] := (genA q s₁).map (ι₁ B₁ B₂ q s₁ r₂ s₂ A)

variable (B₁ B₂ q s₁ r₂ s₂ A) in
/-- The generic `W'`. -/
def W1 : (TQ B₁ B₂ q s₁ r₂ s₂ A)[X] := (genW q s₁).map (ι₁ B₁ B₂ q s₁ r₂ s₂ A)

variable (B₁ B₂ q s₁ r₂ s₂ A) in
/-- The generic `A''`. -/
def A2 : (TQ B₁ B₂ q s₁ r₂ s₂ A)[X] := (genA r₂ s₂).map (ι₂ B₁ B₂ q s₁ r₂ s₂ A)

variable (B₁ B₂ q s₁ r₂ s₂ A) in
/-- The generic `W''`. -/
def W2 : (TQ B₁ B₂ q s₁ r₂ s₂ A)[X] := (genW r₂ s₂).map (ι₂ B₁ B₂ q s₁ r₂ s₂ A)

theorem A1_eq : A1 B₁ B₂ q s₁ r₂ s₂ A =
    monicOf q (fun k => ι₁ B₁ B₂ q s₁ r₂ s₂ A (MvPolynomial.X (Sum.inl k))) := genA_map_eq _

theorem W1_eq : W1 B₁ B₂ q s₁ r₂ s₂ A =
    monicOf s₁ (fun k => ι₁ B₁ B₂ q s₁ r₂ s₂ A (MvPolynomial.X (Sum.inr k))) := genW_map_eq _

theorem A2_eq : A2 B₁ B₂ q s₁ r₂ s₂ A =
    monicOf r₂ (fun k => ι₂ B₁ B₂ q s₁ r₂ s₂ A (MvPolynomial.X (Sum.inl k))) := genA_map_eq _

theorem W2_eq : W2 B₁ B₂ q s₁ r₂ s₂ A =
    monicOf s₂ (fun k => ι₂ B₁ B₂ q s₁ r₂ s₂ A (MvPolynomial.X (Sum.inr k))) := genW_map_eq _

end TQ

namespace Setup

variable {B B₁ B₂ : ℕ} {A : Type*} [CommRing A] [Algebra (RB B) A] [Algebra (RB B₁) A]
  [Algebra (RB B₂) A] (D : Setup B B₁ B₂ A)

section Component

variable {p s q s₁ r₂ s₂ : ℕ}

local notation "𝕋" => TQ B₁ B₂ q s₁ r₂ s₂ A
local notation "𝕊" => A ⊗[RB B] CMod B p s

theorem A1_mul_W1 (hB₁ : B₁ = q + 3 * s₁) :
    A1 B₁ B₂ q s₁ r₂ s₂ A * W1 B₁ B₂ q s₁ r₂ s₂ A ^ 3 = D.F₁ 𝕋 := by
  have h := genF_map_comp hB₁ (Algebra.TensorProduct.includeLeft :
    (A ⊗[RB B₁] CMod B₁ q s₁) →ₐ[A] 𝕋)
  rw [D.univ₁_over] at h
  rw [← h, genF, Polynomial.map_mul, Polynomial.map_pow]
  rfl

theorem A2_mul_W2 (hB₂ : B₂ = r₂ + 3 * s₂) :
    A2 B₁ B₂ q s₁ r₂ s₂ A * W2 B₁ B₂ q s₁ r₂ s₂ A ^ 3 = D.F₂ 𝕋 := by
  have h := genF_map_comp hB₂ (Algebra.TensorProduct.includeRight :
    (A ⊗[RB B₂] CMod B₂ r₂ s₂) →ₐ[A] 𝕋)
  rw [D.univ₂_over] at h
  rw [← h, genF, Polynomial.map_mul, Polynomial.map_pow]
  rfl


theorem TQ_A_split (hB₁ : B₁ = q + 3 * s₁) (hB₂ : B₂ = r₂ + 3 * s₂) (hp : p = q + r₂) :
    cpoly p (A1 B₁ B₂ q s₁ r₂ s₂ A * A2 B₁ B₂ q s₁ r₂ s₂ A) (D.Gb 𝕋 * D.F₂ 𝕋) = X ^ q ∧
      Gpoly p (A1 B₁ B₂ q s₁ r₂ s₂ A * A2 B₁ B₂ q s₁ r₂ s₂ A) (D.Gb 𝕋 * D.F₂ 𝕋) =
        A1 B₁ B₂ q s₁ r₂ s₂ A ∧
      Gpoly p (A1 B₁ B₂ q s₁ r₂ s₂ A * A2 B₁ B₂ q s₁ r₂ s₂ A) (1 - D.Gb 𝕋 * D.F₂ 𝕋) =
        A2 B₁ B₂ q s₁ r₂ s₂ A := by
  have m1 : (A1 B₁ B₂ q s₁ r₂ s₂ A).Monic := by rw [A1_eq]; exact monicOf_monic' _ _
  have m2 : (A2 B₁ B₂ q s₁ r₂ s₂ A).Monic := by rw [A2_eq]; exact monicOf_monic' _ _
  refine cpoly_of_split' (D.bezout_over 𝕋) (m1.mul m2) (fun hnt => ?_) m1 rfl
    ⟨_, (D.A1_mul_W1 hB₁).symm⟩ ⟨_, (D.A2_mul_W2 hB₂).symm⟩
    (fun _ => by rw [A1_eq, natDegree_monicOf])
  have := hnt
  rw [m1.natDegree_mul m2, A1_eq, A2_eq, natDegree_monicOf, natDegree_monicOf, hp]

theorem TQ_W_split (hB₁ : B₁ = q + 3 * s₁) (hB₂ : B₂ = r₂ + 3 * s₂) (hs : s = s₁ + s₂) :
    cpoly s (W1 B₁ B₂ q s₁ r₂ s₂ A * W2 B₁ B₂ q s₁ r₂ s₂ A) (D.Gb 𝕋 * D.F₂ 𝕋) = X ^ s₁ ∧
      Gpoly s (W1 B₁ B₂ q s₁ r₂ s₂ A * W2 B₁ B₂ q s₁ r₂ s₂ A) (D.Gb 𝕋 * D.F₂ 𝕋) =
        W1 B₁ B₂ q s₁ r₂ s₂ A ∧
      Gpoly s (W1 B₁ B₂ q s₁ r₂ s₂ A * W2 B₁ B₂ q s₁ r₂ s₂ A) (1 - D.Gb 𝕋 * D.F₂ 𝕋) =
        W2 B₁ B₂ q s₁ r₂ s₂ A := by
  have m1 : (W1 B₁ B₂ q s₁ r₂ s₂ A).Monic := by rw [W1_eq]; exact monicOf_monic' _ _
  have m2 : (W2 B₁ B₂ q s₁ r₂ s₂ A).Monic := by rw [W2_eq]; exact monicOf_monic' _ _
  refine cpoly_of_split' (D.bezout_over 𝕋) (m1.mul m2) (fun hnt => ?_) m1 rfl
    ⟨A1 B₁ B₂ q s₁ r₂ s₂ A * W1 B₁ B₂ q s₁ r₂ s₂ A ^ 2, by rw [← D.A1_mul_W1 hB₁]; ring⟩
    ⟨A2 B₁ B₂ q s₁ r₂ s₂ A * W2 B₁ B₂ q s₁ r₂ s₂ A ^ 2, by rw [← D.A2_mul_W2 hB₂]; ring⟩
    (fun _ => by rw [W1_eq, natDegree_monicOf])
  have := hnt
  rw [m1.natDegree_mul m2, W1_eq, W2_eq, natDegree_monicOf, natDegree_monicOf, hs]

variable (q s₁ r₂ s₂) in
/-- The coordinates of the product pair `(A' A'', W' W'')`. -/
def xPhi : Fin p ⊕ Fin s → 𝕋 :=
  Sum.elim (fun i => (A1 B₁ B₂ q s₁ r₂ s₂ A * A2 B₁ B₂ q s₁ r₂ s₂ A).coeff i)
    (fun i => (W1 B₁ B₂ q s₁ r₂ s₂ A * W2 B₁ B₂ q s₁ r₂ s₂ A).coeff i)

omit [Algebra (RB B) A] in
theorem A1A2_eq (hp : p = q + r₂) :
    monicOf p (fun k => (xPhi (s := s) q s₁ r₂ s₂ (Sum.inl k) : 𝕋)) =
      A1 B₁ B₂ q s₁ r₂ s₂ A * A2 B₁ B₂ q s₁ r₂ s₂ A := by
  have m1 : (A1 B₁ B₂ q s₁ r₂ s₂ A).Monic := by rw [A1_eq]; exact monicOf_monic' _ _
  have m2 : (A2 B₁ B₂ q s₁ r₂ s₂ A).Monic := by rw [A2_eq]; exact monicOf_monic' _ _
  refine monicOf_coeff (m1.mul m2) fun hnt => ?_
  have := hnt
  rw [m1.natDegree_mul m2, A1_eq, A2_eq, natDegree_monicOf, natDegree_monicOf, hp]

omit [Algebra (RB B) A] in
theorem W1W2_eq (hs : s = s₁ + s₂) :
    monicOf s (fun k => (xPhi (p := p) q s₁ r₂ s₂ (Sum.inr k) : 𝕋)) =
      W1 B₁ B₂ q s₁ r₂ s₂ A * W2 B₁ B₂ q s₁ r₂ s₂ A := by
  have m1 : (W1 B₁ B₂ q s₁ r₂ s₂ A).Monic := by rw [W1_eq]; exact monicOf_monic' _ _
  have m2 : (W2 B₁ B₂ q s₁ r₂ s₂ A).Monic := by rw [W2_eq]; exact monicOf_monic' _ _
  refine monicOf_coeff (m1.mul m2) fun hnt => ?_
  have := hnt
  rw [m1.natDegree_mul m2, W1_eq, W2_eq, natDegree_monicOf, natDegree_monicOf, hs]

include D in
theorem xPhi_spec (hB₁ : B₁ = q + 3 * s₁) (hB₂ : B₂ = r₂ + 3 * s₂) (hp : p = q + r₂)
    (hs : s = s₁ + s₂) :
    (genF p s).map (MvPolynomial.eval₂Hom (cmap B A 𝕋) (xPhi q s₁ r₂ s₂)) =
      ((univPoly B).map (algebraMap (RB B) A)).map (algebraMap A 𝕋) := by
  rw [genF_map_eval₂, D.factor_over, A1A2_eq hp, W1W2_eq hs, ← D.A1_mul_W1 hB₁,
    ← D.A2_mul_W2 hB₂]
  ring

/-- `Φ : T → TQ`, classifying the product pair. -/
def Phi (hB : B = p + 3 * s) (hB₁ : B₁ = q + 3 * s₁) (hB₂ : B₂ = r₂ + 3 * s₂) (hp : p = q + r₂)
    (hs : s = s₁ + s₂) : 𝕊 →ₐ[A] 𝕋 :=
  liftT hB (xPhi q s₁ r₂ s₂) (D.xPhi_spec hB₁ hB₂ hp hs)


/-! ### Generic facts over an `A`-algebra receiving `T` -/

section OverS

variable {S : Type*} [CommRing S] [Algebra A S] (φ : A ⊗[RB B] CMod B p s →ₐ[A] S)

omit [Algebra (RB B₁) A] [Algebra (RB B₂) A] in
theorem ATmap_eq : (AT (B := B) (A := A) p s).map (φ : 𝕊 →+* S) =
    monicOf p (fun k => φ (incl B p s A (MvPolynomial.X (Sum.inl k)))) := by
  rw [AT_map, genA_map_eq]; rfl

omit [Algebra (RB B₁) A] [Algebra (RB B₂) A] in
theorem WTmap_eq : (WT (B := B) (A := A) p s).map (φ : 𝕊 →+* S) =
    monicOf s (fun k => φ (incl B p s A (MvPolynomial.X (Sum.inr k)))) := by
  rw [WT_map, genW_map_eq]; rfl

omit [Algebra (RB B₁) A] [Algebra (RB B₂) A] in
theorem ATmap_deg :
    Nontrivial S → ((AT (B := B) (A := A) p s).map (φ : 𝕊 →+* S)).natDegree = p := fun _ => by
  rw [ATmap_eq, natDegree_monicOf]

omit [Algebra (RB B₁) A] [Algebra (RB B₂) A] in
theorem WTmap_deg :
    Nontrivial S → ((WT (B := B) (A := A) p s).map (φ : 𝕊 →+* S)).natDegree = s := fun _ => by
  rw [WTmap_eq, natDegree_monicOf]

theorem ATWT_map (hB : B = p + 3 * s) :
    (AT (B := B) (A := A) p s).map (φ : 𝕊 →+* S) *
      (WT (B := B) (A := A) p s).map (φ : 𝕊 →+* S) ^ 3 = D.F₁ S * D.F₂ S := by
  have h := congrArg (Polynomial.map (φ : 𝕊 →+* S)) (D.AT_mul_WT hB)
  rwa [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_mul, F₁_map, F₂_map] at h

theorem ATmap_dvd (hB : B = p + 3 * s) :
    (AT (B := B) (A := A) p s).map (φ : 𝕊 →+* S) ∣ D.F₁ S * D.F₂ S := ⟨_, (D.ATWT_map φ hB).symm⟩

theorem WTmap_dvd (hB : B = p + 3 * s) :
    (WT (B := B) (A := A) p s).map (φ : 𝕊 →+* S) ∣ D.F₁ S * D.F₂ S :=
  ⟨(AT (B := B) (A := A) p s).map (φ : 𝕊 →+* S) *
      (WT (B := B) (A := A) p s).map (φ : 𝕊 →+* S) ^ 2, by
    rw [← D.ATWT_map φ hB]; ring⟩

end OverS

theorem AT_dvd_idem (hB : B = p + 3 * s) :
    AT p s ∣ D.ET p s * D.ET p s - D.ET p s := by
  have h := D.ATmap_dvd (AlgHom.id A 𝕊) hB
  rw [AlgHom.id_toRingHom, Polynomial.map_id] at h
  exact idem_dvd (D.bezout_over 𝕊) h

theorem WT_dvd_idem (hB : B = p + 3 * s) :
    WT p s ∣ D.ET p s * D.ET p s - D.ET p s := by
  have h := D.WTmap_dvd (AlgHom.id A 𝕊) hB
  rw [AlgHom.id_toRingHom, Polynomial.map_id] at h
  exact idem_dvd (D.bezout_over 𝕊) h

theorem cA_idem (hB : B = p + 3 * s) (k : ℕ) : D.cA p s k * D.cA p s k = D.cA p s k :=
  cpoly_coeff_idem' (AT_monic p s) (fun _ => AT_natDegree p s) (D.AT_dvd_idem hB) k

theorem cW_idem (hB : B = p + 3 * s) (t : ℕ) : D.cW p s t * D.cW p s t = D.cW p s t :=
  cpoly_coeff_idem' (WT_monic p s) (fun _ => WT_natDegree p s) (D.WT_dvd_idem hB) t

/-! ### `Φ` -/

theorem AT_map_Phi (hB : B = p + 3 * s) (hB₁ : B₁ = q + 3 * s₁) (hB₂ : B₂ = r₂ + 3 * s₂)
    (hp : p = q + r₂) (hs : s = s₁ + s₂) :
    (AT (B := B) (A := A) p s).map (D.Phi hB hB₁ hB₂ hp hs : 𝕊 →+* 𝕋) =
      A1 B₁ B₂ q s₁ r₂ s₂ A * A2 B₁ B₂ q s₁ r₂ s₂ A := by
  rw [AT_map, Phi, genA_map_liftT]
  exact A1A2_eq hp

theorem WT_map_Phi (hB : B = p + 3 * s) (hB₁ : B₁ = q + 3 * s₁) (hB₂ : B₂ = r₂ + 3 * s₂)
    (hp : p = q + r₂) (hs : s = s₁ + s₂) :
    (WT (B := B) (A := A) p s).map (D.Phi hB hB₁ hB₂ hp hs : 𝕊 →+* 𝕋) =
      W1 B₁ B₂ q s₁ r₂ s₂ A * W2 B₁ B₂ q s₁ r₂ s₂ A := by
  rw [WT_map, Phi, genW_map_liftT]
  exact W1W2_eq hs

theorem Phi_cA (hB : B = p + 3 * s) (hB₁ : B₁ = q + 3 * s₁) (hB₂ : B₂ = r₂ + 3 * s₂)
    (hp : p = q + r₂) (hs : s = s₁ + s₂) : D.Phi hB hB₁ hB₂ hp hs (D.cA p s q) = 1 := by
  have h := congrArg (fun P => P.coeff q) (cpoly_map (n := p) (E := D.ET p s)
    (D.Phi hB hB₁ hB₂ hp hs : 𝕊 →+* 𝕋) (AT_monic p s))
  simp only [coeff_map] at h
  rw [D.AT_map_Phi, ET, E_map, (D.TQ_A_split hB₁ hB₂ hp).1, coeff_X_pow_self] at h
  exact h

theorem Phi_cW (hB : B = p + 3 * s) (hB₁ : B₁ = q + 3 * s₁) (hB₂ : B₂ = r₂ + 3 * s₂)
    (hp : p = q + r₂) (hs : s = s₁ + s₂) : D.Phi hB hB₁ hB₂ hp hs (D.cW p s s₁) = 1 := by
  have h := congrArg (fun P => P.coeff s₁) (cpoly_map (n := s) (E := D.ET p s)
    (D.Phi hB hB₁ hB₂ hp hs : 𝕊 →+* 𝕋) (WT_monic p s))
  simp only [coeff_map] at h
  rw [D.WT_map_Phi, ET, E_map, (D.TQ_W_split hB₁ hB₂ hs).1, coeff_X_pow_self] at h
  exact h


/-! ### The component `T ⧸ (1 - cA q · cW s₁)` and `Ψ` -/

variable (p s q s₁) in
/-- The ideal cutting out a component. -/
abbrev Ib : Ideal (A ⊗[RB B] CMod B p s) := Ideal.span {1 - D.cA p s q * D.cW p s s₁}

local notation "𝔹" => (A ⊗[RB B] CMod B p s) ⧸ D.Ib p s q s₁

variable (p s q s₁) in
/-- The projection onto a component. -/
abbrev πb : (A ⊗[RB B] CMod B p s) →ₐ[A] 𝔹 := Ideal.Quotient.mkₐ A _

theorem πb_cA (hB : B = p + 3 * s) : D.πb p s q s₁ (D.cA p s q) = 1 := by
  have he : D.πb p s q s₁ (D.cA p s q * D.cW p s s₁) = 1 := quot_idem_eq_one _
  calc D.πb p s q s₁ (D.cA p s q)
      = D.πb p s q s₁ (D.cA p s q) * D.πb p s q s₁ (D.cA p s q * D.cW p s s₁) := by
        rw [he, mul_one]
    _ = 1 := by rw [← map_mul, ← mul_assoc, D.cA_idem hB, he]

theorem πb_cW (hB : B = p + 3 * s) : D.πb p s q s₁ (D.cW p s s₁) = 1 := by
  have he : D.πb p s q s₁ (D.cA p s q * D.cW p s s₁) = 1 := quot_idem_eq_one _
  calc D.πb p s q s₁ (D.cW p s s₁)
      = D.πb p s q s₁ (D.cW p s s₁) * D.πb p s q s₁ (D.cA p s q * D.cW p s s₁) := by
        rw [he, mul_one]
    _ = 1 := by rw [← map_mul, mul_comm (D.cA p s q), ← mul_assoc, D.cW_idem hB, mul_comm, he]

theorem cA_bar (hB : B = p + 3 * s) :
    cpoly p ((AT p s).map (D.πb p s q s₁ : 𝕊 →+* 𝔹)) (D.Gb 𝔹 * D.F₂ 𝔹) = X ^ q := by
  have h := cpoly_map_eq_X_pow' (AT_monic p s) (fun _ => AT_natDegree p s) (D.AT_dvd_idem hB)
    (D.πb p s q s₁ : 𝕊 →+* 𝔹) (D.πb_cA hB)
  rwa [ET, E_map] at h

theorem cW_bar (hB : B = p + 3 * s) :
    cpoly s ((WT p s).map (D.πb p s q s₁ : 𝕊 →+* 𝔹)) (D.Gb 𝔹 * D.F₂ 𝔹) = X ^ s₁ := by
  have h := cpoly_map_eq_X_pow' (WT_monic p s) (fun _ => WT_natDegree p s) (D.WT_dvd_idem hB)
    (D.πb p s q s₁ : 𝕊 →+* 𝔹) (D.πb_cW hB)
  rwa [ET, E_map] at h

variable (p s q s₁) in
/-- `A'` on the component. -/
def A1b : 𝔹[X] := Gpoly p ((AT p s).map (D.πb p s q s₁ : 𝕊 →+* 𝔹)) (D.Gb 𝔹 * D.F₂ 𝔹)

variable (p s q s₁) in
/-- `A''` on the component. -/
def A2b : 𝔹[X] := Gpoly p ((AT p s).map (D.πb p s q s₁ : 𝕊 →+* 𝔹)) (1 - D.Gb 𝔹 * D.F₂ 𝔹)

variable (p s q s₁) in
/-- `W'` on the component. -/
def W1b : 𝔹[X] := Gpoly s ((WT p s).map (D.πb p s q s₁ : 𝕊 →+* 𝔹)) (D.Gb 𝔹 * D.F₂ 𝔹)

variable (p s q s₁) in
/-- `W''` on the component. -/
def W2b : 𝔹[X] := Gpoly s ((WT p s).map (D.πb p s q s₁ : 𝕊 →+* 𝔹)) (1 - D.Gb 𝔹 * D.F₂ 𝔹)

theorem bar_split (hB : B = p + 3 * s) (hp : p = q + r₂) (hs : s = s₁ + s₂) :
    D.A1b p s q s₁ * D.W1b p s q s₁ ^ 3 = D.F₁ 𝔹 ∧
    D.A2b p s q s₁ * D.W2b p s q s₁ ^ 3 = D.F₂ 𝔹 ∧
    D.A1b p s q s₁ * D.A2b p s q s₁ = (AT p s).map (D.πb p s q s₁ : 𝕊 →+* 𝔹) ∧
    D.W1b p s q s₁ * D.W2b p s q s₁ = (WT p s).map (D.πb p s q s₁ : 𝕊 →+* 𝔹) ∧
    (D.A1b p s q s₁).Monic ∧ (D.A2b p s q s₁).Monic ∧ (D.W1b p s q s₁).Monic ∧
    (D.W2b p s q s₁).Monic ∧
    (Nontrivial 𝔹 → (D.A1b p s q s₁).natDegree = q ∧ (D.A2b p s q s₁).natDegree = r₂ ∧
      (D.W1b p s q s₁).natDegree = s₁ ∧ (D.W2b p s q s₁).natDegree = s₂) := by
  unfold A1b A2b W1b W2b
  obtain ⟨pA, mA1, mA2, dA, -, -⟩ := split_one' (D.bezout_over 𝔹) ((AT_monic p s).map _)
    (ATmap_deg _) (D.ATmap_dvd _ hB) (D.cA_bar hB)
  obtain ⟨pW, mW1, mW2, dW, -, -⟩ := split_one' (D.bezout_over 𝔹) ((WT_monic p s).map _)
    (WTmap_deg _) (D.WTmap_dvd _ hB) (D.cW_bar hB)
  obtain ⟨e1, e2, -⟩ := pair_split' (D.bezout_over 𝔹) ((AT_monic p s).map _) (ATmap_deg _)
    ((WT_monic p s).map _) (WTmap_deg _) (D.F₁_monic 𝔹) (fun _ => D.F₁_natDegree 𝔹)
    (D.F₂_monic 𝔹) (D.ATWT_map _ hB) (D.cA_bar hB) (D.cW_bar hB)
  refine ⟨e1, e2, pA, pW, mA1, mA2, mW1, mW2, fun hnt => ?_⟩
  have h1 := (dA hnt).1
  have h2 := (dW hnt).1
  have h3 := congrArg natDegree pA
  have h4 := congrArg natDegree pW
  rw [mA1.natDegree_mul mA2, ATmap_deg _ hnt] at h3
  rw [mW1.natDegree_mul mW2, WTmap_deg _ hnt] at h4
  refine ⟨h1, ?_, h2, ?_⟩ <;> omega

variable (p s q s₁) in
/-- The coordinates of `(A', W')` on the component. -/
def x1 : Fin q ⊕ Fin s₁ → 𝔹 :=
  Sum.elim (fun i => (D.A1b p s q s₁).coeff i) (fun i => (D.W1b p s q s₁).coeff i)

variable (p s q s₁ r₂ s₂) in
/-- The coordinates of `(A'', W'')` on the component. -/
def x2 : Fin r₂ ⊕ Fin s₂ → 𝔹 :=
  Sum.elim (fun i => (D.A2b p s q s₁).coeff i) (fun i => (D.W2b p s q s₁).coeff i)

theorem x1_spec (hB : B = p + 3 * s) (hp : p = q + r₂) (hs : s = s₁ + s₂) :
    (genF q s₁).map (MvPolynomial.eval₂Hom (cmap B₁ A 𝔹) (D.x1 p s q s₁)) =
      ((univPoly B₁).map (algebraMap (RB B₁) A)).map (algebraMap A 𝔹) := by
  obtain ⟨e1, -, -, -, mA1, -, mW1, -, hd⟩ := D.bar_split hB hp hs
  rw [genF_map_eval₂, D.univ₁_over]
  simp only [x1, Sum.elim_inl, Sum.elim_inr]
  rw [monicOf_coeff mA1 (fun h => (hd h).1), monicOf_coeff mW1 (fun h => (hd h).2.2.1)]
  exact e1

theorem x2_spec (hB : B = p + 3 * s) (hp : p = q + r₂) (hs : s = s₁ + s₂) :
    (genF r₂ s₂).map (MvPolynomial.eval₂Hom (cmap B₂ A 𝔹) (D.x2 p s q s₁ r₂ s₂)) =
      ((univPoly B₂).map (algebraMap (RB B₂) A)).map (algebraMap A 𝔹) := by
  obtain ⟨-, e2, -, -, -, mA2, -, mW2, hd⟩ := D.bar_split hB hp hs
  rw [genF_map_eval₂, D.univ₂_over]
  simp only [x2, Sum.elim_inl, Sum.elim_inr]
  rw [monicOf_coeff mA2 (fun h => (hd h).2.1), monicOf_coeff mW2 (fun h => (hd h).2.2.2)]
  exact e2

/-- `Ψ : TQ → T ⧸ (1 - e)`, classifying the split pair. -/
def Psi (hB : B = p + 3 * s) (hB₁ : B₁ = q + 3 * s₁) (hB₂ : B₂ = r₂ + 3 * s₂) (hp : p = q + r₂)
    (hs : s = s₁ + s₂) : 𝕋 →ₐ[A] 𝔹 :=
  Algebra.TensorProduct.productMap (liftT hB₁ (D.x1 p s q s₁) (D.x1_spec hB hp hs))
    (liftT hB₂ (D.x2 p s q s₁ r₂ s₂) (D.x2_spec hB hp hs))


section Maps

variable (hB : B = p + 3 * s) (hB₁ : B₁ = q + 3 * s₁) (hB₂ : B₂ = r₂ + 3 * s₂) (hp : p = q + r₂)
  (hs : s = s₁ + s₂)

include hB hB₁ hB₂ hp hs

theorem A1_map_Psi : (A1 B₁ B₂ q s₁ r₂ s₂ A).map (D.Psi hB hB₁ hB₂ hp hs : 𝕋 →+* 𝔹) =
    D.A1b p s q s₁ := by
  obtain ⟨-, -, -, -, m, -, -, -, hd⟩ := D.bar_split hB hp hs
  rw [A1, Polynomial.map_map, genA_map_eq]
  refine Eq.trans ?_ (monicOf_coeff m (fun h => (hd h).1))
  congr 1
  funext k
  change D.Psi hB hB₁ hB₂ hp hs ((1 : A) ⊗ₜ[RB B₁] cX B₁ (Sum.inl k) ⊗ₜ[A] 1) = _
  rw [Psi, Algebra.TensorProduct.productMap_left_apply, liftT_X]
  rfl

theorem W1_map_Psi : (W1 B₁ B₂ q s₁ r₂ s₂ A).map (D.Psi hB hB₁ hB₂ hp hs : 𝕋 →+* 𝔹) =
    D.W1b p s q s₁ := by
  obtain ⟨-, -, -, -, -, -, m, -, hd⟩ := D.bar_split hB hp hs
  rw [W1, Polynomial.map_map, genW_map_eq]
  refine Eq.trans ?_ (monicOf_coeff m (fun h => (hd h).2.2.1))
  congr 1
  funext k
  change D.Psi hB hB₁ hB₂ hp hs ((1 : A) ⊗ₜ[RB B₁] cX B₁ (Sum.inr k) ⊗ₜ[A] 1) = _
  rw [Psi, Algebra.TensorProduct.productMap_left_apply, liftT_X]
  rfl

theorem A2_map_Psi : (A2 B₁ B₂ q s₁ r₂ s₂ A).map (D.Psi hB hB₁ hB₂ hp hs : 𝕋 →+* 𝔹) =
    D.A2b p s q s₁ := by
  obtain ⟨-, -, -, -, -, m, -, -, hd⟩ := D.bar_split hB hp hs
  rw [A2, Polynomial.map_map, genA_map_eq]
  refine Eq.trans ?_ (monicOf_coeff m (fun h => (hd h).2.1))
  congr 1
  funext k
  change D.Psi hB hB₁ hB₂ hp hs ((1 : A ⊗[RB B₁] CMod B₁ q s₁) ⊗ₜ[A]
    ((1 : A) ⊗ₜ[RB B₂] cX B₂ (Sum.inl k))) = _
  rw [Psi, Algebra.TensorProduct.productMap_right_apply, liftT_X]
  rfl

theorem W2_map_Psi : (W2 B₁ B₂ q s₁ r₂ s₂ A).map (D.Psi hB hB₁ hB₂ hp hs : 𝕋 →+* 𝔹) =
    D.W2b p s q s₁ := by
  obtain ⟨-, -, -, -, -, -, -, m, hd⟩ := D.bar_split hB hp hs
  rw [W2, Polynomial.map_map, genW_map_eq]
  refine Eq.trans ?_ (monicOf_coeff m (fun h => (hd h).2.2.2))
  congr 1
  funext k
  change D.Psi hB hB₁ hB₂ hp hs ((1 : A ⊗[RB B₁] CMod B₁ q s₁) ⊗ₜ[A]
    ((1 : A) ⊗ₜ[RB B₂] cX B₂ (Sum.inr k))) = _
  rw [Psi, Algebra.TensorProduct.productMap_right_apply, liftT_X]
  rfl

omit hB hB₁ hB₂ hp hs in
theorem AT_coeff (i : Fin p) :
    (AT (B := B) (A := A) p s).coeff i = (1 : A) ⊗ₜ[RB B] cX B (Sum.inl i) := by
  rw [AT, coeff_map, genA, coeff_monicOf]
  rfl

omit hB hB₁ hB₂ hp hs in
theorem WT_coeff (i : Fin s) :
    (WT (B := B) (A := A) p s).coeff i = (1 : A) ⊗ₜ[RB B] cX B (Sum.inr i) := by
  rw [WT, coeff_map, genW, coeff_monicOf]
  rfl

theorem Psi_Phi :
    (D.Psi hB hB₁ hB₂ hp hs).comp (D.Phi hB hB₁ hB₂ hp hs) = D.πb p s q s₁ := by
  obtain ⟨-, -, pA, pW, -⟩ := D.bar_split hB hp hs
  apply liftT_ext
  intro v
  rw [AlgHom.comp_apply, Phi, liftT_X]
  rcases v with i | i
  · have h := congrArg (fun P => P.coeff i)
      (show (A1 B₁ B₂ q s₁ r₂ s₂ A * A2 B₁ B₂ q s₁ r₂ s₂ A).map
          (D.Psi hB hB₁ hB₂ hp hs : 𝕋 →+* 𝔹) = (AT p s).map (D.πb p s q s₁ : 𝕊 →+* 𝔹) by
        rw [Polynomial.map_mul, D.A1_map_Psi hB hB₁ hB₂ hp hs, D.A2_map_Psi hB hB₁ hB₂ hp hs, pA])
    simp only [coeff_map, RingHom.coe_coe] at h
    rw [AT_coeff] at h
    exact h
  · have h := congrArg (fun P => P.coeff i)
      (show (W1 B₁ B₂ q s₁ r₂ s₂ A * W2 B₁ B₂ q s₁ r₂ s₂ A).map
          (D.Psi hB hB₁ hB₂ hp hs : 𝕋 →+* 𝔹) = (WT p s).map (D.πb p s q s₁ : 𝕊 →+* 𝔹) by
        rw [Polynomial.map_mul, D.W1_map_Psi hB hB₁ hB₂ hp hs, D.W2_map_Psi hB hB₁ hB₂ hp hs, pW])
    simp only [coeff_map, RingHom.coe_coe] at h
    rw [WT_coeff] at h
    exact h

/-- `Φ̄ : T ⧸ (1 - e) → TQ`. -/
def Phib : 𝔹 →ₐ[A] 𝕋 :=
  Ideal.Quotient.liftₐ (D.Ib p s q s₁) (D.Phi hB hB₁ hB₂ hp hs) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, map_sub, map_one, map_mul, D.Phi_cA, D.Phi_cW, mul_one, sub_self, mul_zero])

theorem Phib_comp : (D.Phib hB hB₁ hB₂ hp hs).comp (D.πb p s q s₁) = D.Phi hB hB₁ hB₂ hp hs :=
  Ideal.Quotient.liftₐ_comp _ _ _

theorem Phib_comp_ringHom :
    ((D.Phib hB hB₁ hB₂ hp hs : 𝔹 →+* 𝕋).comp (D.πb p s q s₁ : 𝕊 →+* 𝔹)) =
      (D.Phi hB hB₁ hB₂ hp hs : 𝕊 →+* 𝕋) :=
  RingHom.ext fun x => AlgHom.congr_fun (D.Phib_comp hB hB₁ hB₂ hp hs) x

theorem ATb_map_Phib :
    ((AT p s).map (D.πb p s q s₁ : 𝕊 →+* 𝔹)).map (D.Phib hB hB₁ hB₂ hp hs : 𝔹 →+* 𝕋) =
      A1 B₁ B₂ q s₁ r₂ s₂ A * A2 B₁ B₂ q s₁ r₂ s₂ A := by
  rw [Polynomial.map_map, D.Phib_comp_ringHom, D.AT_map_Phi]

theorem WTb_map_Phib :
    ((WT p s).map (D.πb p s q s₁ : 𝕊 →+* 𝔹)).map (D.Phib hB hB₁ hB₂ hp hs : 𝔹 →+* 𝕋) =
      W1 B₁ B₂ q s₁ r₂ s₂ A * W2 B₁ B₂ q s₁ r₂ s₂ A := by
  rw [Polynomial.map_map, D.Phib_comp_ringHom, D.WT_map_Phi]

theorem A1b_map_Phib :
    (D.A1b p s q s₁).map (D.Phib hB hB₁ hB₂ hp hs : 𝔹 →+* 𝕋) = A1 B₁ B₂ q s₁ r₂ s₂ A := by
  rw [A1b, Gpoly_map _ ((AT_monic p s).map _), D.ATb_map_Phib, E_map]
  exact (D.TQ_A_split hB₁ hB₂ hp).2.1

theorem A2b_map_Phib :
    (D.A2b p s q s₁).map (D.Phib hB hB₁ hB₂ hp hs : 𝔹 →+* 𝕋) = A2 B₁ B₂ q s₁ r₂ s₂ A := by
  rw [A2b, Gpoly_map _ ((AT_monic p s).map _), D.ATb_map_Phib, Polynomial.map_sub,
    Polynomial.map_one, E_map]
  exact (D.TQ_A_split hB₁ hB₂ hp).2.2

theorem W1b_map_Phib :
    (D.W1b p s q s₁).map (D.Phib hB hB₁ hB₂ hp hs : 𝔹 →+* 𝕋) = W1 B₁ B₂ q s₁ r₂ s₂ A := by
  rw [W1b, Gpoly_map _ ((WT_monic p s).map _), D.WTb_map_Phib, E_map]
  exact (D.TQ_W_split hB₁ hB₂ hs).2.1

theorem W2b_map_Phib :
    (D.W2b p s q s₁).map (D.Phib hB hB₁ hB₂ hp hs : 𝔹 →+* 𝕋) = W2 B₁ B₂ q s₁ r₂ s₂ A := by
  rw [W2b, Gpoly_map _ ((WT_monic p s).map _), D.WTb_map_Phib, Polynomial.map_sub,
    Polynomial.map_one, E_map]
  exact (D.TQ_W_split hB₁ hB₂ hs).2.2

theorem Phib_Psi : (D.Phib hB hB₁ hB₂ hp hs).comp (D.Psi hB hB₁ hB₂ hp hs) = AlgHom.id A 𝕋 := by
  apply Algebra.TensorProduct.ext
  · apply liftT_ext
    intro v
    simp only [AlgHom.comp_apply, AlgHom.id_apply, Algebra.TensorProduct.includeLeft_apply]
    rw [Psi, Algebra.TensorProduct.productMap_left_apply, liftT_X]
    rcases v with i | i
    · have h := congrArg (fun P => P.coeff i) (D.A1b_map_Phib hB hB₁ hB₂ hp hs)
      simp only [coeff_map, RingHom.coe_coe] at h
      simp only [x1, Sum.elim_inl]
      rw [h, A1_eq, coeff_monicOf]
      rfl
    · have h := congrArg (fun P => P.coeff i) (D.W1b_map_Phib hB hB₁ hB₂ hp hs)
      simp only [coeff_map, RingHom.coe_coe] at h
      simp only [x1, Sum.elim_inr]
      rw [h, W1_eq, coeff_monicOf]
      rfl
  · apply liftT_ext
    intro v
    simp only [AlgHom.comp_apply, AlgHom.id_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply]
    rw [Psi, Algebra.TensorProduct.productMap_right_apply, liftT_X]
    rcases v with i | i
    · have h := congrArg (fun P => P.coeff i) (D.A2b_map_Phib hB hB₁ hB₂ hp hs)
      simp only [coeff_map, RingHom.coe_coe] at h
      simp only [x2, Sum.elim_inl]
      rw [h, A2_eq, coeff_monicOf]
      rfl
    · have h := congrArg (fun P => P.coeff i) (D.W2b_map_Phib hB hB₁ hB₂ hp hs)
      simp only [coeff_map, RingHom.coe_coe] at h
      simp only [x2, Sum.elim_inr]
      rw [h, W2_eq, coeff_monicOf]
      rfl

theorem Psi_Phib : (D.Psi hB hB₁ hB₂ hp hs).comp (D.Phib hB hB₁ hB₂ hp hs) = AlgHom.id A 𝔹 := by
  apply Ideal.Quotient.algHom_ext A
  rw [AlgHom.comp_assoc, D.Phib_comp, D.Psi_Phi, AlgHom.id_comp]

/-- **A component of `T` is the factorized side.** -/
def quotEquiv : 𝔹 ≃ₐ[A] 𝕋 :=
  AlgEquiv.ofAlgHom (D.Phib hB hB₁ hB₂ hp hs) (D.Psi hB hB₁ hB₂ hp hs)
    (D.Phib_Psi hB hB₁ hB₂ hp hs) (D.Psi_Phib hB hB₁ hB₂ hp hs)

end Maps

end Component


/-! ## The global decomposition -/

section Global

variable {p s : ℕ}

local notation "𝕊" => A ⊗[RB B] CMod B p s

theorem eq_one_of_idem_mul {S : Type*} [CommRing S] {x y : S} (hx : x * x = x)
    (hxy : x * y = 1) : x = 1 := by
  calc x = x * (x * y) := by rw [hxy, mul_one]
    _ = (x * x) * y := by ring
    _ = 1 := by rw [hx, hxy]

/-- On a nonzero ring receiving `T` where `cA k = cW t = 1`, the degrees add up. -/
theorem degree_of_component (hB : B = p + 3 * s) {S : Type*} [CommRing S] [Algebra A S]
    [Nontrivial S] (φ : 𝕊 →ₐ[A] S) {k t : ℕ} (hA : φ (D.cA p s k) = 1)
    (hW : φ (D.cW p s t) = 1) : k + 3 * t = B₁ := by
  have hcA := cpoly_map_eq_X_pow' (AT_monic p s) (fun _ => AT_natDegree p s) (D.AT_dvd_idem hB)
    (φ : 𝕊 →+* S) hA
  have hcW := cpoly_map_eq_X_pow' (WT_monic p s) (fun _ => WT_natDegree p s) (D.WT_dvd_idem hB)
    (φ : 𝕊 →+* S) hW
  rw [ET, E_map] at hcA hcW
  exact (pair_split' (D.bezout_over _) ((AT_monic p s).map _) (ATmap_deg _)
    ((WT_monic p s).map _) (WTmap_deg _) (D.F₁_monic _) (fun _ => D.F₁_natDegree _)
    (D.F₂_monic _) (D.ATWT_map _ hB) hcA hcW).2.2 ‹_›

/-- Components whose degrees do not add up vanish. -/
theorem cA_mul_cW_eq_zero (hB : B = p + 3 * s) {k t : ℕ} (h : k + 3 * t ≠ B₁) :
    D.cA p s k * D.cW p s t = 0 := by
  have he : (D.cA p s k * D.cW p s t) * (D.cA p s k * D.cW p s t) =
      D.cA p s k * D.cW p s t := by
    calc _ = (D.cA p s k * D.cA p s k) * (D.cW p s t * D.cW p s t) := by ring
      _ = _ := by rw [D.cA_idem hB, D.cW_idem hB]
  apply idem_eq_zero_of_quot he
  intro hnt
  have h1 : Ideal.Quotient.mkₐ A (Ideal.span {1 - D.cA p s k * D.cW p s t})
      (D.cA p s k * D.cW p s t) = 1 := quot_idem_eq_one _
  rw [map_mul] at h1
  set π := Ideal.Quotient.mkₐ A (Ideal.span {1 - D.cA p s k * D.cW p s t})
  have hA := eq_one_of_idem_mul (by rw [← map_mul, D.cA_idem hB]) h1
  have h2 : π (D.cW p s t) * π (D.cA p s k) = 1 := (mul_comm _ _).trans h1
  have hW := eq_one_of_idem_mul (by rw [← map_mul, D.cW_idem hB]) h2
  exact h (D.degree_of_component hB _ hA hW)

/-- The degree condition for a component. -/
def Valid (B₁ s q : ℕ) : Prop := q ≤ B₁ ∧ 3 ∣ B₁ - q ∧ (B₁ - q) / 3 ≤ s

instance (B₁ s q : ℕ) : Decidable (Valid B₁ s q) := by unfold Valid; infer_instance

variable (p s) in
/-- The idempotent of the component of index `q`. -/
def eps (q : ℕ) : 𝕊 := if Valid B₁ s q then D.cA p s q * D.cW p s ((B₁ - q) / 3) else 0

/-- **The components exhaust `T`.** -/
theorem sum_eps (hB : B = p + 3 * s) : ∑ q ∈ Finset.range (p + 1), D.eps p s q = 1 := by
  have hA := cpoly_sum_coeff' (E := D.ET p s) (AT_monic p s) (fun _ => AT_natDegree p s)
  have hW := cpoly_sum_coeff' (E := D.ET p s) (WT_monic p s) (fun _ => WT_natDegree p s)
  have h : (∑ k ∈ Finset.range (p + 1), D.cA p s k) * (∑ t ∈ Finset.range (s + 1), D.cW p s t) =
      1 := by
    simp only [cA, cW]; rw [hA, hW, one_mul]
  rw [← h, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold eps
  split_ifs with hv
  · obtain ⟨h1, h2, h3⟩ := hv
    rw [Finset.sum_eq_single ((B₁ - k) / 3)]
    · intro t _ ht
      apply D.cA_mul_cW_eq_zero hB
      omega
    · intro hn
      exfalso
      exact hn (Finset.mem_range.mpr (by omega))
  · refine (Finset.sum_eq_zero fun t ht => D.cA_mul_cW_eq_zero hB ?_).symm
    intro h'
    apply hv
    have := Finset.mem_range.mp ht
    exact ⟨by omega, ⟨t, by omega⟩, by omega⟩

theorem eps_mul (hB : B = p + 3 * s) (q q' : ℕ) :
    D.eps p s q * D.eps p s q' = if q = q' then D.eps p s q else 0 := by
  have hAo := cpoly_coeff_mul' (E := D.ET p s) (AT_monic p s) (fun _ => AT_natDegree p s)
    (D.AT_dvd_idem hB)
  unfold eps
  split_ifs with h1 h2 h3 h3 h2 h3 <;> try simp only [mul_zero, zero_mul]
  · subst h3
    calc _ = (D.cA p s q * D.cA p s q) * (D.cW p s ((B₁ - q) / 3) * D.cW p s ((B₁ - q) / 3)) := by
          ring
      _ = _ := by rw [D.cA_idem hB, D.cW_idem hB]
  · have := hAo q q'
    rw [if_neg h3] at this
    calc _ = (D.cA p s q * D.cA p s q') * (D.cW p s ((B₁ - q) / 3) * D.cW p s ((B₁ - q') / 3)) := by
          ring
      _ = 0 := by simp only [cA] at this ⊢; rw [this, zero_mul]
  · exact absurd (h3 ▸ h1) h2

end Global

end Setup

/-! ## Splitting a ring along orthogonal idempotents -/

section CRT

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] {ι : Type*} [Fintype ι]
  [DecidableEq ι] (ε : ι → R)

/-- The map to the product of the components. -/
def toComponents : R →ₐ[A] Π i, R ⧸ Ideal.span {1 - ε i} :=
  Pi.algHom A _ fun i => Ideal.Quotient.mkₐ A (Ideal.span {1 - ε i})

theorem toComponents_bijective (hmul : ∀ i j, ε i * ε j = if i = j then ε i else 0)
    (hsum : ∑ i, ε i = 1) : Function.Bijective (toComponents (A := A) ε) := by
  have hone : ∀ i, Ideal.Quotient.mk (Ideal.span {1 - ε i}) (ε i) = 1 := fun i =>
    quot_idem_eq_one (ε i)
  have hzero : ∀ i j, j ≠ i → Ideal.Quotient.mk (Ideal.span {1 - ε i}) (ε j) = 0 := by
    intro i j hji
    calc Ideal.Quotient.mk (Ideal.span {1 - ε i}) (ε j)
        = Ideal.Quotient.mk (Ideal.span {1 - ε i}) (ε j) *
            Ideal.Quotient.mk (Ideal.span {1 - ε i}) (ε i) := by rw [hone, mul_one]
      _ = 0 := by rw [← map_mul, hmul, if_neg hji, map_zero]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hxi : ∀ i, ε i * x = 0 := by
      intro i
      have := congrFun hx i
      simp only [toComponents, Pi.algHom_apply, Ideal.Quotient.mkₐ_eq_mk, Pi.zero_apply,
        Ideal.Quotient.eq_zero_iff_mem] at this
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
      rw [← hc]
      have := hmul i i
      rw [if_pos rfl] at this
      linear_combination (-c) * this
    calc x = (∑ i, ε i) * x := by rw [hsum, one_mul]
      _ = 0 := by rw [Finset.sum_mul]; exact Finset.sum_eq_zero fun i _ => hxi i
  · intro y
    choose x hx using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨∑ j, ε j * x j, funext fun i => ?_⟩
    simp only [toComponents, Pi.algHom_apply, Ideal.Quotient.mkₐ_eq_mk, map_sum, map_mul]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [hzero i j hj, zero_mul])
      (fun h => absurd (Finset.mem_univ i) h), hone, one_mul, hx]

end CRT

end KhanSL2.Collision.CoordSplit
