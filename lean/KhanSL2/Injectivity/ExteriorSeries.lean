module

public import KhanSL2.Injectivity.ExteriorPolynomialEvaluation
public import KhanSL2.Injectivity.ExteriorWords
public import KhanSL2.Injectivity.FinitePairing
public import KhanSL2.Injectivity.ExteriorDeterminant
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-! Coefficientwise finite exterior operations on formal series. Formal series
are used only as an algebraic device for finite coefficient identities. -/

@[expose] public section

noncomputable section
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

namespace KhanSL2.FiniteExterior.Series

open KhanSL2.Injectivity

variable {σ α : Type*} [DecidableEq α] [GeneratorOrder α]

def mapCoefficients {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    [Module ℂ A] [Module ℂ B] (f : A →ₗ[ℂ] B) :
    MvPowerSeries σ A →ₗ[ℂ] MvPowerSeries σ B where
  toFun F d := f (F d)
  map_add' F G := by funext d; exact map_add f _ _
  map_smul' c F := by funext d; exact map_smul f c _

@[simp] theorem mapCoefficients_apply {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    [Module ℂ A] [Module ℂ B] (f : A →ₗ[ℂ] B) (F : MvPowerSeries σ A) (d) :
    mapCoefficients f F d = f (F d) := rfl

abbrev Cochain (σ α : Type*) := MvPowerSeries σ (Exterior α)
abbrev Scalar (σ : Type*) := MvPowerSeries σ ℂ

def pairing (c : Exterior α) : Cochain σ α →ₗ[ℂ] Scalar σ :=
  mapCoefficients (coefficientPairing c)

def contract (a : α) : Cochain σ α →ₗ[ℂ] Cochain σ α :=
  mapCoefficients (contraction GeneratorOrder.code a)

def parity : Cochain σ α →ₗ[ℂ] Cochain σ α := mapCoefficients parityLinear

def scalar : Scalar σ →+* Cochain σ α :=
  MvPowerSeries.map (σ := σ) (algebraMap ℂ (Exterior α))

@[simp] theorem coeff_pairing (c : Exterior α) (F : Cochain σ α) (d) :
    MvPowerSeries.coeff (R := ℂ) d (pairing c F) =
      coefficientPairing c (MvPowerSeries.coeff (R := Exterior α) d F) := rfl

@[simp] theorem coeff_contract (a : α) (F : Cochain σ α) (d) :
    MvPowerSeries.coeff (R := Exterior α) d (contract a F) =
      contraction GeneratorOrder.code a (MvPowerSeries.coeff (R := Exterior α) d F) := rfl

@[simp] theorem coeff_parity (F : Cochain σ α) (d) :
    MvPowerSeries.coeff (R := Exterior α) d (parity F) =
      parityLinear (MvPowerSeries.coeff (R := Exterior α) d F) := rfl

theorem pairing_generator_mul (a : α) (c : Exterior α) (F : Cochain σ α) :
    pairing (generator a * c) F = pairing c (contract a F) := by
  apply MvPowerSeries.ext
  intro d
  exact coefficientPairing_generator_mul a c (F d)

theorem contract_mul (a : α) (F G : Cochain σ α) :
    contract a (F * G) = contract a F * G + parity F * contract a G := by
  classical
  apply MvPowerSeries.ext
  intro d
  simp only [coeff_contract, MvPowerSeries.coeff_mul, map_sum,
    map_add, coeff_parity]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij _
  exact contraction_wedge GeneratorOrder.code GeneratorOrder.code_injective a _ _

theorem pairing_scalar_mul (c : Exterior α) (p : Scalar σ) (F : Cochain σ α) :
    pairing c (scalar p * F) = p * pairing c F := by
  classical
  apply MvPowerSeries.ext
  intro d
  simp only [coeff_pairing, MvPowerSeries.coeff_mul, map_sum,
    scalar, MvPowerSeries.coeff_map, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul, map_smul, smul_eq_mul]

theorem scalar_commute (p : Scalar σ) (F : Cochain σ α) :
    scalar p * F = F * scalar p := by
  classical
  apply MvPowerSeries.ext
  intro d
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  rw [Finsupp.sum_antidiagonal_swap d (fun e f =>
    MvPowerSeries.coeff (R := Exterior α) e (scalar p) * MvPowerSeries.coeff (R := Exterior α) f F)]
  apply Finset.sum_congr rfl
  intro ij _
  change algebraMap ℂ (Exterior α) (p ij.2) * F ij.1 =
    F ij.1 * algebraMap ℂ (Exterior α) (p ij.2)
  exact Algebra.commutes (p ij.2) (F ij.1)

@[simp] theorem contract_one (a : α) : contract a (1 : Cochain σ α) = 0 := by
  classical
  apply MvPowerSeries.ext
  intro d
  simp only [coeff_contract, MvPowerSeries.coeff_one, apply_ite,
    map_zero, MvPowerSeries.coeff_zero]
  split_ifs <;> simp [one_def]

@[simp] theorem pairing_one_one : pairing (1 : Exterior α) (1 : Cochain σ α) = 1 := by
  classical
  apply MvPowerSeries.ext
  intro d
  simp only [coeff_pairing, MvPowerSeries.coeff_one, apply_ite, map_zero]
  split_ifs <;> simp [one_def, monomial]

/-- A degree-one exterior series, with its contraction and augmentation laws.
All concrete series below discharge these laws coefficient by coefficient. -/
structure LinearSeries (σ α : Type*) [DecidableEq α] [GeneratorOrder α] where
  val : Cochain σ α
  odd : parity val = -val
  contract_eq : ∀ a, contract a val = scalar (pairing (generator a) val)
  pairing_one_mul : ∀ F, pairing 1 (val * F) = 0

theorem contract_linear_mul (a : α) (F : LinearSeries σ α) (G : Cochain σ α) :
    contract a (F.val * G) = scalar (pairing (generator a) F.val) * G -
      F.val * contract a G := by
  rw [contract_mul, F.contract_eq, F.odd, neg_mul, sub_eq_add_neg]

theorem orderedProduct_remove_succ {n : ℕ} (F : Fin (n + 2) → Cochain σ α)
    (j : Fin (n + 1)) :
    orderedProduct (j.succ.removeNth F) = F 0 * orderedProduct (j.removeNth (Fin.tail F)) := by
  rw [orderedProduct_succ]
  have hzero : (j.succ.removeNth F) 0 = F 0 := rfl
  have htail : Fin.tail (j.succ.removeNth F) = j.removeNth (Fin.tail F) := by
    funext i
    simp [Fin.tail_def, Fin.removeNth, Fin.succ_succAbove_succ]
  rw [hzero, htail]

theorem contract_orderedProduct (a : α) {n : ℕ} (F : Fin (n + 1) → LinearSeries σ α) :
    contract a (orderedProduct fun j => (F j).val) =
      ∑ j : Fin (n + 1), (-1 : ℂ) ^ (j : ℕ) •
        (scalar (pairing (generator a) (F j).val) *
          orderedProduct (fun i => (F (j.succAbove i)).val)) := by
  induction n with
  | zero =>
    rw [orderedProduct_succ, contract_linear_mul]
    simp [Fin.removeNth, Fin.tail_def]
  | succ n ih =>
    rw [orderedProduct_succ, contract_linear_mul]
    simp only [Fin.tail_def]
    rw [ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.zero_succAbove,
      Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [show orderedProduct (fun i => (F (j.succ.succAbove i)).val) =
        (F 0).val * orderedProduct (fun i => (F ((j.succAbove i).succ)).val) by
      exact orderedProduct_remove_succ (fun i => (F i).val) j]
    simp only [pow_succ, Fin.val_succ, mul_neg_one, neg_smul, mul_smul_comm,
      Fin.tail_def]
    rw [← mul_assoc, ← scalar_commute, mul_assoc]

theorem pairing_generatorWord_linearSeries {n : ℕ} (a : Fin n → α)
    (F : Fin n → LinearSeries σ α) :
    pairing (generatorWord a) (orderedProduct fun j => (F j).val) =
      Matrix.det (fun i j => pairing (generator (a i)) (F j).val) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [generatorWord_succ, pairing_generator_mul, contract_orderedProduct,
      map_sum, Matrix.det_succ_row_zero]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, pairing_scalar_mul, ih]
    simp only [Algebra.smul_def, map_pow, map_neg, map_one, mul_assoc,
      Matrix.submatrix, Fin.tail_def]
    rfl

theorem pairing_generatorWord_linearSeries_other {n m : ℕ} (a : Fin n → α)
    (F : Fin m → LinearSeries σ α) (hne : n ≠ m) :
    pairing (generatorWord a) (orderedProduct fun j => (F j).val) = 0 := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => exact (hne rfl).elim
    | succ m =>
      rw [generatorWord_zero, orderedProduct_succ]
      exact (F 0).pairing_one_mul _
  | succ n ih =>
    cases m with
    | zero => simp [generatorWord_succ, pairing_generator_mul]
    | succ m =>
      rw [generatorWord_succ, pairing_generator_mul, contract_orderedProduct, map_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [map_smul, pairing_scalar_mul, ih _ _ (by omega), mul_zero, smul_zero]

def pairingRight (F : Cochain σ α) : Exterior α →ₗ[ℂ] Scalar σ where
  toFun c := pairing c F
  map_add' c d := by ext e; exact LinearMap.congr_fun (map_add coefficientPairing c d) _
  map_smul' z c := by ext e; exact LinearMap.congr_fun (map_smul coefficientPairing z c) _

theorem pairing_orderedProduct_eq_determinantEvaluation {n : ℕ}
    (F : Fin n → LinearSeries σ α) (c : Exterior α) :
    pairing c (orderedProduct fun j => (F j).val) =
      determinantEvaluation n (fun a j => pairing (generator a) (F j).val) c := by
  have h : pairingRight (orderedProduct fun j => (F j).val) =
      determinantEvaluation n (fun a j => pairing (generator a) (F j).val) := by
    apply linearMap_ext_orderedProducts
    intro m a
    by_cases hm : m = n
    · subst m
      exact (pairing_generatorWord_linearSeries a F).trans
        (determinantEvaluation_orderedProduct n
          (fun b j => pairing (generator b) (F j).val) a).symm
    · exact (pairing_generatorWord_linearSeries_other a F hm).trans
        (determinantEvaluation_orderedProduct_other n m
          (fun b j => pairing (generator b) (F j).val) a hm).symm
  exact LinearMap.congr_fun h c

theorem contraction_generator (a b : α) :
    contraction GeneratorOrder.code a (generator b) =
      coefficientPairing (generator a) (generator b) • (1 : Exterior α) := by
  change contraction GeneratorOrder.code a (monomial {b}) = _
  rw [contraction_monomial]
  by_cases h : a = b
  · subst b
    simp [generator, contraction_monomial, position, one_def, monomial, Finset.filter_singleton]
  · simp [generator, contraction_monomial, h, Ne.symm h, monomial,
      Finsupp.single_apply]

def linearSeriesOfCoefficients (F : Cochain σ α)
    (hF : ∀ d, ∃ (a : α) (z : ℂ), F d = z • generator a) : LinearSeries σ α where
  val := F
  odd := by
    apply MvPowerSeries.ext
    intro d
    obtain ⟨a,z,h⟩ := hF d
    change parityLinear (F d) = -F d
    rw [h, map_smul, parity_generator, smul_neg]
  contract_eq := by
    intro a
    apply MvPowerSeries.ext
    intro d
    obtain ⟨b,z,h⟩ := hF d
    change contraction GeneratorOrder.code a (F d) =
      algebraMap ℂ (Exterior α) (coefficientPairing (generator a) (F d))
    rw [h, map_smul, contraction_generator, map_smul, smul_eq_mul,
      Algebra.algebraMap_eq_smul_one, smul_smul]
  pairing_one_mul := by
    intro G
    classical
    apply MvPowerSeries.ext
    intro d
    rw [coeff_pairing, MvPowerSeries.coeff_mul, map_sum]
    apply Finset.sum_eq_zero
    intro ij _
    obtain ⟨a,z,h⟩ := hF ij.1
    change coefficientPairing 1 (F ij.1 * G ij.2) = 0
    rw [h, smul_mul_assoc, map_smul, coefficientPairing_one_generator_mul, smul_zero]

end KhanSL2.FiniteExterior.Series

namespace KhanSL2.FiniteExterior

open KhanSL2.Injectivity

variable {α P Q : Type*} [DecidableEq α] [GeneratorOrder α]
variable [CommRing P] [Algebra ℂ P] [CommRing Q] [Algebra ℂ Q]

theorem determinantEvaluation_map (n : ℕ) (w : α → Fin n → P)
    (f : P →ₐ[ℂ] Q) (c : Exterior α) :
    f (determinantEvaluation n w c) = determinantEvaluation n (fun a j => f (w a j)) c := by
  have h : f.toLinearMap.comp (determinantEvaluation n w) =
      determinantEvaluation n (fun a j => f (w a j)) := by
    apply linearMap_ext_orderedProducts
    intro m a
    change f (determinantEvaluation n w _) = _
    by_cases hm : m = n
    · subst m
      rw [determinantEvaluation_orderedProduct, determinantEvaluation_orderedProduct,
        AlgHom.map_det]
      rfl
    · rw [determinantEvaluation_orderedProduct_other n m w a hm, map_zero,
        determinantEvaluation_orderedProduct_other n m _ a hm]
  exact LinearMap.congr_fun h c

end KhanSL2.FiniteExterior
