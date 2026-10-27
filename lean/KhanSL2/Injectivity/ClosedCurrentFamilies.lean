module

public import KhanSL2.Injectivity.CurrentAdjoint
public import KhanSL2.Injectivity.CartanFunctional

/-! Genuine closed Cartan chain families, and insertion of finite Newton cycles. -/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace KhanSL2.Injectivity.Cartan

variable (P : Type*) [CommRing P] [Algebra ℂ P]

/-- A polynomial family of genuine cycles, equivariant for every positive
Cartan current (with index zero included for convenient polynomial formulas). -/
structure ClosedCurrentFamily (f : ℕ → P) where
  toLinearMap : P →ₗ[ℂ] Cochain
  closed : ∀ p u, FiniteExterior.coefficientPairing (toLinearMap p) (q u) = 0
  current : ∀ k p, rootCurrentAction k (toLinearMap p) = toLinearMap (f k * p)

variable {P} {f : ℕ → P}

namespace ClosedCurrentFamily

def insertLinear (C : ClosedCurrentFamily P f) (θ : ℕ →₀ P) : P →ₗ[ℂ] Cochain where
  toFun p := ∑ j ∈ θ.support,
    generator (.cartan (j - 1)) * C.toLinearMap (θ j * p)
  map_add' p r := by
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' r p := by
    simp [mul_smul_comm, ← Finset.smul_sum]

@[simp] theorem insertLinear_apply (C : ClosedCurrentFamily P f) (θ : ℕ →₀ P) (p : P) :
    C.insertLinear θ p = ∑ j ∈ θ.support,
      generator (.cartan (j - 1)) * C.toLinearMap (θ j * p) := rfl

theorem insertLinear_closed (C : ClosedCurrentFamily P f) (θ : ℕ →₀ P)
    (hzero : θ 0 = 0) (hcycle : ∑ j ∈ θ.support, f j * θ j = 0) (p : P) (u : Cochain) :
    FiniteExterior.coefficientPairing (C.insertLinear θ p) (q u) = 0 := by
  have hterm (j : ℕ) (hj : j ∈ θ.support) :
      FiniteExterior.coefficientPairing
        (generator (.cartan (j - 1)) * C.toLinearMap (θ j * p)) (q u) =
      -FiniteExterior.coefficientPairing (C.toLinearMap (f j * (θ j * p))) u := by
    have hj0 : j ≠ 0 := by
      intro he
      subst j
      exact (Finsupp.mem_support_iff.mp hj) hzero
    have hj1 : j - 1 + 1 = j := by omega
    have h := pairing_cartan_q (j - 1) (C.toLinearMap (θ j * p)) u
    rw [C.closed, add_zero, hj1, C.current] at h
    exact h
  rw [insertLinear_apply]
  simp only [map_sum, LinearMap.sum_apply]
  calc
    _ = ∑ j ∈ θ.support,
        -FiniteExterior.coefficientPairing (C.toLinearMap (f j * (θ j * p))) u :=
      Finset.sum_congr rfl hterm
    _ = -FiniteExterior.coefficientPairing
        (C.toLinearMap (∑ j ∈ θ.support, f j * (θ j * p))) u := by
      simp only [map_sum, LinearMap.sum_apply, Finset.sum_neg_distrib]
    _ = 0 := by
      have hsum : (∑ j ∈ θ.support, f j * (θ j * p)) = 0 := by
        calc
          _ = (∑ j ∈ θ.support, f j * θ j) * p := by
            rw [Finset.sum_mul]
            simp only [mul_assoc]
          _ = 0 := by rw [hcycle, zero_mul]
      rw [hsum, map_zero, map_zero, LinearMap.zero_apply, neg_zero]

theorem insertLinear_current (C : ClosedCurrentFamily P f) (θ : ℕ →₀ P)
    (k : ℕ) (p : P) :
    rootCurrentAction k (C.insertLinear θ p) = C.insertLinear θ (f k * p) := by
  simp only [insertLinear_apply, map_sum, rootCurrentAction_mul,
    rootCurrentAction_generator, rootCurrentGenerator, zero_mul, zero_add, C.current]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [mul_left_comm (f k) (θ j) p]

/-- Insert a finite polynomial Koszul cycle into a genuine Cartan chain family.
No exactness or comparison theorem is assumed. -/
def insert (C : ClosedCurrentFamily P f) (θ : ℕ →₀ P)
    (hzero : θ 0 = 0) (hcycle : ∑ j ∈ θ.support, f j * θ j = 0) :
    ClosedCurrentFamily P f where
  toLinearMap := C.insertLinear θ
  closed := C.insertLinear_closed θ hzero hcycle
  current := C.insertLinear_current θ

/-- Neutral epsilon modes can be inserted into every closed current family. -/
def prependNeutral (C : ClosedCurrentFamily P f) (i : ℕ) : ClosedCurrentFamily P f where
  toLinearMap := (FiniteExterior.wedgeLinear Mode.code (generator (.neutral i))).comp C.toLinearMap
  closed p u := by
    change FiniteExterior.coefficientPairing (generator (.neutral i) * C.toLinearMap p) (q u) = 0
    have h := pairing_neutral_q i (C.toLinearMap p) u
    rw [C.closed, add_zero] at h
    exact h
  current k p := by
    change rootCurrentAction k (generator (.neutral i) * C.toLinearMap p) =
      generator (.neutral i) * C.toLinearMap (f k * p)
    rw [rootCurrentAction_mul, rootCurrentAction_generator, rootCurrentGenerator,
      zero_mul, zero_add, C.current]

@[simp] theorem prependNeutral_apply (C : ClosedCurrentFamily P f) (i : ℕ) (p : P) :
    (C.prependNeutral i).toLinearMap p = generator (.neutral i) * C.toLinearMap p := rfl

def functional (C : ClosedCurrentFamily P f) (p : P) : KhanSL2.Cohomology →ₗ[ℂ] ℂ :=
  descendCartanFunctional (FiniteExterior.coefficientPairing (C.toLinearMap p)) (C.closed p)

@[simp] theorem functional_classOf (C : ClosedCurrentFamily P f) (p : P)
    (u : KhanSL2.Cochain) (hu : u ∈ relativeCycles) :
    C.functional p (classOf u hu) =
      FiniteExterior.coefficientPairing (C.toLinearMap p) (restriction u) := rfl

end ClosedCurrentFamily
end KhanSL2.Injectivity.Cartan
