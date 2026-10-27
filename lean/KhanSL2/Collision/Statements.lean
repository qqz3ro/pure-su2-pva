module

public import KhanSL2.Conditional.Coefficients
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Algebra.DirectSum.Module

@[expose] public section

/-!
# Factorization statements on étale charts

`R_B = ℂ[e₁, …, e_B]` carries the universal monic polynomial
`F_B(u) = ∏ (u - t_i) = Σ_k (-1)^{B-k} e_{B-k} u^k`. A *chart* is an étale `R_B`-algebra
`A` with a factorization `F_B = f₁ f₂` into coprime monic polynomials of positive degrees
`B₁ + B₂ = B`. The coefficients of `f₁` and `f₂` make `A` an algebra over `R_{B₁}` and
`R_{B₂}`.

* `KFactor B` is the factorization of the coefficient homology `K` on every chart
  (depth paper, Prop. 6.3, eq. `Kfactor`; notes, Thm. 7.4).
* `JFactor B` is the same for the polynomial target `J` (eq. `Jfactor`).
* `ChartComparison B` is their consequence once all smaller comparisons are known:
  `A ⊗ K_{B,p} ≅ A ⊗ J_{B,p}` on every chart.

The collision-support step is proved from `ChartComparison`; the latter is proved from
`KFactor` and `JFactor`.
-/

noncomputable section

open Polynomial TensorProduct
open scoped DirectSum

namespace KhanSL2.Collision

open Conditional
open scoped KhanSL2.Conditional

/-- The universal monic polynomial `∏ (u - t_i)` in elementary symmetric coordinates:
the coefficient of `u^k`, `k < B`, is `(-1)^(B-k) e_{B-k}`, and `e_j = X (j - 1)`. -/
def univPoly (B : ℕ) : (Depth.RB B)[X] :=
  Depth.monicOf B (fun k => ((-1 : ℂ) ^ (B - (k : ℕ))) •
    MvPolynomial.X (⟨B - 1 - (k : ℕ), by omega⟩ : Fin B))

/-- The elementary symmetric coordinates of a polynomial `f` of degree `n`:
`e_{j+1}(f) = (-1)^(j+1) coeff_{n-1-j} f`. -/
def elemCoord {A : Type*} [CommRing A] (n : ℕ) (f : A[X]) (j : Fin n) : A :=
  (-1 : A) ^ ((j : ℕ) + 1) * f.coeff (n - 1 - (j : ℕ))

/-- The coefficient map `R_n → A` attached to a degree-`n` polynomial over a `ℂ`-algebra. -/
def coeffHom {A : Type*} [CommRing A] [Algebra ℂ A] (n : ℕ) (f : A[X]) :
    Depth.RB n →ₐ[ℂ] A :=
  MvPolynomial.aeval (elemCoord n f)

/-- Chart data: a coprime monic factorization of the universal polynomial of degree `B`
over an `R_B`-algebra, with factors of degrees `B₁` and `B₂`. -/
structure ChartData (B B₁ B₂ : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB B) A] where
  f₁ : A[X]
  f₂ : A[X]
  monic₁ : f₁.Monic
  monic₂ : f₂.Monic
  degree₁ : f₁.natDegree = B₁
  degree₂ : f₂.natDegree = B₂
  factor : (univPoly B).map (algebraMap (Depth.RB B) A) = f₁ * f₂
  coprime : IsCoprime f₁ f₂

section ChartAlgebras

variable {B B₁ B₂ : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB B) A]

/-- `A` is a `ℂ`-algebra through `R_B`. -/
abbrev chartComplexAlgebra : Algebra ℂ A :=
  (algebraMap (Depth.RB B) A).comp (algebraMap ℂ (Depth.RB B)) |>.toAlgebra

/-- The `R_{B₁}`-algebra structure on a chart. -/
abbrev ChartData.algebra₁ (c : ChartData B B₁ B₂ A) : Algebra (Depth.RB B₁) A :=
  letI := chartComplexAlgebra (B := B) (A := A)
  (coeffHom B₁ c.f₁).toRingHom.toAlgebra

/-- The `R_{B₂}`-algebra structure on a chart. -/
abbrev ChartData.algebra₂ (c : ChartData B B₁ B₂ A) : Algebra (Depth.RB B₂) A :=
  letI := chartComplexAlgebra (B := B) (A := A)
  (coeffHom B₂ c.f₂).toRingHom.toAlgebra

end ChartAlgebras

/-- The factorized side of a chart: `⊕_{q ≤ p} (A ⊗_{R_{B₁}} M₁ q) ⊗_A (A ⊗_{R_{B₂}} M₂ (p - q))`. -/
abbrev FactorSide {B B₁ B₂ : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB B) A]
    (c : ChartData B B₁ B₂ A) (M₁ : ℕ → Type) [∀ q, AddCommGroup (M₁ q)]
    [∀ q, Module (Depth.RB B₁) (M₁ q)] (M₂ : ℕ → Type) [∀ q, AddCommGroup (M₂ q)]
    [∀ q, Module (Depth.RB B₂) (M₂ q)] (p : ℕ) : Type :=
  letI := c.algebra₁
  letI := c.algebra₂
  ⨁ q : Fin (p + 1), (A ⊗[Depth.RB B₁] M₁ q) ⊗[A] (A ⊗[Depth.RB B₂] M₂ (p - q))

/-- **Factorization of `K` on charts** (depth paper, eq. `Kfactor`). -/
def KFactor (B : ℕ) : Prop :=
  ∀ (B₁ B₂ : ℕ), 0 < B₁ → 0 < B₂ → B₁ + B₂ = B →
    ∀ (A : Type) [CommRing A] [Algebra (Depth.RB B) A] [Algebra.Etale (Depth.RB B) A]
      (c : ChartData B B₁ B₂ A) (p : ℕ),
      letI := c.algebra₁
      letI := c.algebra₂
      Nonempty ((A ⊗[Depth.RB B] K B p) ≃ₗ[A] FactorSide c (K B₁) (K B₂) p)

/-- **Factorization of `J` on charts** (depth paper, eq. `Jfactor`). -/
def JFactor (B : ℕ) : Prop :=
  ∀ (B₁ B₂ : ℕ), 0 < B₁ → 0 < B₂ → B₁ + B₂ = B →
    ∀ (A : Type) [CommRing A] [Algebra (Depth.RB B) A] [Algebra.Etale (Depth.RB B) A]
      (c : ChartData B B₁ B₂ A) (p : ℕ),
      letI := c.algebra₁
      letI := c.algebra₂
      Nonempty ((A ⊗[Depth.RB B] J B p) ≃ₗ[A] FactorSide c (J B₁) (J B₂) p)

/-- On every chart, `K` and `J` agree once all smaller comparisons are isomorphisms. -/
def ChartComparison (B : ℕ) : Prop :=
  EarlierComparisons B →
  ∀ (B₁ B₂ : ℕ), 0 < B₁ → 0 < B₂ → B₁ + B₂ = B →
    ∀ (A : Type) [CommRing A] [Algebra (Depth.RB B) A] [Algebra.Etale (Depth.RB B) A]
      (_ : ChartData B B₁ B₂ A) (p : ℕ),
      Nonempty ((A ⊗[Depth.RB B] K B p) ≃ₗ[A] (A ⊗[Depth.RB B] J B p))

end KhanSL2.Collision
