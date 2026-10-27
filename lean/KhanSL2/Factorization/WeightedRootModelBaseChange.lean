module

public import KhanSL2.Factorization.WeightedRootModel

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped TensorProduct BigOperators
namespace KhanSL2.Factorization.WeightedRootModel
open WeightedRoots

/-- Multiplicity one on odd roots and two on even roots. -/
def rootWeight (q r : ℕ) : Fin q ⊕ Fin r → ℕ := Sum.elim (fun _ => 1) (fun _ => 2)

theorem rootWeight_pos (q r : ℕ) (i : Fin q ⊕ Fin r) : 0 < rootWeight q r i := by
  cases i <;> simp [rootWeight]

variable (q r : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB (q+2*r)) A]

/-- Base change through the canonical weighted characteristic map. -/
abbrev WeightedBase := A ⊗[Depth.RB (q+2*r)] LabelledWeightedRing q r

def weightedBaseRight : LabelledWeightedRing q r →ₐ[Depth.RB (q+2*r)] WeightedBase q r A :=
  Algebra.TensorProduct.includeRight

def baseRoot (i : Fin q ⊕ Fin r) : WeightedBase q r A :=
  weightedBaseRight q r A (show LabelledWeightedRing q r from MvPolynomial.X i)

/-- The actual universal polynomial splits into the prescribed weighted linear factors. -/
theorem univPoly_map_baseRoot :
    (Collision.univPoly (q+2*r)).map (algebraMap (Depth.RB (q+2*r)) (WeightedBase q r A)) =
      rootProduct (baseRoot q r A) (rootWeight q r) Finset.univ := by
  have h := congrArg (Polynomial.map (weightedBaseRight q r A).toRingHom)
    (univPoly_map_weightedRootMap q r)
  have hc : (weightedBaseRight q r A).toRingHom.comp (weightedRootMap q r).toRingHom =
      algebraMap (Depth.RB (q+2*r)) (WeightedBase q r A) := by
    apply RingHom.ext
    intro a
    exact (weightedBaseRight q r A).commutes a
  rw [Polynomial.map_map,hc] at h
  apply h.trans
  simp only [weightedCharacteristic,Polynomial.map_mul,Polynomial.map_prod,
    Polynomial.map_pow,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
    rootProduct,Fintype.prod_sum_type,rootWeight,Sum.elim_inl,Sum.elim_inr,pow_one]
  rfl

theorem baseRoot_factor {b₁ b₂ : ℕ} (c : Collision.ChartData (q+2*r) b₁ b₂ A) :
    rootProduct (baseRoot q r A) (rootWeight q r) Finset.univ =
      c.f₁.map (algebraMap A (WeightedBase q r A)) *
        c.f₂.map (algebraMap A (WeightedBase q r A)) := by
  have h := congrArg (Polynomial.map (algebraMap A (WeightedBase q r A))) c.factor
  rw [Polynomial.map_map,← IsScalarTower.algebraMap_eq (Depth.RB (q+2*r)) A (WeightedBase q r A),
    univPoly_map_baseRoot] at h
  simpa only [Polynomial.map_mul] using h

/-- The actual quotient ring cut out by both weighted factor identities. -/
abbrev AssignmentRing {b₁ b₂ : ℕ} (c : Collision.ChartData (q+2*r) b₁ b₂ A)
    (σ : Admissible (rootWeight q r) b₁) :=
  FactorRing (c.f₁.map (algebraMap A (WeightedBase q r A)))
    (c.f₂.map (algebraMap A (WeightedBase q r A))) (baseRoot q r A) (rootWeight q r) (selected σ.val)

def assignmentMap {b₁ b₂ : ℕ} (c : Collision.ChartData (q+2*r) b₁ b₂ A) :
    WeightedBase q r A →ₐ[A] ∀ σ : Admissible (rootWeight q r) b₁, AssignmentRing q r A c σ :=
  AlgHom.pi fun _σ => Ideal.Quotient.mkₐ A _

/-- The splitting uses the original factor degree even if this weighted component
vanishes on the chart. The zero algebra case is included explicitly. -/
theorem assignmentMap_bijective {b₁ b₂ : ℕ} (c : Collision.ChartData (q+2*r) b₁ b₂ A) :
    Function.Bijective (assignmentMap q r A c) := by
  classical
  rcases subsingleton_or_nontrivial (WeightedBase q r A) with ht | ht
  · let := ht
    constructor
    · intro x y _
      exact Subsingleton.elim x y
    · intro y
      exact ⟨0,Subsingleton.elim _ _⟩
  · let := ht
    have hd : (c.f₁.map (algebraMap A (WeightedBase q r A))).natDegree = b₁ :=
      (c.monic₁.natDegree_map _).trans c.degree₁
    let e := weightedSplittingAlgEquivOfCoprime (R:=A)
      (c.monic₁.map (algebraMap A (WeightedBase q r A)))
      (c.monic₂.map (algebraMap A (WeightedBase q r A)))
      (c.coprime.map (Polynomial.mapRingHom (algebraMap A (WeightedBase q r A))))
      (baseRoot q r A) (rootWeight q r) (rootWeight_pos q r) (baseRoot_factor q r A c)
    have he := e.bijective
    change Function.Bijective (fun (x : WeightedBase q r A)
      (σ : Admissible (rootWeight q r) (c.f₁.map (algebraMap A (WeightedBase q r A))).natDegree) =>
        Ideal.Quotient.mk (factorIdeal (c.f₁.map (algebraMap A (WeightedBase q r A)))
          (c.f₂.map (algebraMap A (WeightedBase q r A))) (baseRoot q r A) (rootWeight q r)
          (selected σ.val)) x) at he
    change Function.Bijective (fun (x : WeightedBase q r A)
      (σ : Admissible (rootWeight q r) b₁) =>
        Ideal.Quotient.mk (factorIdeal (c.f₁.map (algebraMap A (WeightedBase q r A)))
          (c.f₂.map (algebraMap A (WeightedBase q r A))) (baseRoot q r A) (rootWeight q r)
          (selected σ.val)) x)
    let K := fun σ : (Fin q ⊕ Fin r) → Bool =>
      factorIdeal (c.f₁.map (algebraMap A (WeightedBase q r A)))
        (c.f₂.map (algebraMap A (WeightedBase q r A))) (baseRoot q r A) (rootWeight q r) (selected σ)
    have hreindex (d e : ℕ) (h : d = e) :
        Function.Bijective (fun (x : WeightedBase q r A) (σ : Admissible (rootWeight q r) d) =>
          Ideal.Quotient.mk (K σ.val) x) ↔
        Function.Bijective (fun (x : WeightedBase q r A) (σ : Admissible (rootWeight q r) e) =>
          Ideal.Quotient.mk (K σ.val) x) := by
      subst e
      rfl
    exact (hreindex _ _ hd).mp he

/-- Exact coefficient-algebra splitting into all admissible weighted assignments. -/
def assignmentSplitting {b₁ b₂ : ℕ} (c : Collision.ChartData (q+2*r) b₁ b₂ A) :
    WeightedBase q r A ≃ₐ[A] ∀ σ : Admissible (rootWeight q r) b₁, AssignmentRing q r A c σ :=
  AlgEquiv.ofBijective (assignmentMap q r A c) (assignmentMap_bijective q r A c)

@[simp] theorem assignmentSplitting_apply {b₁ b₂ : ℕ} (c : Collision.ChartData (q+2*r) b₁ b₂ A)
    (x : WeightedBase q r A) (σ : Admissible (rootWeight q r) b₁) :
    assignmentSplitting q r A c x σ = Ideal.Quotient.mk _ x := rfl

end KhanSL2.Factorization.WeightedRootModel



