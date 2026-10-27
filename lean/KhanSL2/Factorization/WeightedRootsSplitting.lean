module

public import KhanSL2.Factorization.WeightedRootsFactors

@[expose] public section

/-! Removing the zero components gives exactly the admissible weighted-root
splitting of Appendix 6.2. -/

noncomputable section
open scoped BigOperators
open Polynomial
namespace KhanSL2.Factorization.WeightedRoots

variable {A : Type*} [CommRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem factorRing_subsingleton_of_wrong_weight {f₁ f₂ : A[X]} (hf₁ : f₁.Monic)
    (x : ι → A) (m : ι → ℕ) (S : Finset ι)
    (hdeg : (∑ i ∈ S, m i) ≠ f₁.natDegree) :
    Subsingleton (FactorRing f₁ f₂ x m S) := by
  rcases subsingleton_or_nontrivial (FactorRing f₁ f₂ x m S) with h | h
  · exact h
  · let := h
    have hf := (factorIdeal_le_iff f₁ f₂ x m S (factorIdeal f₁ f₂ x m S)).mp le_rfl
    have hd := congrArg Polynomial.natDegree hf.1
    rw [rootProduct_natDegree,hf₁.natDegree_map] at hd
    exact False.elim (hdeg hd)

/-- The root assignments whose total first-factor weight has the required size. -/
def Admissible (m : ι → ℕ) (d : ℕ) := {σ : ι → Bool // (∑ i ∈ selected σ, m i) = d}

def restrictAssignments (f₁ f₂ : A[X]) (x : ι → A) (m : ι → ℕ) :
    (∀ σ : ι → Bool, FactorRing f₁ f₂ x m (selected σ)) →+*
      ∀ σ : Admissible m f₁.natDegree, FactorRing f₁ f₂ x m (selected σ.val) where
  toFun u σ := u σ.val
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem restrictAssignments_bijective {f₁ f₂ : A[X]} (hf₁ : f₁.Monic)
    (x : ι → A) (m : ι → ℕ) :
    Function.Bijective (restrictAssignments f₁ f₂ x m) := by
  classical
  constructor
  · intro u v h
    funext σ
    by_cases hs : (∑ i ∈ selected σ, m i) = f₁.natDegree
    · exact congrFun h (⟨σ,hs⟩ : Admissible m f₁.natDegree)
    · let := factorRing_subsingleton_of_wrong_weight (f₂ := f₂) hf₁ x m (selected σ) hs
      exact Subsingleton.elim _ _
  · intro u
    refine ⟨fun σ => if hs : (∑ i ∈ selected σ, m i) = f₁.natDegree then u ⟨σ,hs⟩ else 0, ?_⟩
    funext σ
    simp only [restrictAssignments,RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk,
      dif_pos σ.property]
    rfl

/-- The exact coprime weighted-root splitting. It is a theorem over every
commutative coefficient ring, with no reducedness or domain hypothesis. -/
def weightedSplittingEquiv {α β f₁ f₂ : A[X]}
    (hf₁ : f₁.Monic) (hf₂ : f₂.Monic) (hbez : α*f₁ + β*f₂ = 1)
    (x : ι → A) (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hprod : rootProduct x m Finset.univ = f₁*f₂) :
    A ≃+* ∀ σ : Admissible m f₁.natDegree,
      FactorRing f₁ f₂ x m (selected σ.val) :=
  (splittingEquiv hf₁ hf₂ hbez x m hm hprod).trans
    (RingEquiv.ofBijective (restrictAssignments f₁ f₂ x m)
      (restrictAssignments_bijective hf₁ x m))

@[simp] theorem weightedSplittingEquiv_apply {α β f₁ f₂ : A[X]}
    (hf₁ : f₁.Monic) (hf₂ : f₂.Monic) (hbez : α*f₁ + β*f₂ = 1)
    (x : ι → A) (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hprod : rootProduct x m Finset.univ = f₁*f₂) (a : A)
    (σ : Admissible m f₁.natDegree) :
    weightedSplittingEquiv hf₁ hf₂ hbez x m hm hprod a σ = Ideal.Quotient.mk _ a := by
  exact splittingEquiv_apply hf₁ hf₂ hbez x m hm hprod a σ.val

/-- The splitting depends only on coprimeness; Bézout witnesses are chosen here. -/
def weightedSplittingEquivOfCoprime {f₁ f₂ : A[X]}
    (hf₁ : f₁.Monic) (hf₂ : f₂.Monic) (hcop : IsCoprime f₁ f₂)
    (x : ι → A) (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hprod : rootProduct x m Finset.univ = f₁*f₂) :
    A ≃+* ∀ σ : Admissible m f₁.natDegree,
      FactorRing f₁ f₂ x m (selected σ.val) :=
  weightedSplittingEquiv hf₁ hf₂ (Classical.choose_spec (Classical.choose_spec hcop)) x m hm hprod

@[simp] theorem weightedSplittingEquivOfCoprime_apply {f₁ f₂ : A[X]}
    (hf₁ : f₁.Monic) (hf₂ : f₂.Monic) (hcop : IsCoprime f₁ f₂)
    (x : ι → A) (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hprod : rootProduct x m Finset.univ = f₁*f₂) (a : A)
    (σ : Admissible m f₁.natDegree) :
    weightedSplittingEquivOfCoprime hf₁ hf₂ hcop x m hm hprod a σ = Ideal.Quotient.mk _ a :=
  weightedSplittingEquiv_apply hf₁ hf₂ _ x m hm hprod a σ

end KhanSL2.Factorization.WeightedRoots


