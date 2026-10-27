module

public import KhanSL2.ExteriorContraction

@[expose] public section

/-!
# Derivations specified by their generator values

The image of each differentiated factor is placed first. The resulting
extension is a sum of left multiplications followed by odd contractions.
This gives the precise Leibniz rule for either parity of the generator images.
-/

noncomputable section

namespace KhanSL2.FiniteExterior

variable {α : Type*} [DecidableEq α]

def extendDerivation (code : α → ℕ) (f : α → Exterior α) :
    Exterior α →ₗ[ℂ] Exterior α :=
  Finsupp.linearCombination ℂ fun s =>
    ∑ m ∈ s, ((-1 : ℂ) ^ position code m s) •
      wedge code (f m) (monomial (s.erase m))

@[simp] theorem extendDerivation_monomial
    (code : α → ℕ) (f : α → Exterior α) (s : Finset α) :
    extendDerivation code f (monomial s) =
      ∑ m ∈ s, ((-1 : ℂ) ^ position code m s) •
        wedge code (f m) (monomial (s.erase m)) := by
  simp [extendDerivation, monomial]

def finiteDerivation (code : α → ℕ) (f : α → Exterior α) (M : Finset α) :
    Exterior α →ₗ[ℂ] Exterior α :=
  ∑ m ∈ M, (wedgeLinear code (f m)).comp (contraction code m)

theorem finiteDerivation_apply (code : α → ℕ) (f : α → Exterior α)
    (M : Finset α) (u : Exterior α) :
    finiteDerivation code f M u =
      ∑ m ∈ M, wedge code (f m) (contraction code m u) := by
  simp [finiteDerivation, wedge, LinearMap.sum_apply]

theorem finiteDerivation_monomial
    (code : α → ℕ) (f : α → Exterior α) (M s : Finset α) (hs : s ⊆ M) :
    finiteDerivation code f M (monomial s) =
      extendDerivation code f (monomial s) := by
  rw [finiteDerivation_apply, extendDerivation_monomial]
  calc
    (∑ m ∈ M, wedge code (f m) (contraction code m (monomial s))) =
        ∑ m ∈ s, wedge code (f m) (contraction code m (monomial s)) := by
      symm
      exact Finset.sum_subset hs (fun m _ hm => by simp [hm])
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      simp [hm, wedge_smul_right]

def supportModes (u : Exterior α) : Finset α := u.support.biUnion id

theorem subset_supportModes {u : Exterior α} {s : Finset α} (hs : s ∈ u.support) :
    s ⊆ supportModes u := by
  intro m hm
  exact Finset.mem_biUnion.mpr ⟨s, hs, hm⟩

theorem finiteDerivation_eq
    (code : α → ℕ) (f : α → Exterior α) (M : Finset α) (u : Exterior α)
    (hu : supportModes u ⊆ M) :
    finiteDerivation code f M u = extendDerivation code f u := by
  have heq : u = ∑ s ∈ u.support, u s • monomial s := by
    simpa only [Finsupp.sum, monomial, Finsupp.smul_single, smul_eq_mul, mul_one]
      using (Finsupp.sum_single u).symm
  conv_lhs => rw [heq]
  conv_rhs => rw [heq]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro s hs
  rw [finiteDerivation_monomial code f M s ((subset_supportModes hs).trans hu)]

theorem finiteDerivation_wedge
    (code : α → ℕ) (hinj : Function.Injective code)
    (f : α → Exterior α) (M : Finset α) (u v : Exterior α) (r : ℂ)
    (hcomm : ∀m, wedge code (f m) (parityLinear u) =
      r • wedge code u (f m)) :
    finiteDerivation code f M (wedge code u v) =
      wedge code (finiteDerivation code f M u) v +
        r • wedge code u (finiteDerivation code f M v) := by
  simp only [finiteDerivation_apply]
  simp_rw [contraction_wedge code hinj, wedge_add_right, ← wedge_assoc,
    hcomm, wedge_smul_left, wedge_assoc]
  rw [Finset.sum_add_distrib]
  change _ = wedgeLinear code (∑ m ∈ M, _) v +
    r • wedgeLinear code u (∑ m ∈ M, _)
  simp only [map_sum, LinearMap.sum_apply, Finset.smul_sum]
  simp only [wedge, show ∀x y z, wedgeLinear code (wedgeLinear code x y) z =
    wedgeLinear code x (wedgeLinear code y z) from wedge_assoc code]

/-- The full Leibniz rule, with an arbitrary scalar twist on the fixed left input. -/
theorem extendDerivation_wedge
    (code : α → ℕ) (hinj : Function.Injective code)
    (f : α → Exterior α) (u v : Exterior α) (r : ℂ)
    (hcomm : ∀m, wedge code (f m) (parityLinear u) =
      r • wedge code u (f m)) :
    extendDerivation code f (wedge code u v) =
      wedge code (extendDerivation code f u) v +
        r • wedge code u (extendDerivation code f v) := by
  let M := supportModes u ∪ supportModes v ∪ supportModes (wedge code u v)
  have hu : supportModes u ⊆ M :=
    (Finset.subset_union_left).trans Finset.subset_union_left
  have hv : supportModes v ⊆ M :=
    (Finset.subset_union_right).trans Finset.subset_union_left
  have huv : supportModes (wedge code u v) ⊆ M := Finset.subset_union_right
  rw [← finiteDerivation_eq code f M _ huv,
    ← finiteDerivation_eq code f M _ hu,
    ← finiteDerivation_eq code f M _ hv]
  exact finiteDerivation_wedge code hinj f M u v r hcomm

theorem finiteDerivation_wedge_twist
    (code : α → ℕ) (hinj : Function.Injective code)
    (f : α → Exterior α) (M : Finset α) (u v u' : Exterior α)
    (hcomm : ∀m, wedge code (f m) (parityLinear u) = wedge code u' (f m)) :
    finiteDerivation code f M (wedge code u v) =
      wedge code (finiteDerivation code f M u) v +
        wedge code u' (finiteDerivation code f M v) := by
  simp only [finiteDerivation_apply]
  simp_rw [contraction_wedge code hinj, wedge_add_right, ← wedge_assoc,
    hcomm, wedge_assoc]
  rw [Finset.sum_add_distrib]
  change _ = wedgeLinear code (∑ m ∈ M, _) v +
    wedgeLinear code u' (∑ m ∈ M, _)
  simp only [map_sum, LinearMap.sum_apply]
  simp only [wedge, show ∀x y z, wedgeLinear code (wedgeLinear code x y) z =
    wedgeLinear code x (wedgeLinear code y z) from wedge_assoc code]

/-- A version allowing an arbitrary linear twist of the left argument. -/
theorem extendDerivation_wedge_twist
    (code : α → ℕ) (hinj : Function.Injective code)
    (f : α → Exterior α) (u v u' : Exterior α)
    (hcomm : ∀m, wedge code (f m) (parityLinear u) = wedge code u' (f m)) :
    extendDerivation code f (wedge code u v) =
      wedge code (extendDerivation code f u) v +
        wedge code u' (extendDerivation code f v) := by
  let M := supportModes u ∪ supportModes v ∪ supportModes (wedge code u v)
  have hu : supportModes u ⊆ M :=
    (Finset.subset_union_left).trans Finset.subset_union_left
  have hv : supportModes v ⊆ M :=
    (Finset.subset_union_right).trans Finset.subset_union_left
  have huv : supportModes (wedge code u v) ⊆ M := Finset.subset_union_right
  rw [← finiteDerivation_eq code f M _ huv,
    ← finiteDerivation_eq code f M _ hu,
    ← finiteDerivation_eq code f M _ hv]
  exact finiteDerivation_wedge_twist code hinj f M u v u' hcomm

end KhanSL2.FiniteExterior
