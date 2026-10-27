module

public import KhanSL2.SourceGrading
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Finite sectors of the source

Only spanning monomials are used: no independence or presentation-normal-form
theorem is assumed.  The sector indices count X factors, Y factors, and the
sum of derivative indices, respectively.
-/

noncomputable section

namespace KhanSL2.Source

def xProduct (xs : List ℕ) : Source := (xs.map X).prod

def yProduct (ys : List ℕ) : Source := (ys.map Y).prod

def jetMonomial (xs ys : List ℕ) : Source := xProduct xs * yProduct ys

@[simp] theorem xProduct_nil : xProduct [] = 1 := rfl
@[simp] theorem yProduct_nil : yProduct [] = 1 := rfl
@[simp] theorem xProduct_cons (i : ℕ) (xs : List ℕ) :
    xProduct (i :: xs) = X i * xProduct xs := rfl
@[simp] theorem yProduct_cons (i : ℕ) (ys : List ℕ) :
    yProduct (i :: ys) = Y i * yProduct ys := rfl

@[simp] theorem xProduct_append (xs xs' : List ℕ) :
    xProduct (xs ++ xs') = xProduct xs * xProduct xs' := by
  simp [xProduct, List.map_append, List.prod_append]

@[simp] theorem yProduct_append (ys ys' : List ℕ) :
    yProduct (ys ++ ys') = yProduct ys * yProduct ys' := by
  simp [yProduct, List.map_append, List.prod_append]

theorem yProduct_mul_X (ys : List ℕ) (i : ℕ) :
    yProduct ys * X i = X i * yProduct ys := by
  induction ys with
  | nil => simp
  | cons j ys ih =>
    simp only [yProduct_cons]
    calc
      (Y j * yProduct ys) * X i = Y j * (yProduct ys * X i) := mul_assoc _ _ _
      _ = Y j * (X i * yProduct ys) := by rw [ih]
      _ = (Y j * X i) * yProduct ys := (mul_assoc _ _ _).symm
      _ = (X i * Y j) * yProduct ys := by rw [← X_mul_Y]
      _ = X i * (Y j * yProduct ys) := mul_assoc _ _ _

theorem yProduct_mul_xProduct (ys xs : List ℕ) :
    yProduct ys * xProduct xs = xProduct xs * yProduct ys := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [xProduct_cons]
    calc
      yProduct ys * (X i * xProduct xs) = (yProduct ys * X i) * xProduct xs :=
        (mul_assoc _ _ _).symm
      _ = (X i * yProduct ys) * xProduct xs := by rw [yProduct_mul_X]
      _ = X i * (yProduct ys * xProduct xs) := mul_assoc _ _ _
      _ = X i * (xProduct xs * yProduct ys) := by rw [ih]
      _ = (X i * xProduct xs) * yProduct ys := (mul_assoc _ _ _).symm

theorem jetMonomial_mul (xs ys xs' ys' : List ℕ) :
    jetMonomial xs ys * jetMonomial xs' ys' =
      jetMonomial (xs ++ xs') (ys ++ ys') := by
  simp only [jetMonomial, xProduct_append, yProduct_append]
  calc
    (xProduct xs * yProduct ys) * (xProduct xs' * yProduct ys') =
        xProduct xs * ((yProduct ys * xProduct xs') * yProduct ys') := by
          simp only [mul_assoc]
    _ = xProduct xs * ((xProduct xs' * yProduct ys) * yProduct ys') := by
          rw [yProduct_mul_xProduct]
    _ = (xProduct xs * xProduct xs') * (yProduct ys * yProduct ys') := by
          simp only [mul_assoc]

/-- The manuscript's `(r,s,N)` in the existing `(total CE,B,spin)` grading. -/
def sectorDegree (r s N : ℕ) : Degree :=
  (2 * (r : ℤ) + 3 * (s : ℤ), (r : ℤ) + 3 * (s : ℤ),
    2 * (r : ℤ) + 3 * (s : ℤ) + (N : ℤ))

@[simp] theorem sectorDegree_zero : sectorDegree 0 0 0 = 0 := by
  simp [sectorDegree]

theorem sectorDegree_add (r s N r' s' N' : ℕ) :
    sectorDegree (r + r') (s + s') (N + N') =
      sectorDegree r s N + sectorDegree r' s' N' := by
  ext <;> simp [sectorDegree, Nat.cast_add] <;> ring

theorem sectorDegree_injective :
    Function.Injective (fun t : ℕ × ℕ × ℕ => sectorDegree t.1 t.2.1 t.2.2) := by
  rintro ⟨r, s, N⟩ ⟨r', s', N'⟩ h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg (fun d : Degree => d.2.1) h
  have h₃ := congrArg (fun d : Degree => d.2.2) h
  simp only [sectorDegree, Prod.fst, Prod.snd] at h₁ h₂ h₃
  have hr : r = r' := by omega
  have hs : s = s' := by omega
  have hN : N = N' := by omega
  simp [hr, hs, hN]

theorem xProduct_mem (xs : List ℕ) :
    xProduct xs ∈ piece (sectorDegree xs.length 0 xs.sum) := by
  induction xs with
  | nil => simpa using one_mem
  | cons i xs ih =>
    have hx : X i ∈ piece (sectorDegree 1 0 i) := by
      simpa [sectorDegree, add_comm] using X_mem i
    have h := mul_mem hx ih
    rw [← sectorDegree_add] at h
    simpa [Nat.add_comm] using h

theorem yProduct_mem (ys : List ℕ) :
    yProduct ys ∈ piece (sectorDegree 0 ys.length ys.sum) := by
  induction ys with
  | nil => simpa using one_mem
  | cons i ys ih =>
    have hy : Y i ∈ piece (sectorDegree 0 1 i) := by
      simpa [sectorDegree, add_comm] using Y_mem i
    have h := mul_mem hy ih
    rw [← sectorDegree_add] at h
    simpa [Nat.add_comm] using h

theorem jetMonomial_mem_piece (xs ys : List ℕ) :
    jetMonomial xs ys ∈ piece (sectorDegree xs.length ys.length (xs.sum + ys.sum)) := by
  have h := mul_mem (xProduct_mem xs) (yProduct_mem ys)
  rw [← sectorDegree_add] at h
  simpa only [Nat.add_zero, Nat.zero_add, jetMonomial] using h

/-- The sector is a span of finite labelled monomials, not an assumed basis. -/
def sector (r s N : ℕ) : Submodule ℂ Source :=
  Submodule.span ℂ {a | ∃ xs ys : List ℕ,
    xs.length = r ∧ ys.length = s ∧ xs.sum + ys.sum = N ∧ jetMonomial xs ys = a}

theorem jetMonomial_mem_sector (xs ys : List ℕ) :
    jetMonomial xs ys ∈ sector xs.length ys.length (xs.sum + ys.sum) :=
  Submodule.subset_span ⟨xs, ys, rfl, rfl, rfl, rfl⟩

theorem sector_le_piece (r s N : ℕ) : sector r s N ≤ piece (sectorDegree r s N) := by
  apply Submodule.span_le.mpr
  rintro a ⟨xs, ys, rfl, rfl, rfl, rfl⟩
  exact jetMonomial_mem_piece xs ys

theorem sector_mul_mem {r s N r' s' N' : ℕ} {a b : Source}
    (ha : a ∈ sector r s N) (hb : b ∈ sector r' s' N') :
    a * b ∈ sector (r + r') (s + s') (N + N') := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨xs, ys, hxs, hys, hN, rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨xs', ys', hxs', hys', hN', rfl⟩ := hb
      rw [jetMonomial_mul]
      apply Submodule.subset_span
      refine ⟨xs ++ xs', ys ++ ys', ?_, ?_, ?_, rfl⟩
      · simp [hxs, hxs']
      · simp [hys, hys']
      · simp only [List.sum_append]
        omega
    | zero => simp
    | add b c hb hc ib ic =>
      simpa only [mul_add] using (sector (r + r') (s + s') (N + N')).add_mem ib ic
    | smul k b hb ib =>
      simpa only [mul_smul_comm] using
        (sector (r + r') (s + s') (N + N')).smul_mem k ib
  | zero => simp
  | add a c ha hc ia ic =>
    simpa only [add_mul] using (sector (r + r') (s + s') (N + N')).add_mem ia ic
  | smul k a ha ia =>
    simpa only [smul_mul_assoc] using
      (sector (r + r') (s + s') (N + N')).smul_mem k ia

abbrev SectorIndex := ℕ × ℕ × ℕ

def indexedSector (t : SectorIndex) : Submodule ℂ Source := sector t.1 t.2.1 t.2.2

theorem one_mem_sector : (1 : Source) ∈ sector 0 0 0 := by
  simpa [jetMonomial] using jetMonomial_mem_sector [] []

theorem X_mem_sector (i : ℕ) : X i ∈ sector 1 0 i := by
  simpa [jetMonomial] using jetMonomial_mem_sector [i] []

theorem Y_mem_sector (i : ℕ) : Y i ∈ sector 0 1 i := by
  simpa [jetMonomial] using jetMonomial_mem_sector [] [i]

theorem indexedSector_iSup_mul_mem {a b : Source}
    (ha : a ∈ ⨆ t, indexedSector t) (hb : b ∈ ⨆ t, indexedSector t) :
    a * b ∈ ⨆ t, indexedSector t := by
  refine Submodule.iSup_induction indexedSector
    (motive := fun a => a * b ∈ ⨆ t, indexedSector t) ha ?_ ?_ ?_
  · rintro ⟨r, s, N⟩ a ha
    refine Submodule.iSup_induction indexedSector
      (motive := fun b => a * b ∈ ⨆ t, indexedSector t) hb ?_ ?_ ?_
    · rintro ⟨r', s', N'⟩ b hb
      exact Submodule.mem_iSup_of_mem (r + r', s + s', N + N') (sector_mul_mem ha hb)
    · simp
    · intro b c hb hc
      simpa only [mul_add] using (⨆ t, indexedSector t).add_mem hb hc
  · simp
  · intro a c ha hc
    simpa only [add_mul] using (⨆ t, indexedSector t).add_mem ha hc

theorem indexedSector_iSup_eq_top : (⨆ t, indexedSector t) = ⊤ := by
  suffices h : ∀ a : Source, a ∈ ⨆ t, indexedSector t from top_unique (fun a _ => h a)
  intro a
  induction a using inductionOn with
  | scalar k =>
    apply Submodule.mem_iSup_of_mem (0, 0, 0)
    simpa only [Algebra.smul_def, mul_one, indexedSector] using (sector 0 0 0).smul_mem k one_mem_sector
  | hx i => exact Submodule.mem_iSup_of_mem (1, 0, i) (X_mem_sector i)
  | hy i => exact Submodule.mem_iSup_of_mem (0, 1, i) (Y_mem_sector i)
  | add a b ha hb => exact (⨆ t, indexedSector t).add_mem ha hb
  | mul a b ha hb => exact indexedSector_iSup_mul_mem ha hb

theorem coaction_indexedSector_coe
    (a : DirectSum SectorIndex fun t => indexedSector t) (t : SectorIndex) :
    (coaction (DirectSum.coeLinearMap indexedSector a)).coeff
        (sectorDegree t.1 t.2.1 t.2.2) = (a t : Source) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of u a =>
    rw [DirectSum.coeLinearMap_of,
      coaction_of_mem (sector_le_piece u.1 u.2.1 u.2.2 a.property)]
    by_cases h : u = t
    · subst u
      simp
    · have hd : sectorDegree u.1 u.2.1 u.2.2 ≠ sectorDegree t.1 t.2.1 t.2.2 :=
        fun hd => h (sectorDegree_injective hd)
      simp [Finsupp.single_eq_of_ne (Ne.symm hd), DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
  | add a b ha hb =>
    simp only [map_add]
    change (coaction (DirectSum.coeLinearMap indexedSector a)).coeff
        (sectorDegree t.1 t.2.1 t.2.2) +
      (coaction (DirectSum.coeLinearMap indexedSector b)).coeff
        (sectorDegree t.1 t.2.1 t.2.2) = (a t : Source) + (b t : Source)
    rw [ha, hb]

/-- The finite-expression source is the internal direct sum of its sectors. -/
theorem sector_grading_internal : DirectSum.IsInternal indexedSector := by
  change Function.Bijective (DirectSum.coeLinearMap indexedSector)
  constructor
  · intro a b hab
    apply DFinsupp.ext
    intro t
    apply Subtype.ext
    rw [← coaction_indexedSector_coe a t, ← coaction_indexedSector_coe b t, hab]
  · apply LinearMap.range_eq_top.mp
    rw [DirectSum.range_coeLinearMap, indexedSector_iSup_eq_top]

end KhanSL2.Source
