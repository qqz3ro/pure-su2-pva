module

public import KhanSL2.Deformation.Derivations
public import KhanSL2.CochainGrading
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Set.Finite.Powerset

@[expose] public section

/-!
# Additive gradings of the cochain algebra by generator weights

A function `g : Mode → G` into an additive group grades the exterior monomials by
`gdeg g s = Σ_{m ∈ s} g m`. This file records the generic facts used repeatedly in §5:

* `gPiece g d`, `gProj g d`: homogeneous pieces and projections (an instance of
  `BasisGrading`); `sum_gProj`, `mem_gPiece_of_gProj`;
* products, generators, derivations (`extendDerivation_mem_gPiece`) and algebra endomorphisms
  (`algHom_mem_gPiece`) respect the grading;
* homogeneous operators commute with the projections (`gProj_comm`);
* disjointness of distinct pieces (`disjoint_gPiece`), and finite-dimensionality when a
  nonnegative coordinate of the grading has finite sublevel sets on generators
  (`finiteDimensional_gPiece`).
-/

noncomputable section

namespace KhanSL2

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The `g`-degree of an exterior monomial. -/
def gdeg (g : Mode → G) (s : ExteriorMonomial) : G := ∑ m ∈ s, g m

/-- Cochains homogeneous of `g`-degree `d`. -/
def gPiece (g : Mode → G) (d : G) : Submodule ℂ Cochain := BasisGrading.piece (gdeg g) d

/-- The projection onto `g`-degree `d`. -/
def gProj (g : Mode → G) (d : G) : Cochain →ₗ[ℂ] Cochain := BasisGrading.projection (gdeg g) d

variable (g : Mode → G)

@[simp] theorem gProj_apply (d : G) (v : Cochain) (s : ExteriorMonomial) :
    gProj g d v s = if gdeg g s = d then v s else 0 := rfl

omit [DecidableEq G] in
theorem mem_gPiece_iff {d : G} {u : Cochain} : u ∈ gPiece g d ↔ ∀ s ∈ u.support, gdeg g s = d :=
  Finsupp.mem_supported ℂ u

omit [DecidableEq G] in
theorem single_mem_gPiece (s : ExteriorMonomial) (r : ℂ) :
    Finsupp.single s r ∈ gPiece g (gdeg g s) := BasisGrading.single_mem (gdeg g) s r

theorem gProj_mem (d : G) (v : Cochain) : gProj g d v ∈ gPiece g d :=
  BasisGrading.projection_mem (gdeg g) d v

theorem gProj_of_mem {d : G} {v : Cochain} (hv : v ∈ gPiece g d) : gProj g d v = v :=
  BasisGrading.projection_of_mem (gdeg g) hv

theorem gProj_of_mem_ne {d e : G} (hde : d ≠ e) {v : Cochain} (hv : v ∈ gPiece g e) :
    gProj g d v = 0 := BasisGrading.projection_of_mem_ne (gdeg g) hde hv

/-- Every cochain is the sum of its homogeneous components. -/
theorem sum_gProj (v : Cochain) : ∑ d ∈ v.support.image (gdeg g), gProj g d v = v := by
  ext s
  simp only [Finset.sum_apply', gProj_apply]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hs
    exact h (Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.mpr (Ne.symm hs)))

/-- A cochain whose components outside degree `d` vanish is homogeneous of degree `d`. -/
theorem mem_gPiece_of_gProj {d : G} {v : Cochain} (h : ∀ e, e ≠ d → gProj g e v = 0) :
    v ∈ gPiece g d := by
  rw [mem_gPiece_iff]
  intro s hs
  by_contra hne
  have := congrArg (fun w : Cochain => w s) (h (gdeg g s) hne)
  simp only [gProj_apply, if_pos rfl, Finsupp.coe_zero, Pi.zero_apply] at this
  exact Finsupp.mem_support_iff.mp hs this

/-- Two cochains with the same components are equal. -/
theorem eq_of_gProj {v w : Cochain} (h : ∀ d, gProj g d v = gProj g d w) : v = w := by
  ext s
  have := congrArg (fun u : Cochain => u s) (h (gdeg g s))
  simpa using this

/-- **Homogeneous operators commute with the projections.** -/
theorem gProj_comm (E : Cochain →ₗ[ℂ] Cochain) (δ : G)
    (hE : ∀ d u, u ∈ gPiece g d → E u ∈ gPiece g (d + δ)) (d : G) (v : Cochain) :
    gProj g (d + δ) (E v) = E (gProj g d v) :=
  BasisGrading.projection_linearMap (gdeg g) E (fun d => d + δ) (fun _ _ h => add_right_cancel h)
    hE d v

theorem gProj_comm_zero (E : Cochain →ₗ[ℂ] Cochain)
    (hE : ∀ d u, u ∈ gPiece g d → E u ∈ gPiece g d) (d : G) (v : Cochain) :
    gProj g d (E v) = E (gProj g d v) := by
  simpa using gProj_comm g E 0 (fun d u hu => by simpa using hE d u hu) d v

omit [DecidableEq G] in
theorem gdeg_union {s t : ExteriorMonomial} (h : Disjoint s t) :
    gdeg g (s ∪ t) = gdeg g s + gdeg g t := Finset.sum_union h

omit [DecidableEq G] in
theorem gdeg_erase_add {m : Mode} {s : ExteriorMonomial} (hm : m ∈ s) :
    gdeg g (s.erase m) + g m = gdeg g s := Finset.sum_erase_add s g hm

omit [DecidableEq G] in
theorem monomialWedge_mem_gPiece (s t : ExteriorMonomial) :
    monomialWedge s t ∈ gPiece g (gdeg g s + gdeg g t) := by
  unfold monomialWedge
  split
  · rename_i h
    rw [← gdeg_union g h]
    exact single_mem_gPiece g _ _
  · exact (gPiece g _).zero_mem

omit [DecidableEq G] in
theorem mul_mem_gPiece {d e : G} {u v : Cochain} (hu : u ∈ gPiece g d) (hv : v ∈ gPiece g e) :
    u * v ∈ gPiece g (d + e) := by
  rw [cochain_mul_eq_wedge, ← u.sum_single, ← v.sum_single]
  simp only [Finsupp.sum, wedge, map_sum, LinearMap.sum_apply]
  apply (gPiece g _).sum_mem
  intro t ht
  apply (gPiece g _).sum_mem
  intro s hs
  have hd : gdeg g s = d := (mem_gPiece_iff g).mp hu s hs
  have he : gdeg g t = e := (mem_gPiece_iff g).mp hv t ht
  simp only [wedgeLinear, Finsupp.linearCombination_single, LinearMap.smul_apply, smul_smul]
  apply (gPiece g _).smul_mem
  simpa only [hd, he] using monomialWedge_mem_gPiece g s t

omit [DecidableEq G] in
theorem generator_mem_gPiece (m : Mode) : generator m ∈ gPiece g (g m) := by
  simpa [gdeg, generator] using single_mem_gPiece g {m} 1

omit [DecidableEq G] in
theorem one_mem_gPiece : cochainOne ∈ gPiece g 0 := by
  simpa [gdeg, cochainOne] using single_mem_gPiece g ∅ 1

omit [DecidableEq G] in
theorem generator_mul_mem_gPiece (m : Mode) {d : G} {u : Cochain} (hu : u ∈ gPiece g d) :
    generator m * u ∈ gPiece g (g m + d) := mul_mem_gPiece g (generator_mem_gPiece g m) hu

omit [DecidableEq G] in
/-- **Derivations with homogeneous generator values are homogeneous.** -/
theorem extendDerivation_mem_gPiece (f : Mode → Cochain) (δ : G)
    (hf : ∀ m, f m ∈ gPiece g (g m + δ)) {d : G} {u : Cochain} (hu : u ∈ gPiece g d) :
    extendDerivation f u ∈ gPiece g (d + δ) := by
  rw [← u.sum_single]
  simp only [Finsupp.sum, map_sum, extendDerivation, Finsupp.linearCombination_single]
  apply (gPiece g _).sum_mem
  intro s hs
  apply (gPiece g _).smul_mem
  apply (gPiece g _).sum_mem
  intro m hm
  apply (gPiece g _).smul_mem
  have hd : gdeg g s = d := (mem_gPiece_iff g).mp hu s hs
  have heq : (g m + δ) + gdeg g (s.erase m) = d + δ := by
    rw [← hd, ← gdeg_erase_add g hm]; abel
  rw [← heq, ← cochain_mul_eq_wedge]
  exact mul_mem_gPiece g (hf m) (single_mem_gPiece g _ 1)

/-- Left multiplication by a homogeneous element commutes with the projections. -/
theorem gProj_mul_left {e : G} {a : Cochain} (ha : a ∈ gPiece g e) (d : G) (v : Cochain) :
    gProj g (d + e) (a * v) = a * gProj g d v := by
  have := gProj_comm g (LinearMap.mulLeft ℂ a) e
    (fun d u hu => by rw [add_comm]; exact mul_mem_gPiece g ha hu) d v
  simpa using this

/-- **Algebra endomorphisms with homogeneous generator images are homogeneous**, possibly for a
different grading `g'` of the target. -/
theorem algHom_gProj' (g' : Mode → G) (F : Cochain →ₐ[ℂ] Cochain)
    (hF : ∀ m, F (generator m) ∈ gPiece g' (g m)) (u : Cochain) (d : G) :
    gProj g' d (F u) = F (gProj g d u) := by
  induction u using cochain_induction generalizing d with
  | hzero => simp
  | hone =>
    have h1 : F cochainOne = cochainOne := by rw [← cochain_one_eq, map_one]
    rw [h1]
    by_cases hd : d = 0
    · subst hd; rw [gProj_of_mem g' (one_mem_gPiece g'), gProj_of_mem g (one_mem_gPiece g), h1]
    · rw [gProj_of_mem_ne g' hd (one_mem_gPiece g'), gProj_of_mem_ne g hd (one_mem_gPiece g),
        map_zero]
  | hadd u v hu hv => simp only [map_add, hu, hv]
  | hsmul r u hu => simp only [map_smul, hu]
  | hgen m u hu =>
    rw [← cochain_mul_eq_wedge, map_mul]
    have h1 := gProj_mul_left g' (hF m) (d - g m) (F u)
    have h2 := gProj_mul_left g (generator_mem_gPiece g m) (d - g m) u
    rw [sub_add_cancel] at h1 h2
    rw [h1, h2, map_mul, hu]

theorem algHom_mem_gPiece' (g' : Mode → G) (F : Cochain →ₐ[ℂ] Cochain)
    (hF : ∀ m, F (generator m) ∈ gPiece g' (g m)) {d : G} {u : Cochain} (hu : u ∈ gPiece g d) :
    F u ∈ gPiece g' d := by
  rw [← gProj_of_mem g hu, ← algHom_gProj' g g' F hF]
  exact gProj_mem g' d _

theorem algHom_gProj (F : Cochain →ₐ[ℂ] Cochain) (hF : ∀ m, F (generator m) ∈ gPiece g (g m))
    (u : Cochain) (d : G) : gProj g d (F u) = F (gProj g d u) := algHom_gProj' g g F hF u d

theorem algHom_mem_gPiece (F : Cochain →ₐ[ℂ] Cochain) (hF : ∀ m, F (generator m) ∈ gPiece g (g m))
    {d : G} {u : Cochain} (hu : u ∈ gPiece g d) : F u ∈ gPiece g d :=
  algHom_mem_gPiece' g g F hF hu

/-- Distinct homogeneous pieces are disjoint from each other. -/
theorem disjoint_gPiece {ι : Type*} {p : Submodule ℂ Cochain} {q : ι → Submodule ℂ Cochain}
    {d : G} {e : ι → G} (hp : p ≤ gPiece g d) (hq : ∀ j, q j ≤ gPiece g (e j))
    (hne : ∀ j, e j ≠ d) : Disjoint p (⨆ j, q j) := by
  rw [Submodule.disjoint_def]
  intro x hxp hxq
  have hker : (⨆ j, q j) ≤ LinearMap.ker (gProj g d) :=
    iSup_le fun j y hy => gProj_of_mem_ne g (Ne.symm (hne j)) (hq j hy)
  have := hker hxq
  rw [LinearMap.mem_ker, gProj_of_mem g (hp hxp)] at this
  exact this

/-- Projections only shrink the support. -/
theorem gProj_mem_of_mem {G' : Type*} [AddCommGroup G'] (g' : Mode → G') {e : G'} {z : Cochain}
    (hz : z ∈ gPiece g' e) (d : G) :
    gProj g d z ∈ gPiece g' e := by
  rw [mem_gPiece_iff] at hz ⊢
  intro s hs
  apply hz s
  rw [Finsupp.mem_support_iff] at hs ⊢
  intro h0
  apply hs
  simp [h0]

theorem eq_zero_of_mem_ne {d e : G} {u : Cochain} (hd : u ∈ gPiece g d) (he : u ∈ gPiece g e)
    (h : d ≠ e) : u = 0 := by
  rw [← gProj_of_mem g hd]
  exact gProj_of_mem_ne g h he

theorem disjoint_of_le_ker {p q : Submodule ℂ Cochain} {d : G} (hp : p ≤ gPiece g d)
    (hq : q ≤ LinearMap.ker (gProj g d)) : Disjoint p q := by
  rw [Submodule.disjoint_def]
  intro x hxp hxq
  have := hq hxq
  rwa [LinearMap.mem_ker, gProj_of_mem g (hp hxp)] at this

omit [DecidableEq G] in
/-- Pushing a grading forward along an additive map. -/
theorem gPiece_le_map {G' : Type*} [AddCommGroup G'] [DecidableEq G'] (φ : G →+ G') (d : G) :
    gPiece g d ≤ gPiece (fun m => φ (g m)) (φ d) := by
  intro u hu
  rw [mem_gPiece_iff] at hu ⊢
  intro s hs
  simp only [gdeg, ← map_sum]
  exact congrArg φ (hu s hs)

omit [DecidableEq G] in
/-- **Finite-dimensionality** of the pieces, when a nonnegative coordinate of the grading has
finite sublevel sets on the generators. -/
theorem finite_gdeg (h : G →+ ℤ) (hpos : ∀ m, 0 ≤ h (g m))
    (hfin : ∀ K : ℤ, Set.Finite {m | h (g m) ≤ K}) (d : G) :
    Set.Finite {s : ExteriorMonomial | gdeg g s = d} := by
  have hF := hfin (h d)
  refine (hF.toFinset.powerset.finite_toSet).subset fun s hs =>
    Finset.mem_coe.mpr (Finset.mem_powerset.mpr fun m hm => ?_)
  rw [Set.Finite.mem_toFinset]
  change h (g m) ≤ h d
  rw [← (show gdeg g s = d from hs), gdeg, map_sum]
  exact Finset.single_le_sum (f := fun m => h (g m)) (fun m _ => hpos m) hm

omit [DecidableEq G] in
theorem finiteDimensional_gPiece {d : G} (hfin : Set.Finite {s : ExteriorMonomial | gdeg g s = d}) :
    FiniteDimensional ℂ (gPiece g d) := by
  have := hfin.to_subtype
  exact LinearEquiv.finiteDimensional (Finsupp.supportedEquivFinsupp (M := ℂ) (R := ℂ)
    {s : ExteriorMonomial | gdeg g s = d}).symm

omit [DecidableEq G] in
/-- Generator memberships transported along an additive map of gradings. -/
theorem map_gen_mem {G' : Type*} [AddCommGroup G'] [DecidableEq G'] (g' : Mode → G')
    (φ : G →+ G') (hφ : ∀ m, φ (g m) = g' m) {f : Mode → Cochain} {δ : G}
    (hf : ∀ m, f m ∈ gPiece g (g m + δ)) (m : Mode) : f m ∈ gPiece g' (g' m + φ δ) := by
  have h := gPiece_le_map g φ _ (hf m)
  have heq : (fun m => φ (g m)) = g' := funext hφ
  rw [heq, map_add, hφ] at h
  exact h


end KhanSL2
