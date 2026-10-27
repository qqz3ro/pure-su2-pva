module

public import KhanSL2.Deformation.SplitIdentities
public import KhanSL2.Deformation.Grading

@[expose] public section

/-!
# Gradings of the split complex

* `Mode.tdeg`: the degree `T = S - B` of a generator (`b_j ↦ j`, `c_j ↦ j + 1`);
* `coarse m = (1, T)`: cochain degree and `T`; the Casimir arguments run on its pieces, which are
  finite-dimensional (`finiteDimensional_coarse`);
* `fine m = (1, B, T_c, T_b)`: cochain degree, `b`-count, and the `T`-degrees of the `c` and `b`
  modes separately; `d_c`, `d_Z`, `d_g` and the colour actions are homogeneous for it.
-/

noncomputable section

namespace KhanSL2

open Deformation

/-- `T = S - B` of a generator. -/
def Mode.tdeg : Mode → ℤ
  | .b j _ => j
  | .c j _ => j + 1

/-- `T` of the `c` modes. -/
def Mode.tcDeg : Mode → ℤ
  | .b _ _ => 0
  | .c j _ => j + 1

/-- `T` of the `b` modes. -/
def Mode.tbDeg : Mode → ℤ
  | .b j _ => j
  | .c _ _ => 0

/-- Cochain degree and `T`. -/
def coarse (m : Mode) : ℤ × ℤ := (1, m.tdeg)

/-- Cochain degree, `b`-count, and the `T`-degrees of the `c` and `b` modes. -/
def fine (m : Mode) : ℤ × ℤ × ℤ × ℤ := (1, (m.bCount : ℤ), m.tcDeg, m.tbDeg)

/-- Forgetting the refinement. -/
def fineToCoarse : ℤ × ℤ × ℤ × ℤ →+ ℤ × ℤ where
  toFun d := (d.1, d.2.2.1 + d.2.2.2)
  map_zero' := rfl
  map_add' d e := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
    congr 1; ring

theorem fineToCoarse_fine (m : Mode) : fineToCoarse (fine m) = coarse m := by
  cases m <;> simp [fineToCoarse, fine, coarse, Mode.tcDeg, Mode.tbDeg, Mode.tdeg]

theorem fine_le_coarse (d : ℤ × ℤ × ℤ × ℤ) : gPiece fine d ≤ gPiece coarse (fineToCoarse d) := by
  have h := gPiece_le_map fine fineToCoarse d
  simpa only [fineToCoarse_fine] using h

theorem Mode.tdeg_nonneg (m : Mode) : 0 ≤ m.tdeg := by
  cases m <;> simp only [Mode.tdeg] <;> omega

theorem finite_tdeg_le (K : ℤ) : Set.Finite {m : Mode | m.tdeg ≤ K} := by
  let R : Finset (ℕ × Fin 3) := Finset.range (K.toNat + 1) ×ˢ Finset.univ
  let S : Finset Mode := R.image (fun p => Mode.b p.1 p.2) ∪ R.image (fun p => Mode.c p.1 p.2)
  refine S.finite_toSet.subset ?_
  intro m hm
  simp only [Set.mem_setOf_eq] at hm
  simp only [S, R, Finset.coe_union, Finset.coe_image, Finset.coe_product, Finset.coe_range,
    Finset.coe_univ, Set.mem_union, Set.mem_image, Set.mem_prod, Set.mem_Iio, Set.mem_univ,
    and_true, Prod.exists]
  cases m with
  | b j a =>
    left; refine ⟨j, a, ?_, rfl⟩
    simp only [Mode.tdeg] at hm; omega
  | c j a =>
    right; refine ⟨j, a, ?_, rfl⟩
    simp only [Mode.tdeg] at hm; omega

theorem finite_coarse (d : ℤ × ℤ) : Set.Finite {s : ExteriorMonomial | gdeg coarse s = d} :=
  finite_gdeg coarse (AddMonoidHom.snd ℤ ℤ) (fun m => Mode.tdeg_nonneg m)
    (fun K => finite_tdeg_le K) d

theorem finiteDimensional_coarse (d : ℤ × ℤ) : FiniteDimensional ℂ (gPiece coarse d) :=
  finiteDimensional_gPiece coarse (finite_coarse d)

theorem finite_fine (d : ℤ × ℤ × ℤ × ℤ) : Set.Finite {s : ExteriorMonomial | gdeg fine s = d} := by
  have h := finite_coarse (fineToCoarse d)
  refine h.subset fun s hs => ?_
  simp only [Set.mem_setOf_eq] at hs ⊢
  rw [← hs, gdeg, gdeg, map_sum]
  simp only [fineToCoarse_fine]

theorem finiteDimensional_fine (d : ℤ × ℤ × ℤ × ℤ) : FiniteDimensional ℂ (gPiece fine d) :=
  finiteDimensional_gPiece fine (finite_fine d)

/-! ## Homogeneity of the generator images -/

theorem bbPair_mem_fine (i k : ℕ) (a : Fin 3) :
    bbPair i k a ∈ gPiece fine (2, 2, 0, (i : ℤ) + k) := by
  apply (gPiece _ _).sum_mem; intro b _
  apply (gPiece _ _).sum_mem; intro c _
  apply (gPiece _ _).smul_mem
  have h := mul_mem_gPiece fine (generator_mem_gPiece fine (.b i b))
    (generator_mem_gPiece fine (.b k c))
  convert h using 1
  simp [fine, Mode.bCount, Mode.tcDeg, Mode.tbDeg]

theorem colorGenerator_mem_fine (e : Fin 3) (m : Mode) :
    colorGenerator e m ∈ gPiece fine (fine m) := by
  apply (gPiece _ _).sum_mem; intro c _
  apply (gPiece _ _).smul_mem
  have h := generator_mem_gPiece fine (m.recolor c)
  cases m <;> exact h

theorem qGenerator_c_mem_fine (j : ℕ) (a : Fin 3) :
    qGenerator (.c j a) ∈ gPiece fine (fine (.c j a) + (1, 0, 0, 0)) := by
  apply (gPiece _ _).smul_mem
  apply (gPiece _ _).sum_mem; intro i hi
  have hi' := Finset.mem_range.mp hi
  apply (gPiece _ _).sum_mem; intro b _
  apply (gPiece _ _).sum_mem; intro c _
  apply (gPiece _ _).smul_mem
  rw [← cochain_mul_eq_wedge]
  have h := mul_mem_gPiece fine (generator_mem_gPiece fine (.c i b))
    (generator_mem_gPiece fine (.c (j - 1 - i) c))
  convert h using 2
  simp only [fine, Mode.bCount, Mode.tcDeg, Mode.tbDeg, Prod.mk_add_mk, Prod.mk.injEq,
    Nat.cast_zero, true_and, and_true]
  omega

theorem zzConv_mem_fine (j : ℕ) (a : Fin 3) :
    zzConv j a ∈ gPiece fine (2, 2, 0, (j : ℤ) + 1) := by
  apply (gPiece _ _).sum_mem; intro i hi
  have hi' := Finset.mem_range.mp hi
  have h := bbPair_mem_fine (i + 1) (j - i) a
  convert h using 3
  push_cast [Nat.cast_sub hi'.le]
  ring_nf

theorem bbConv_mem_fine (j : ℕ) (a : Fin 3) : bbConv j a ∈ gPiece fine (2, 2, 0, (j : ℤ)) := by
  apply (gPiece _ _).sum_mem; intro i hi
  have hi' := Finset.mem_range.mp hi
  have h := bbPair_mem_fine i (j - i) a
  convert h using 3
  push_cast [Nat.cast_sub (Nat.lt_succ_iff.mp hi')]
  ring_nf

theorem dCGen_mem_fine (m : Mode) : dCGen m ∈ gPiece fine (fine m + (1, 0, 0, 0)) := by
  cases m with
  | c j a => exact qGenerator_c_mem_fine j a
  | b j a => exact (gPiece _ _).zero_mem

theorem dZGen_mem_fine (m : Mode) : dZGen m ∈ gPiece fine (fine m + (1, 1, 0, 0)) := by
  cases m with
  | c j a => exact (gPiece _ _).zero_mem
  | b j a =>
    cases j with
    | zero => exact (gPiece _ _).zero_mem
    | succ j =>
      apply (gPiece _ _).smul_mem
      convert zzConv_mem_fine j a using 2
      simp [fine, Mode.bCount, Mode.tcDeg, Mode.tbDeg]

theorem dGGen_mem_fine (m : Mode) : dGGen m ∈ gPiece fine (fine m + (1, 1, 0, 0)) := by
  cases m with
  | c j a => exact (gPiece _ _).zero_mem
  | b j a =>
    cases j with
    | succ j => exact (gPiece _ _).zero_mem
    | zero =>
      apply (gPiece _ _).smul_mem
      convert bbPair_mem_fine 0 0 a using 2
      simp [fine, Mode.bCount, Mode.tcDeg, Mode.tbDeg]

theorem dppGen_mem_coarse (m : Mode) : dppGen m ∈ gPiece coarse (coarse m + (1, 0)) := by
  cases m with
  | c j a =>
    have h := fine_le_coarse _ (qGenerator_c_mem_fine j a)
    rw [map_add, fineToCoarse_fine] at h
    show qGenerator (.c j a) ∈ _
    simpa [fineToCoarse] using h
  | b j a =>
    apply (gPiece _ _).smul_mem
    have h := fine_le_coarse _ (bbConv_mem_fine j a)
    convert h using 2
    simp [fineToCoarse, coarse, Mode.tdeg]

theorem iotaGen_mem_fine (e : Fin 3) (m : Mode) :
    iotaGen e m ∈ gPiece fine (fine m + (-1, -1, 0, 0)) := by
  unfold iotaGen
  split_ifs with h
  · subst h
    convert one_mem_gPiece fine using 2
    simp [fine, Mode.bCount, Mode.tcDeg, Mode.tbDeg]
  · exact (gPiece _ _).zero_mem

/-! ## Homogeneity of the operators -/

section Operators

variable {d : ℤ × ℤ × ℤ × ℤ} {u : Cochain}

theorem dC_mem_fine (hu : u ∈ gPiece fine d) : dC u ∈ gPiece fine (d + (1, 0, 0, 0)) :=
  extendDerivation_mem_gPiece fine dCGen _ dCGen_mem_fine hu

theorem dZ_mem_fine (hu : u ∈ gPiece fine d) : dZ u ∈ gPiece fine (d + (1, 1, 0, 0)) :=
  extendDerivation_mem_gPiece fine dZGen _ dZGen_mem_fine hu

theorem dG_mem_fine (hu : u ∈ gPiece fine d) : dG u ∈ gPiece fine (d + (1, 1, 0, 0)) :=
  extendDerivation_mem_gPiece fine dGGen _ dGGen_mem_fine hu

theorem iota_mem_fine (e : Fin 3) (hu : u ∈ gPiece fine d) :
    iota e u ∈ gPiece fine (d + (-1, -1, 0, 0)) :=
  extendDerivation_mem_gPiece fine (iotaGen e) _ (iotaGen_mem_fine e) hu

theorem colorActionOn_mem_fine (P : Mode → Bool) (e : Fin 3) (hu : u ∈ gPiece fine d) :
    colorActionOn P e u ∈ gPiece fine d := by
  have := extendDerivation_mem_gPiece fine (fun m => if P m then colorGenerator e m else 0) 0
    (fun m => by
      simp only [add_zero]
      split_ifs
      · exact colorGenerator_mem_fine e m
      · exact (gPiece _ _).zero_mem) hu
  rw [add_zero] at this
  exact this

theorem colorAction_mem_fine (e : Fin 3) (hu : u ∈ gPiece fine d) :
    colorAction e u ∈ gPiece fine d := colorActionOn_mem_fine (fun _ => true) e hu

end Operators

section CoarseOperators

variable {d : ℤ × ℤ} {u : Cochain}

theorem coarse_of_fine {f : Mode → Cochain} {δ : ℤ × ℤ × ℤ × ℤ}
    (hf : ∀ m, f m ∈ gPiece fine (fine m + δ)) (m : Mode) :
    f m ∈ gPiece coarse (coarse m + fineToCoarse δ) := by
  have h := fine_le_coarse _ (hf m)
  rwa [map_add, fineToCoarse_fine] at h

theorem dpp_mem_coarse (hu : u ∈ gPiece coarse d) : dpp u ∈ gPiece coarse (d + (1, 0)) :=
  extendDerivation_mem_gPiece coarse dppGen _ dppGen_mem_coarse hu

theorem dC_mem_coarse (hu : u ∈ gPiece coarse d) : dC u ∈ gPiece coarse (d + (1, 0)) :=
  extendDerivation_mem_gPiece coarse dCGen _ (coarse_of_fine dCGen_mem_fine) hu

theorem dZ_mem_coarse (hu : u ∈ gPiece coarse d) : dZ u ∈ gPiece coarse (d + (1, 0)) := by
  show extendDerivation dZGen u ∈ _
  have := extendDerivation_mem_gPiece coarse dZGen _ (coarse_of_fine dZGen_mem_fine) hu
  simpa [fineToCoarse] using this

theorem dG_mem_coarse (hu : u ∈ gPiece coarse d) : dG u ∈ gPiece coarse (d + (1, 0)) := by
  show extendDerivation dGGen u ∈ _
  have := extendDerivation_mem_gPiece coarse dGGen _ (coarse_of_fine dGGen_mem_fine) hu
  simpa [fineToCoarse] using this

theorem iota_mem_coarse (e : Fin 3) (hu : u ∈ gPiece coarse d) :
    iota e u ∈ gPiece coarse (d + (-1, 0)) := by
  show extendDerivation (iotaGen e) u ∈ _
  have := extendDerivation_mem_gPiece coarse (iotaGen e) _
    (coarse_of_fine (iotaGen_mem_fine e)) hu
  simpa [fineToCoarse] using this

theorem colorActionOn_mem_coarse (P : Mode → Bool) (e : Fin 3) (hu : u ∈ gPiece coarse d) :
    colorActionOn P e u ∈ gPiece coarse d := by
  have := extendDerivation_mem_gPiece coarse (fun m => if P m then colorGenerator e m else 0) 0
    (fun m => by
      simp only [add_zero]
      split_ifs
      · have h := coarse_of_fine (δ := 0) (fun m => by simpa using colorGenerator_mem_fine e m) m
        rwa [map_zero, add_zero] at h
      · exact (gPiece _ _).zero_mem) hu
  rw [add_zero] at this
  exact this

theorem colorAction_mem_coarse (e : Fin 3) (hu : u ∈ gPiece coarse d) :
    colorAction e u ∈ gPiece coarse d := colorActionOn_mem_coarse (fun _ => true) e hu

theorem swap_mem_coarse (hu : u ∈ gPiece coarse d) : swap u ∈ gPiece coarse d :=
  algHom_mem_gPiece coarse swap (fun m => by
    rw [swap_generator]
    cases m with
    | c j a =>
      show generator (.b (j + 1) a) ∈ _
      convert generator_mem_gPiece coarse (.b (j + 1) a) using 2
      simp [coarse, Mode.tdeg]
    | b j a =>
      cases j with
      | zero => exact generator_mem_gPiece coarse _
      | succ j =>
        show generator (.c j a) ∈ _
        convert generator_mem_gPiece coarse (.c j a) using 2
        simp [coarse, Mode.tdeg]) hu

end CoarseOperators

end KhanSL2
