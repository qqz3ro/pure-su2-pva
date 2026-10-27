module

public import KhanSL2.PVAMap

@[expose] public section

/-! PVA laws pass to subalgebras and homogeneous quotients by actual maps
preserving all operations. The direct-sum grading is supplied separately. -/

noncomputable section

namespace KhanSL2.PVAMap

variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]
  {DA : DifferentialData A} {brA : LambdaBracket A}
  {DB : DifferentialData B} {brB : LambdaBracket B}
  (f : PVAMap DA brA DB brB)

theorem algebra_of_injective
    (hf : Function.Injective f.linear)
    (hg : ∀ d a, f.linear a ∈ DB.piece d ↔ a ∈ DA.piece d)
    (hi : DirectSum.IsInternal DA.piece)
    (hB : IsGradedDifferentialSuperalgebra B DB) :
    IsGradedDifferentialSuperalgebra A DA where
  grading_internal := hi
  one_mul a := by
    apply hf
    rw [f.map_mul, f.map_one, hB.one_mul]
  mul_one a := by
    apply hf
    rw [f.map_mul, f.map_one, hB.mul_one]
  mul_assoc a b c := by
    apply hf
    simp only [f.map_mul, hB.mul_assoc]
  supercomm d e a b ha hb := by
    apply hf
    rw [f.map_mul, map_smul, f.map_mul]
    exact hB.supercomm d e _ _ ((hg d a).mpr ha) ((hg e b).mpr hb)
  one_degree := (hg _ _).mp (by rw [f.map_one]; exact hB.one_degree)
  mul_degree d e a b ha hb := (hg _ _).mp (by
    rw [f.map_mul]
    exact hB.mul_degree _ _ _ _ ((hg _ _).mpr ha) ((hg _ _).mpr hb))
  translation_degree d a ha := (hg _ _).mp (by
    rw [f.map_translation]
    exact hB.translation_degree _ _ ((hg _ _).mpr ha))
  translation_one := by
    apply hf
    rw [f.map_translation, f.map_one, map_zero, hB.translation_one]
  translation_mul a b := by
    apply hf
    simp only [f.map_translation, f.map_mul, map_add, hB.translation_mul]

theorem algebra_of_surjective
    (hf : Function.Surjective f.linear)
    (hg : ∀ d, DB.piece d = (DA.piece d).map f.linear)
    (hi : DirectSum.IsInternal DB.piece)
    (hA : IsGradedDifferentialSuperalgebra A DA) :
    IsGradedDifferentialSuperalgebra B DB where
  grading_internal := hi
  one_mul b := by
    obtain ⟨a, rfl⟩ := hf b
    rw [← f.map_one, ← f.map_mul, hA.one_mul]
  mul_one b := by
    obtain ⟨a, rfl⟩ := hf b
    rw [← f.map_one, ← f.map_mul, hA.mul_one]
  mul_assoc a b c := by
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    obtain ⟨c, rfl⟩ := hf c
    simp only [← f.map_mul, hA.mul_assoc]
  supercomm d e a b ha hb := by
    rw [hg] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    rw [← f.map_mul, hA.supercomm d e _ _ ha hb, map_smul, f.map_mul]
  one_degree := by
    rw [hg, ← f.map_one]
    exact ⟨DA.one, hA.one_degree, rfl⟩
  mul_degree d e a b ha hb := by
    rw [hg] at ha hb ⊢
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    exact ⟨DA.mul a b, hA.mul_degree _ _ _ _ ha hb, f.map_mul a b⟩
  translation_degree d a ha := by
    rw [hg] at ha ⊢
    obtain ⟨a, ha, rfl⟩ := ha
    exact ⟨DA.translation a, hA.translation_degree _ _ ha, f.map_translation a⟩
  translation_one := by
    rw [← f.map_one, ← f.map_translation, hA.translation_one, map_zero]
  translation_mul a b := by
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    simp only [← f.map_mul, ← f.map_translation, ← map_add, hA.translation_mul]

theorem pva_of_injective
    (hf : Function.Injective f.linear)
    (hg : ∀ d a, f.linear a ∈ DB.piece d ↔ a ∈ DA.piece d)
    (hi : DirectSum.IsInternal DA.piece)
    (hB : IsPVA DB brB) : IsPVA DA brA where
  algebra := f.algebra_of_injective hf hg hi hB.algebra
  sesquilinear_left a b := by
    apply coefficientMap_injective f.linear hf
    rw [map_neg, LambdaPolynomial.coefficientMap_shift, f.map_bracket_poly,
      f.map_bracket_poly, f.map_translation, hB.sesquilinear_left]
  sesquilinear_right a b := by
    apply coefficientMap_injective f.linear hf
    rw [map_add, LambdaPolynomial.coefficientMap_mapCoefficients f.linear
      DA.translation DB.translation f.map_translation,
      LambdaPolynomial.coefficientMap_shift, f.map_bracket_poly,
      f.map_bracket_poly, f.map_translation, hB.sesquilinear_right]
  super_skew d e a b ha hb := by
    apply coefficientMap_injective f.linear hf
    rw [map_smul, LambdaPolynomial.coefficientMap_skew f.linear
      DA.translation DB.translation f.map_translation, f.map_bracket_poly,
      f.map_bracket_poly]
    exact hB.super_skew d e _ _ ((hg d a).mpr ha) ((hg e b).mpr hb)
  super_jacobi d e a b c ha hb := by
    apply coefficientMap_injective f.linear hf
    rw [map_add, map_smul, f.map_jacobiLeft, f.map_jacobiMiddle, f.map_jacobiRight]
    exact hB.super_jacobi d e _ _ _ ((hg d a).mpr ha) ((hg e b).mpr hb)
  super_leibniz d e a b c ha hb := by
    apply coefficientMap_injective f.linear hf
    rw [map_add, map_smul, f.map_mulRight, f.map_mulLeft,
      f.map_bracket_poly, f.map_bracket_poly, f.map_bracket_poly, f.map_mul]
    exact hB.super_leibniz d e _ _ _ ((hg d a).mpr ha) ((hg e b).mpr hb)
  bracket_degree d e a b n ha hb := (hg _ _).mp (by
    rw [f.map_bracket]
    exact hB.bracket_degree d e _ _ n ((hg d a).mpr ha) ((hg e b).mpr hb))

theorem pva_of_surjective
    (hf : Function.Surjective f.linear)
    (hg : ∀ d, DB.piece d = (DA.piece d).map f.linear)
    (hi : DirectSum.IsInternal DB.piece)
    (hA : IsPVA DA brA) : IsPVA DB brB where
  algebra := f.algebra_of_surjective hf hg hi hA.algebra
  sesquilinear_left a b := by
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    simpa only [map_neg, f.map_bracket_poly, f.map_translation,
      LambdaPolynomial.coefficientMap_shift] using
      congrArg (coefficientMap f.linear) (hA.sesquilinear_left a b)
  sesquilinear_right a b := by
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    simpa only [map_add, f.map_bracket_poly, f.map_translation,
      LambdaPolynomial.coefficientMap_shift,
      LambdaPolynomial.coefficientMap_mapCoefficients f.linear
        DA.translation DB.translation f.map_translation] using
      congrArg (coefficientMap f.linear) (hA.sesquilinear_right a b)
  super_skew d e a b ha hb := by
    rw [hg] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    simpa only [map_smul, f.map_bracket_poly,
      LambdaPolynomial.coefficientMap_skew f.linear
        DA.translation DB.translation f.map_translation] using
      congrArg (coefficientMap f.linear) (hA.super_skew d e a b ha hb)
  super_jacobi d e a b c ha hb := by
    rw [hg] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    obtain ⟨c, rfl⟩ := hf c
    simpa only [map_add, map_smul, f.map_jacobiLeft, f.map_jacobiMiddle,
      f.map_jacobiRight] using
      congrArg (coefficientMap f.linear) (hA.super_jacobi d e a b c ha hb)
  super_leibniz d e a b c ha hb := by
    rw [hg] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    obtain ⟨c, rfl⟩ := hf c
    simpa only [map_add, map_smul, f.map_mulRight, f.map_mulLeft,
      f.map_bracket_poly, f.map_mul] using
      congrArg (coefficientMap f.linear) (hA.super_leibniz d e a b c ha hb)
  bracket_degree d e a b n ha hb := by
    rw [hg] at ha hb ⊢
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    exact ⟨brA a b n, hA.bracket_degree _ _ _ _ _ ha hb, f.map_bracket a b n⟩

end KhanSL2.PVAMap
