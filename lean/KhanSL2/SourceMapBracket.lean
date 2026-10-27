module

public import KhanSL2.SourcePVA
public import KhanSL2.SourceGeneration
public import KhanSL2.PVAMap

@[expose] public section

/-! Bracket preservation for a graded differential algebra map out of the source
can be checked on the two generating fields. -/

noncomputable section
namespace KhanSL2
open LambdaPolynomial

variable {A : Type*} [AddCommGroup A] [Module ℂ A]

structure SourceMap (D : DifferentialData A) where
  linear : Source →ₗ[ℂ] A
  map_one : linear 1 = D.one
  map_mul : ∀ a b, linear (a * b) = D.mul (linear a) (linear b)
  map_translation : ∀ a, linear (Source.translation a) = D.translation (linear a)
  map_degree : ∀ d a, a ∈ Source.piece d → linear a ∈ D.piece d

namespace SourceMap
variable {D : DifferentialData A} {br : LambdaBracket A}
  (f : SourceMap D) (hP : IsPVA D br)

def BracketAt (a b : Source) : Prop :=
  coefficientMap f.linear (Source.bracket a b) = br (f.linear a) (f.linear b)

theorem map_mulRight (p : LambdaPolynomial Source) (b : Source) :
    coefficientMap f.linear (p.mulRight sourceData b) =
      mulRight D (coefficientMap f.linear p) (f.linear b) := by
  ext n
  simpa only [coefficientMap_apply, mulRight_apply, sourceData, LinearMap.mul_apply']
    using f.map_mul (p n) b

theorem map_mulLeft (a : Source) (p : LambdaPolynomial Source) :
    coefficientMap f.linear (p.mulLeft sourceData a) =
      mulLeft D (f.linear a) (coefficientMap f.linear p) := by
  ext n
  simpa only [coefficientMap_apply, mulLeft_apply, sourceData, LinearMap.mul_apply']
    using f.map_mul a (p n)

private theorem bracket_one {B : Type*} [AddCommGroup B] [Module ℂ B]
    {DB : DifferentialData B} {bb : LambdaBracket B} (hB : IsPVA DB bb)
    {d : Degree} {a : B} (ha : a ∈ DB.piece d) : bb a DB.one = 0 := by
  have h := hB.super_leibniz d 0 a DB.one DB.one ha hB.algebra.one_degree
  rw [hB.algebra.one_mul] at h
  ext n
  have hn := congrArg (fun p : LambdaPolynomial B => p n) h
  simp only [Finsupp.add_apply, Finsupp.smul_apply, mulRight_apply, mulLeft_apply,
    hB.algebra.one_mul, hB.algebra.mul_one, koszulSign, mul_zero, Int.zero_emod,
    if_true, one_smul] at hn
  have hh : bb a DB.one n + bb a DB.one n = bb a DB.one n + 0 := by
    simpa using hn.symm
  exact add_left_cancel hh

include hP in
theorem bracketAt_swap {d e : Degree} {a b : Source}
    (ha : a ∈ Source.piece d) (hb : b ∈ Source.piece e)
    (h : f.BracketAt (br := br) b a) : f.BracketAt (br := br) a b := by
  unfold BracketAt at h ⊢
  rw [source_isPVA.super_skew d e a b ha hb, map_smul,
    coefficientMap_skew f.linear sourceData.translation D.translation f.map_translation,
    h, hP.super_skew d e _ _ (f.map_degree _ _ ha) (f.map_degree _ _ hb)]

include hP in
theorem bracketAt_right {d : Degree} {a : Source} (ha : a ∈ Source.piece d)
    (hx : f.BracketAt (br := br) a (Source.X 0))
    (hy : f.BracketAt (br := br) a (Source.Y 0))
    {e : Degree} {b : Source} (hb : b ∈ Source.piece e) :
    f.BracketAt (br := br) a b := by
  have hi : b ∈ Source.piece e ∧ f.BracketAt (br := br) a b := by
    apply Source.homogeneous_induction (P := fun e b =>
      b ∈ Source.piece e ∧ f.BracketAt (br := br) a b) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hb
    · intro e
      exact ⟨(Source.piece e).zero_mem, by simp [BracketAt]⟩
    · intro r
      refine ⟨⟨.ofScalar r, .scalar r, rfl⟩, ?_⟩
      have hs := bracket_one source_isPVA ha
      have ht := bracket_one hP (f.map_degree _ _ ha)
      simp only [BracketAt, Algebra.algebraMap_eq_smul_one, map_smul,
        f.map_one]
      change r • coefficientMap f.linear (Source.bracket a sourceData.one) = _
      rw [hs, map_zero, smul_zero, ht, smul_zero]
    · exact ⟨Source.X_mem 0, hx⟩
    · exact ⟨Source.Y_mem 0, hy⟩
    · intro e b c hb hc
      refine ⟨(Source.piece e).add_mem hb.1 hc.1, ?_⟩
      simpa only [BracketAt, map_add] using congrArg₂ (· + ·) hb.2 hc.2
    · intro e k b c hb hc
      refine ⟨Source.mul_mem hb.1 hc.1, ?_⟩
      change coefficientMap f.linear (Source.bracket a (sourceData.mul b c)) = _
      rw [source_isPVA.super_leibniz d e a b c ha hb.1,
        map_add, map_smul, f.map_mulRight, f.map_mulLeft, hb.2, hc.2,
        f.map_mul, hP.super_leibniz d e _ _ _ (f.map_degree _ _ ha)
          (f.map_degree _ _ hb.1)]
    · intro e b hb
      refine ⟨Source.translation_mem hb.1, ?_⟩
      change coefficientMap f.linear (Source.bracket a (sourceData.translation b)) = _
      rw [source_isPVA.sesquilinear_right, map_add,
        coefficientMap_mapCoefficients f.linear sourceData.translation D.translation
          f.map_translation, coefficientMap_shift, hb.2,
        f.map_translation, hP.sesquilinear_right]
  exact hi.2

include hP in
theorem bracketAt_homogeneous
    (hxx : f.BracketAt (br := br) (Source.X 0) (Source.X 0))
    (hxy : f.BracketAt (br := br) (Source.X 0) (Source.Y 0))
    (hyy : f.BracketAt (br := br) (Source.Y 0) (Source.Y 0))
    {d e : Degree} {a b : Source} (ha : a ∈ Source.piece d)
    (hb : b ∈ Source.piece e) : f.BracketAt (br := br) a b := by
  have hyx := f.bracketAt_swap hP (Source.Y_mem 0) (Source.X_mem 0) hxy
  apply f.bracketAt_right hP ha
  · apply f.bracketAt_swap hP ha (Source.X_mem 0)
    exact f.bracketAt_right hP (Source.X_mem 0) hxx hxy ha
  · apply f.bracketAt_swap hP ha (Source.Y_mem 0)
    exact f.bracketAt_right hP (Source.Y_mem 0) hyx hyy ha
  · exact hb

include hP in
theorem bracketAt_all
    (hxx : f.BracketAt (br := br) (Source.X 0) (Source.X 0))
    (hxy : f.BracketAt (br := br) (Source.X 0) (Source.Y 0))
    (hyy : f.BracketAt (br := br) (Source.Y 0) (Source.Y 0))
    (a b : Source) : f.BracketAt (br := br) a b := by
  have ha : a ∈ ⨆ d, Source.piece d := by rw [Source.piece_iSup_eq_top]; trivial
  have hb : b ∈ ⨆ d, Source.piece d := by rw [Source.piece_iSup_eq_top]; trivial
  refine Submodule.iSup_induction Source.piece (motive := fun a =>
    f.BracketAt (br := br) a b) ha ?_ ?_ ?_
  · intro d a ha
    refine Submodule.iSup_induction Source.piece (motive := fun b =>
      f.BracketAt (br := br) a b) hb ?_ ?_ ?_
    · intro e b hb
      exact f.bracketAt_homogeneous hP hxx hxy hyy ha hb
    · simp [BracketAt]
    · intro b c hb hc
      simpa only [BracketAt, map_add] using congrArg₂ (· + ·) hb hc
  · simp [BracketAt]
  · intro a c ha hc
    simpa only [BracketAt, map_add, LinearMap.add_apply] using congrArg₂ (· + ·) ha hc

end SourceMap
end KhanSL2
