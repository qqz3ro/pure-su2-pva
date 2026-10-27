module

public import KhanSL2.SourceUniversal
public import KhanSL2.SourceMapBracket
public import KhanSL2.CanonicalBoundaryDescent
public import KhanSL2.CanonicalBracket
public import KhanSL2.CanonicalVanish

@[expose] public section

/-!
# The specified canonical morphism

`phi` is an explicitly evaluated map on the source quotient. Its definition
uses proved invariant CE boundaries for the relations; it does not depend
on the main isomorphism proposition. All PVA morphism laws are proved here.
-/

noncomputable section
namespace KhanSL2

/-- The prescribed images, with proofs of every defining relation. -/
def canonicalImages : SourceGeneratorImages targetData where
  x := xClass
  y := yClass
  x_mem := xClass_degree
  y_mem := yClass_degree
  x_sq := CanonicalRelations.xClass_sq
  xy := CanonicalVanish.xClass_yClass
  x_ty := CanonicalRelations.xClass_translation_yClass
  y_ty := CanonicalVanish.yClass_translation_yClass

/-- Evaluate a finite source expression by `X_i ↦ T^i xClass` and
`Y_i ↦ T^i yClass`, using the target unit and multiplication. -/
def phiExpression : SourcePresentation.Expression → Cohomology := canonicalImages.eval

/-- Every relation in the differential source presentation evaluates equally.
This includes algebra laws, supercommutativity, the four relations, their
derivatives, and closure under addition and multiplication. -/
theorem phi_well_defined {a b : SourcePresentation.Expression}
    (h : SourcePresentation.Relation a b) : phiExpression a = phiExpression b :=
  canonicalImages.eval_relation target_isPVA.algebra h

/-- The canonical map, constructed by evaluation and quotient descent. -/
def phi : Source →ₗ[ℂ] Cohomology := canonicalImages.lift target_isPVA.algebra

@[simp] theorem phi_mk (e : SourcePresentation.Expression) :
    phi (Source.mk e) = phiExpression e := rfl

@[simp] theorem phi_X (i : ℕ) : phi (Source.X i) = (targetData.translation ^ i) xClass := rfl
@[simp] theorem phi_Y (i : ℕ) : phi (Source.Y i) = (targetData.translation ^ i) yClass := rfl
@[simp] theorem phi_X0 : phi (Source.X 0) = xClass := rfl
@[simp] theorem phi_Y0 : phi (Source.Y 0) = yClass := rfl

@[simp] theorem phi_one : phi 1 = targetData.one := canonicalImages.lift_one target_isPVA.algebra

theorem phi_mul (a b : Source) :
    phi (a * b) = targetData.mul (phi a) (phi b) :=
  canonicalImages.lift_mul target_isPVA.algebra a b

theorem phi_translation (a : Source) :
    phi (Source.translation a) = targetData.translation (phi a) :=
  canonicalImages.lift_translation target_isPVA.algebra a

theorem phi_degree {d : Degree} {a : Source} (ha : a ∈ Source.piece d) :
    phi a ∈ targetData.piece d := canonicalImages.lift_degree target_isPVA.algebra ha

/-- The explicit map, bundled with its differential algebra and grading laws. -/
def phiSourceMap : SourceMap targetData where
  linear := phi
  map_one := phi_one
  map_mul := phi_mul
  map_translation := phi_translation
  map_degree _ _ := phi_degree

theorem phi_bracket (a b : Source) (n : ℕ) :
    phi (Source.bracket a b n) = targetBracket (phi a) (phi b) n := by
  have hxx : phiSourceMap.BracketAt (br := targetBracket) (Source.X 0) (Source.X 0) := by
    change coefficientMap phi (Source.bracket (Source.X 0) (Source.X 0)) = _
    rw [Source.bracket_generator_formulas.xx]
    simp [phiSourceMap, CanonicalBracket.target_x_x]
  have hxy : phiSourceMap.BracketAt (br := targetBracket) (Source.X 0) (Source.Y 0) := by
    change coefficientMap phi (Source.bracket (Source.X 0) (Source.Y 0)) = _
    rw [Source.bracket_generator_formulas.xy]
    simp [phiSourceMap, CanonicalBracket.target_x_y]
  have hyy : phiSourceMap.BracketAt (br := targetBracket) (Source.Y 0) (Source.Y 0) := by
    change coefficientMap phi (Source.bracket (Source.Y 0) (Source.Y 0)) = _
    rw [Source.bracket_generator_formulas.yy]
    simp [phiSourceMap, CanonicalBracket.target_y_y]
  exact congrArg (fun p : LambdaPolynomial Cohomology => p n)
    (phiSourceMap.bracketAt_all target_isPVA hxx hxy hyy a b)

/-- The actual canonical PVA morphism, independent of its proposed bijectivity. -/
def phiPVAMap : PVAMap sourceData Source.bracket targetData targetBracket where
  linear := phi
  map_one := phi_one
  map_mul := phi_mul
  map_translation := phi_translation
  map_bracket := phi_bracket

/-- Any unital differential algebra map with the prescribed generator images
equals the constructed map. No bijectivity or bracket hypothesis is used. -/
theorem phi_unique (f : Source →ₗ[ℂ] Cohomology)
    (h1 : f 1 = targetData.one)
    (hm : ∀ a b, f (a * b) = targetData.mul (f a) (f b))
    (hT : ∀ a, f (Source.translation a) = targetData.translation (f a))
    (hx : f (Source.X 0) = xClass) (hy : f (Source.Y 0) = yClass) : f = phi :=
  canonicalImages.lift_unique target_isPVA.algebra f h1 hm hT hx hy

end KhanSL2
