module

public import KhanSL2.SourceParity
public import KhanSL2.SourceData
public import KhanSL2.LambdaPolynomialLemmas

@[expose] public section

/-! # Polynomial Hamiltonian values on the source jets -/

noncomputable section

namespace KhanSL2.Source

open LambdaPolynomial

def jetSpan (g : ℕ → Source) : Submodule ℂ Source :=
  Submodule.span ℂ (Set.range g)

theorem mem_jetSpan (g : ℕ → Source) (i : ℕ) : g i ∈ jetSpan g :=
  Submodule.subset_span ⟨i, rfl⟩

theorem translation_jetSpan (g : ℕ → Source)
    (hg : ∀ i, translation (g i) = g (i + 1)) {a : Source}
    (ha : a ∈ jetSpan g) : translation a ∈ jetSpan g := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    rw [hg]
    exact mem_jetSpan g _
  | zero => simpa only [map_zero] using (jetSpan g).zero_mem
  | add a b ha hb ia ib => simpa only [map_add] using (jetSpan g).add_mem ia ib
  | smul r a ha ia => simpa only [map_smul] using (jetSpan g).smul_mem r ia

theorem jetSpan_commute (g : ℕ → Source) (b : Source) (s : ℂ)
    (hg : ∀ i, g i * b = s • (b * g i)) {a : Source} (ha : a ∈ jetSpan g) :
    a * b = s • (b * a) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    exact hg i
  | zero => simp
  | add a c _ _ ia ic => simp only [add_mul, mul_add, smul_add, ia, ic]
  | smul r a ha ia =>
    rw [smul_mul_assoc, ia, mul_smul_comm, smul_comm r s]

def jetPolynomialSpan (g : ℕ → Source) : Submodule ℂ (LambdaPolynomial Source) where
  carrier := {p | ∀ n, p n ∈ jetSpan g}
  zero_mem' _ := (jetSpan g).zero_mem
  add_mem' hp hq n := (jetSpan g).add_mem (hp n) (hq n)
  smul_mem' r _ hp n := (jetSpan g).smul_mem r (hp n)

theorem single_mem_jetPolynomialSpan (g : ℕ → Source) (n : ℕ)
    {a : Source} (ha : a ∈ jetSpan g) : Finsupp.single n a ∈ jetPolynomialSpan g := by
  intro k
  by_cases h : n = k
  · subst k
    simpa using ha
  · simp [Finsupp.single_apply, h]

theorem rightTranslation_jetPolynomialSpan (g : ℕ → Source)
    (hg : ∀ i, translation (g i) = g (i + 1))
    {p : LambdaPolynomial Source} (hp : p ∈ jetPolynomialSpan g) :
    rightTranslation translation p ∈ jetPolynomialSpan g := by
  intro n
  cases n with
  | zero =>
    simpa [rightTranslation_apply] using translation_jetSpan g hg (hp 0)
  | succ n =>
    simpa [rightTranslation_apply] using
      (jetSpan g).add_mem (translation_jetSpan g hg (hp (n + 1))) (hp n)

/-- Apply `(partial + lambda)^i` to `a partial g + b lambda g`. -/
def jetAction (g : ℕ → Source) (a b : ℂ) : ℕ → LambdaPolynomial Source
  | 0 => Finsupp.single 0 (a • g 1) + Finsupp.single 1 (b • g 0)
  | i + 1 => rightTranslation translation (jetAction g a b i)

@[simp] theorem jetAction_zero (g : ℕ → Source) (a b : ℂ) :
    jetAction g a b 0 =
      Finsupp.single 0 (a • g 1) + Finsupp.single 1 (b • g 0) := rfl

theorem jetAction_succ (g : ℕ → Source) (a b : ℂ) (i : ℕ) :
    jetAction g a b (i + 1) = rightTranslation translation (jetAction g a b i) := rfl

theorem jetAction_mem (g : ℕ → Source)
    (hg : ∀ i, translation (g i) = g (i + 1)) (a b : ℂ) (i : ℕ) :
    jetAction g a b i ∈ jetPolynomialSpan g := by
  induction i with
  | zero =>
    exact (jetPolynomialSpan g).add_mem
      (single_mem_jetPolynomialSpan g 0 ((jetSpan g).smul_mem a (mem_jetSpan g 1)))
      (single_mem_jetPolynomialSpan g 1 ((jetSpan g).smul_mem b (mem_jetSpan g 0)))
  | succ i hi => exact rightTranslation_jetPolynomialSpan g hg hi

/-- `{X_lambda partial^i X}`. -/
def XX (i : ℕ) : LambdaPolynomial Source := jetAction X 1 2 i

/-- `{X_lambda partial^i Y}`. -/
def XY (i : ℕ) : LambdaPolynomial Source := jetAction Y 1 3 i

/-- `{Y_lambda partial^i X}`. -/
def YX (i : ℕ) : LambdaPolynomial Source := jetAction Y 2 3 i

theorem XX_commute_X (i j n : ℕ) : XX i n * X j = X j * XX i n := by
  simpa only [XX, one_smul] using jetSpan_commute X (X j) 1
    (fun k => by simpa only [one_smul] using X_mul_X k j)
    (jetAction_mem X translation_X 1 2 i n)

theorem XX_commute_Y (i j n : ℕ) : XX i n * Y j = Y j * XX i n := by
  simpa only [XX, one_smul] using jetSpan_commute X (Y j) 1
    (fun k => by simpa only [one_smul] using X_mul_Y k j)
    (jetAction_mem X translation_X 1 2 i n)

theorem XY_commute_X (i j n : ℕ) : XY i n * X j = X j * XY i n := by
  simpa only [XY, YX, one_smul] using jetSpan_commute Y (X j) 1
    (fun k => by simpa only [one_smul] using (X_mul_Y j k).symm)
    (jetAction_mem Y translation_Y 1 3 i n)

theorem XY_anticommute_Y (i j n : ℕ) : XY i n * Y j = -(Y j * XY i n) := by
  simpa only [XY, YX, neg_one_smul] using jetSpan_commute Y (Y j) (-1)
    (fun k => by simpa only [neg_one_smul] using Y_mul_Y k j)
    (jetAction_mem Y translation_Y 1 3 i n)

theorem YX_commute_X (i j n : ℕ) : YX i n * X j = X j * YX i n := by
  simpa only [XY, YX, one_smul] using jetSpan_commute Y (X j) 1
    (fun k => by simpa only [one_smul] using (X_mul_Y j k).symm)
    (jetAction_mem Y translation_Y 2 3 i n)

theorem YX_anticommute_Y (i j n : ℕ) : YX i n * Y j = -(Y j * YX i n) := by
  simpa only [XY, YX, neg_one_smul] using jetSpan_commute Y (Y j) (-1)
    (fun k => by simpa only [neg_one_smul] using Y_mul_Y k j)
    (jetAction_mem Y translation_Y 2 3 i n)

end KhanSL2.Source
