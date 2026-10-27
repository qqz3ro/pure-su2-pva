module

public import KhanSL2.BCModeKernel
public import KhanSL2.CEExterior
public import KhanSL2.ExteriorDerivation
public import KhanSL2.BasisGrading

@[expose] public section

/-!
# Adjoining the three missing zero modes

The new generators are placed before all existing generators in the exterior
ordering. Consequently the inclusion of the original cochains preserves their
ordered-monomial basis without a permutation sign.
-/

noncomputable section

namespace KhanSL2

abbrev FullMode := (Fin 3) ⊕ Mode

namespace FullMode

def code : FullMode → ℕ
  | .inl a => a.val
  | .inr m => m.code + 3

def color : FullMode → Fin 3
  | .inl a => a
  | .inr m => m.color

def recolor (a : Fin 3) : FullMode → FullMode
  | .inl _ => .inl a
  | .inr m => .inr (m.recolor a)

def bCount : FullMode → ℕ
  | .inl _ => 0
  | .inr m => m.bCount

def weight : FullMode → ℕ
  | .inl _ => 0
  | .inr m => m.weight

def order : FullMode → ℕ
  | .inl _ => 0
  | .inr m => m.order

def next : FullMode → FullMode
  | .inl a => .inr (.c 0 a)
  | .inr m => .inr m.next

def translationCoefficient (m : FullMode) : ℕ := m.order + 1

def pairsWith : FullMode → FullMode → Prop
  | .inl a, .inr (.b _ d) => a = d
  | .inr (.b _ a), .inl d => a = d
  | .inr m, .inr n => m.pairsWith n
  | _, _ => False

@[simp] theorem pairsWith_inr (m n : Mode) :
    pairsWith (.inr m) (.inr n) ↔ m.pairsWith n := by
  cases m <;> cases n <;> rfl

instance (m n : FullMode) : Decidable (pairsWith m n) := by
  cases m with
  | inl a => cases n with
    | inl b => simp only [pairsWith]; infer_instance
    | inr n => cases n <;> unfold pairsWith <;> infer_instance
  | inr m => cases n with
    | inl b => cases m <;> unfold pairsWith <;> infer_instance
    | inr n =>
      rw [pairsWith_inr]
      infer_instance

theorem code_injective : Function.Injective code := by
  intro m n h
  cases m with
  | inl a => cases n with
    | inl b =>
      have hab : a = b := Fin.ext h
      exact congrArg Sum.inl hab
    | inr n =>
      simp only [code] at h
      omega
  | inr m => cases n with
    | inl b =>
      simp only [code] at h
      omega
    | inr n =>
      have hmn : m = n := Mode.code_injective (Nat.add_right_cancel h)
      exact congrArg Sum.inr hmn

theorem code_inr_lt (m n : Mode) :
    code (.inr m) < code (.inr n) ↔ m.code < n.code := by
  simp [code]

@[simp] theorem order_next (m : FullMode) :
    m.next.order = m.order + 1 := by
  cases m with
  | inl a => rfl
  | inr m => exact Mode.order_next m

@[simp] theorem bCount_next (m : FullMode) :
    m.next.bCount = m.bCount := by
  cases m with
  | inl a => rfl
  | inr m => cases m <;> rfl

@[simp] theorem weight_next (m : FullMode) :
    m.next.weight = m.weight + 1 := by
  cases m with
  | inl a => rfl
  | inr m => cases m <;> rfl

theorem pairsWith_comm (m n : FullMode) :
    m.pairsWith n ↔ n.pairsWith m := by
  cases m with
  | inl a => cases n with
    | inl b => rfl
    | inr n => cases n <;> simp [pairsWith, eq_comm]
  | inr m => cases n with
    | inl b => cases m <;> simp [pairsWith, eq_comm]
    | inr n => simpa using Mode.pairsWith_comm m n

@[simp] theorem next_pairsWith (m n : FullMode) :
    m.next.pairsWith n ↔ m.pairsWith n := by
  cases m with
  | inl a => cases n with
    | inl b => rfl
    | inr n => cases n <;> simp [next, pairsWith, Mode.pairsWith]
  | inr m => cases n with
    | inl b => cases m <;> simp [next, pairsWith, Mode.next]
    | inr n => simp [next]

@[simp] theorem pairsWith_next (m n : FullMode) :
    m.pairsWith n.next ↔ m.pairsWith n := by
  rw [pairsWith_comm, next_pairsWith, pairsWith_comm]

theorem pairsWith_bCount (m n : FullMode) (h : m.pairsWith n) :
    m.bCount + n.bCount = 1 := by
  cases m with
  | inl a => cases n with
    | inl b => exact False.elim h
    | inr n => cases n <;> simp_all [pairsWith, bCount, Mode.bCount]
  | inr m => cases n with
    | inl b => cases m <;> simp_all [pairsWith, bCount, Mode.bCount]
    | inr n => exact Mode.pairsWith_bCount m n ((pairsWith_inr m n).mp h)

theorem pairsWith_weight (m n : FullMode) (h : m.pairsWith n) :
    m.weight + n.weight = m.order + n.order + 1 := by
  cases m with
  | inl a => cases n with
    | inl b => exact False.elim h
    | inr n => cases n <;> simp_all [pairsWith, weight, order, Mode.weight, Mode.order]
  | inr m => cases n with
    | inl b => cases m <;> simp_all [pairsWith, weight, order, Mode.weight, Mode.order]
    | inr n => exact Mode.pairsWith_weight m n ((pairsWith_inr m n).mp h)

end FullMode

instance : FiniteExterior.GeneratorOrder FullMode where
  code := FullMode.code
  code_injective := FullMode.code_injective

abbrev FullExteriorMonomial := Finset FullMode
abbrev FullCochain := FullExteriorMonomial →₀ ℂ

def fullGenerator (m : FullMode) : FullCochain := FiniteExterior.generator m
def fullWedge := FiniteExterior.wedge FullMode.code
def fullWedgeLinear := FiniteExterior.wedgeLinear FullMode.code
def fullOne : FullCochain := FiniteExterior.monomial ∅
def ghost (a : Fin 3) : FullCochain := fullGenerator (.inl a)

def fullParity : FullCochain →ₐ[ℂ] FullCochain := FiniteExterior.parity

def fullTranslationGenerator (m : FullMode) : FullCochain :=
  (m.translationCoefficient : ℂ) • fullGenerator m.next

def fullTranslation : Module.End ℂ FullCochain :=
  FiniteExterior.extendDerivation FullMode.code fullTranslationGenerator

def fullColorGenerator (a : Fin 3) (m : FullMode) : FullCochain :=
  ∑ c : Fin 3, epsilon a m.color c • fullGenerator (m.recolor c)

def fullColorAction (a : Fin 3) : Module.End ℂ FullCochain :=
  FiniteExterior.extendDerivation FullMode.code (fullColorGenerator a)

def fullMonomialDegree (s : FullExteriorMonomial) : Degree :=
  (s.card, (∑ m ∈ s, m.bCount : ℕ), (∑ m ∈ s, m.weight : ℕ))

def fullPiece (d : Degree) : Submodule ℂ FullCochain :=
  BasisGrading.piece fullMonomialDegree d

def fullData : DifferentialData FullCochain where
  one := fullOne
  mul := fullWedgeLinear
  translation := fullTranslation
  piece := fullPiece

end KhanSL2
