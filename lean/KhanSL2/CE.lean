module

public import KhanSL2.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
# Restricted relative Chevalley–Eilenberg cochains

The exterior monomials are finite sets of generators, and a cochain is a
finitely supported complex linear combination of those monomials.
Thus no completed or unrestricted dual is involved.

`Mode.c j a` denotes the paper's `c_(j+1)^a`. This predecessor convention
avoids both an unused zero mode and subtraction in the type of a generator.
The arithmetic code puts `b_j^0,b_j^1,b_j^2,c_(j+1)^0,c_(j+1)^1,c_(j+1)^2`
in this order for each `j`.

All operations below are concrete finite formulas. Their structural
identities are proved in `CEComplex`, `BCPVA`, and `TargetPVA`.
-/

noncomputable section

namespace KhanSL2

inductive Mode
  | b : ℕ → Fin 3 → Mode
  | c : ℕ → Fin 3 → Mode
  deriving DecidableEq

namespace Mode

def code : Mode → ℕ
  | b j a => 6 * j + a.val
  | c j a => 6 * j + 3 + a.val

def bCount : Mode → ℕ
  | b _ _ => 1
  | c _ _ => 0

def weight : Mode → ℕ
  | b j _ => j + 1
  | c j _ => j + 1

def color : Mode → Fin 3
  | b _ a => a
  | c _ a => a

def recolor (a : Fin 3) : Mode → Mode
  | b j _ => b j a
  | c j _ => c j a

def next : Mode → Mode
  | b j a => b (j + 1) a
  | c j a => c (j + 1) a

/-- The normalized translation coefficient. -/
def translationCoefficient : Mode → ℕ
  | b j _ => j + 1
  | c j _ => j + 2

end Mode

abbrev ExteriorMonomial := Finset Mode
abbrev Cochain := ExteriorMonomial →₀ ℂ

def cochainOne : Cochain := Finsupp.single ∅ 1

def generator (m : Mode) : Cochain := Finsupp.single {m} 1

def inversionCount (s t : ExteriorMonomial) : ℕ :=
  ∑ a ∈ s, (t.filter fun b => b.code < a.code).card

def monomialWedge (s t : ExteriorMonomial) : Cochain :=
  if Disjoint s t then
    Finsupp.single (s ∪ t) ((-1 : ℂ) ^ inversionCount s t)
  else 0

/-- Exterior multiplication, with the sign from ordering the generators. -/
def wedgeLinear : Cochain →ₗ[ℂ] Cochain →ₗ[ℂ] Cochain :=
  Finsupp.linearCombination ℂ fun s =>
    Finsupp.linearCombination ℂ (monomialWedge s)

def wedge (u v : Cochain) : Cochain := wedgeLinear u v

def epsilon (a b c : Fin 3) : ℂ :=
  if (a.val = 0 ∧ b.val = 1 ∧ c.val = 2) ∨
      (a.val = 1 ∧ b.val = 2 ∧ c.val = 0) ∨
      (a.val = 2 ∧ b.val = 0 ∧ c.val = 1) then 1
  else if (a.val = 0 ∧ b.val = 2 ∧ c.val = 1) ∨
      (a.val = 2 ∧ b.val = 1 ∧ c.val = 0) ∨
      (a.val = 1 ∧ b.val = 0 ∧ c.val = 2) then -1
  else 0

/-- Number of earlier factors in the ordered exterior monomial. -/
def position (m : Mode) (s : ExteriorMonomial) : ℕ :=
  (s.filter fun a => a.code < m.code).card

/-- Extend generator values by the graded Leibniz rule.

The image of the selected factor is placed first; the displayed sign
accounts for this convention for either parity of a derivation.
-/
def extendDerivation (f : Mode → Cochain) : Cochain →ₗ[ℂ] Cochain :=
  Finsupp.linearCombination ℂ fun s =>
    ∑ m ∈ s, ((-1 : ℂ) ^ position m s) •
      wedge (f m) (Finsupp.single (s.erase m) 1)

/-- The relative CE differential on generators. -/
def qGenerator : Mode → Cochain
  | .c j a =>
    (- (1 / 2 : ℂ)) •
      ∑ i ∈ Finset.range j, ∑ b : Fin 3, ∑ c : Fin 3,
        epsilon a b c • wedge (generator (.c i b))
          (generator (.c (j - 1 - i) c))
  | .b j a =>
    - ∑ i ∈ Finset.range j, ∑ b : Fin 3, ∑ c : Fin 3,
        epsilon a b c • wedge (generator (.c i b))
          (generator (.b (j - 1 - i) c))

def q : Cochain →ₗ[ℂ] Cochain := extendDerivation qGenerator

/-- Infinitesimal action of a constant color generator. -/
def colorGenerator (a : Fin 3) (m : Mode) : Cochain :=
  ∑ c : Fin 3, epsilon a m.color c • generator (m.recolor c)

def colorAction (a : Fin 3) : Cochain →ₗ[ℂ] Cochain :=
  extendDerivation (colorGenerator a)

def translationGenerator (m : Mode) : Cochain :=
  (m.translationCoefficient : ℂ) • generator m.next

def translation : Cochain →ₗ[ℂ] Cochain :=
  extendDerivation translationGenerator

def relativeInvariants : Submodule ℂ Cochain :=
  ⨅ a : Fin 3, LinearMap.ker (colorAction a)

def relativeCycles : Submodule ℂ Cochain :=
  relativeInvariants ⊓ LinearMap.ker q

/-- Boundaries as a subspace of the cycle space.

The intersection is built into `comap`, so this definition itself needs no
unproved assertion that the CE differential squares to zero. Square-zero
and preservation of invariants are proved in `CEComplex`. Under those
identities, this is exactly the usual relative CE cycles-modulo-boundaries
quotient.
-/
def relativeBoundaries : Submodule ℂ relativeCycles :=
  (relativeInvariants.map q).comap relativeCycles.subtype

abbrev CycleSpace := ↥relativeCycles

instance : AddCommGroup CycleSpace := relativeCycles.addCommGroup
instance : Module ℂ CycleSpace := relativeCycles.module

abbrev Cohomology := CycleSpace ⧸ relativeBoundaries

def classOf (u : Cochain) (hu : u ∈ relativeCycles) : Cohomology :=
  Submodule.Quotient.mk ⟨u, hu⟩

def xRepresentative : Cochain :=
  - ∑ a : Fin 3, wedge (generator (.b 0 a)) (generator (.c 0 a))

def yRepresentative : Cochain :=
  wedge (wedge (generator (.b 0 0)) (generator (.b 0 1)))
    (generator (.b 0 2))

def monomialDegree (s : ExteriorMonomial) : Degree :=
  (s.card, (∑ m ∈ s, m.bCount : ℕ), (∑ m ∈ s, m.weight : ℕ))

def cochainHomogeneous (d : Degree) (u : Cochain) : Prop :=
  ∀ s ∈ u.support, monomialDegree s = d

def cochainPiece (d : Degree) : Submodule ℂ Cochain :=
  Finsupp.supported ℂ ℂ {s | monomialDegree s = d}

def cohomologyPiece (d : Degree) : Submodule ℂ Cohomology :=
  ((cochainPiece d).comap relativeCycles.subtype).map relativeBoundaries.mkQ

def cohomologyHomogeneous (d : Degree) (h : Cohomology) : Prop :=
  ∃ u, ∃ hu : u ∈ relativeCycles, cochainHomogeneous d u ∧ classOf u hu = h

@[simp]
theorem qGenerator_b_zero (a : Fin 3) : qGenerator (.b 0 a) = 0 := by
  simp [qGenerator]

@[simp]
theorem qGenerator_c_zero (a : Fin 3) : qGenerator (.c 0 a) = 0 := by
  simp [qGenerator]

end KhanSL2
