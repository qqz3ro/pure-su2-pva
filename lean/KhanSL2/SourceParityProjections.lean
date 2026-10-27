module

public import KhanSL2.SourceParity
public import Mathlib.Tactic.Module

@[expose] public section

/-! The even and odd projections associated with the source parity involution. -/

noncomputable section

namespace KhanSL2.Source

def evenPart : Module.End ℂ Source :=
  (1 / 2 : ℂ) • (LinearMap.id + parity.toLinearMap)

def oddPart : Module.End ℂ Source :=
  (1 / 2 : ℂ) • (LinearMap.id - parity.toLinearMap)

theorem evenPart_apply (a : Source) :
    evenPart a = (1 / 2 : ℂ) • (a + parity a) := rfl

theorem oddPart_apply (a : Source) :
    oddPart a = (1 / 2 : ℂ) • (a - parity a) := rfl

@[simp] theorem evenPart_add_oddPart (a : Source) :
    evenPart a + oddPart a = a := by
  rw [evenPart_apply, oddPart_apply]
  module

@[simp] theorem parity_evenPart (a : Source) :
    parity (evenPart a) = evenPart a := by
  simp only [evenPart_apply, map_smul, map_add, parity_parity]
  rw [add_comm]

@[simp] theorem parity_oddPart (a : Source) :
    parity (oddPart a) = -oddPart a := by
  simp only [oddPart_apply, map_smul, map_sub, parity_parity]
  module

@[simp] theorem evenPart_parity (a : Source) :
    evenPart (parity a) = evenPart a := by
  simp only [evenPart_apply, parity_parity]
  rw [add_comm]

@[simp] theorem oddPart_parity (a : Source) :
    oddPart (parity a) = -oddPart a := by
  simp only [oddPart_apply, parity_parity]
  module

@[simp] theorem evenPart_evenPart (a : Source) :
    evenPart (evenPart a) = evenPart a := by
  rw [evenPart_apply, parity_evenPart]
  module

@[simp] theorem oddPart_oddPart (a : Source) :
    oddPart (oddPart a) = oddPart a := by
  rw [oddPart_apply, parity_oddPart]
  module

@[simp] theorem evenPart_oddPart (a : Source) :
    evenPart (oddPart a) = 0 := by
  rw [evenPart_apply, parity_oddPart]
  simp

@[simp] theorem oddPart_evenPart (a : Source) :
    oddPart (evenPart a) = 0 := by
  rw [oddPart_apply, parity_evenPart]
  simp

theorem evenPart_translation (a : Source) :
    evenPart (translation a) = translation (evenPart a) := by
  simp only [evenPart_apply, map_smul, map_add, parity_translation]

theorem oddPart_translation (a : Source) :
    oddPart (translation a) = translation (oddPart a) := by
  simp only [oddPart_apply, map_smul, map_sub, parity_translation]

@[simp] theorem evenPart_X (i : ℕ) : evenPart (X i) = X i := by
  simp only [evenPart_apply, parity_X]
  module

@[simp] theorem oddPart_X (i : ℕ) : oddPart (X i) = 0 := by
  simp [oddPart_apply]

@[simp] theorem evenPart_Y (i : ℕ) : evenPart (Y i) = 0 := by
  simp [evenPart_apply]

@[simp] theorem oddPart_Y (i : ℕ) : oddPart (Y i) = Y i := by
  simp only [oddPart_apply, parity_Y]
  module

end KhanSL2.Source
