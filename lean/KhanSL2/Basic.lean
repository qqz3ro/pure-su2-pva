module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.Torsion.Field

@[expose] public section

/-! Basic notation shared by the concrete presentation and the statement. -/

namespace KhanSL2

/-- Total CE degree, number of square-zero coefficient modes, and spin.
The cohomological degree `p` in the attachment is `degree.1 - degree.2.1`. -/
abbrev Degree := ℤ × ℤ × ℤ

end KhanSL2
