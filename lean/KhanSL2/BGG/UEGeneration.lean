module

public import KhanSL2.BGG.Augmentation

@[expose] public section

/-! Lie generating families generate the enveloping algebra as an algebra. -/

noncomputable section

namespace KhanSL2.BGG.UE

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "A" => UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Pulling an associative subalgebra back along the universal Lie map. -/
def algebraLiePreimage (B : Subalgebra R A) : LieSubalgebra R L where
  carrier := {x | UniversalEnvelopingAlgebra.ι R x ∈ B}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change UniversalEnvelopingAlgebra.ι R (x + y) ∈ B
    simpa only [map_add] using B.add_mem hx hy
  smul_mem' := by
    intro r x hx
    change UniversalEnvelopingAlgebra.ι R (r • x) ∈ B
    rw [map_smul, Algebra.smul_def]
    exact B.mul_mem (B.algebraMap_mem r) hx
  lie_mem' := by
    intro x y hx hy
    change UniversalEnvelopingAlgebra.ι R ⁅x, y⁆ ∈ B
    rw [(UniversalEnvelopingAlgebra.ι R).map_lie]
    exact B.sub_mem (B.mul_mem hx hy) (B.mul_mem hy hx)

/-- Lie generation implies algebra generation after passing to `U(L)`. -/
theorem adjoin_eq_top_of_lieSpan_eq_top (S : Set L)
    (hS : LieSubalgebra.lieSpan R L S = ⊤) :
    Algebra.adjoin R ((UniversalEnvelopingAlgebra.ι R) '' S) = ⊤ := by
  let B := Algebra.adjoin R ((UniversalEnvelopingAlgebra.ι R) '' S)
  have hle : LieSubalgebra.lieSpan R L S ≤ algebraLiePreimage R L B := by
    apply LieSubalgebra.lieSpan_le.mpr
    intro x hx
    exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
  have hi (x : L) : UniversalEnvelopingAlgebra.ι R x ∈ B :=
    hle (by rw [hS]; trivial)
  apply top_unique
  intro a _
  exact induction R L (fun r => B.algebraMap_mem r) hi
    (fun _ _ => B.mul_mem) (fun _ _ => B.add_mem) a

end KhanSL2.BGG.UE
