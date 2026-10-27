module

public import KhanSL2.CEDerivationBasics
public import KhanSL2.CochainGrading

@[expose] public section

/-! Degree preservation for the fixed CE differential and color/translation actions. -/

noncomputable section

namespace KhanSL2

theorem qGenerator_degree (m : Mode) :
    qGenerator m ∈ cochainPiece (2, (m.bCount : ℤ), (m.weight : ℤ)) := by
  cases m with
  | b j a =>
    apply (cochainPiece _).neg_mem
    apply (cochainPiece _).sum_mem
    intro i hi
    apply (cochainPiece _).sum_mem
    intro b _
    apply (cochainPiece _).sum_mem
    intro c _
    apply (cochainPiece _).smul_mem
    have hi' := Finset.mem_range.mp hi
    have hdeg : ((1, ((Mode.c i b).bCount : ℤ), ((Mode.c i b).weight : ℤ)) : Degree) +
        (1, ((Mode.b (j - 1 - i) c).bCount : ℤ),
          ((Mode.b (j - 1 - i) c).weight : ℤ)) =
        (2, ((Mode.b j a).bCount : ℤ), ((Mode.b j a).weight : ℤ)) := by
      simp only [Mode.bCount, Mode.weight, Nat.cast_zero, Nat.cast_one,
        Prod.mk_add_mk, zero_add, Nat.cast_add]
      congr 2
      omega
    rw [← hdeg]
    exact cochain_wedge_mem (cochain_generator_mem _) (cochain_generator_mem _)
  | c j a =>
    apply (cochainPiece _).smul_mem
    apply (cochainPiece _).sum_mem
    intro i hi
    apply (cochainPiece _).sum_mem
    intro b _
    apply (cochainPiece _).sum_mem
    intro c _
    apply (cochainPiece _).smul_mem
    have hi' := Finset.mem_range.mp hi
    have hdeg : ((1, ((Mode.c i b).bCount : ℤ), ((Mode.c i b).weight : ℤ)) : Degree) +
        (1, ((Mode.c (j - 1 - i) c).bCount : ℤ),
          ((Mode.c (j - 1 - i) c).weight : ℤ)) =
        (2, ((Mode.c j a).bCount : ℤ), ((Mode.c j a).weight : ℤ)) := by
      simp only [Mode.bCount, Mode.weight, Nat.cast_zero, Nat.cast_one,
        Prod.mk_add_mk, zero_add, Nat.cast_add]
      congr 2
      omega
    rw [← hdeg]
    exact cochain_wedge_mem (cochain_generator_mem _) (cochain_generator_mem _)

theorem colorGenerator_degree (a : Fin 3) (m : Mode) :
    colorGenerator a m ∈ cochainPiece (1, (m.bCount : ℤ), (m.weight : ℤ)) := by
  apply (cochainPiece _).sum_mem
  intro c _
  apply (cochainPiece _).smul_mem
  cases m with
  | b j b =>
    simpa [Mode.recolor, Mode.bCount, Mode.weight] using cochain_generator_mem (Mode.b j c)
  | c j b =>
    simpa [Mode.recolor, Mode.bCount, Mode.weight] using cochain_generator_mem (Mode.c j c)

theorem translationGenerator_degree (m : Mode) :
    translationGenerator m ∈ cochainPiece
      ((1, (m.bCount : ℤ), (m.weight : ℤ)) + (0, 0, 1)) := by
  apply (cochainPiece _).smul_mem
  cases m with
  | b j a =>
    simpa [Mode.next, Mode.bCount, Mode.weight, Nat.cast_add, add_assoc]
      using cochain_generator_mem (Mode.b (j + 1) a)
  | c j a =>
    simpa [Mode.next, Mode.bCount, Mode.weight, Nat.cast_add, add_assoc]
      using cochain_generator_mem (Mode.c (j + 1) a)

theorem extendDerivation_degree (f : Mode → Cochain) (δ : Degree)
    (hf : ∀m, f m ∈ cochainPiece ((1, (m.bCount : ℤ), (m.weight : ℤ)) + δ))
    {d : Degree} {u : Cochain} (hu : u ∈ cochainPiece d) :
    extendDerivation f u ∈ cochainPiece (d + δ) := by
  rw [← u.sum_single]
  simp only [Finsupp.sum, map_sum, extendDerivation, Finsupp.linearCombination_single]
  apply (cochainPiece _).sum_mem
  intro s hs
  apply (cochainPiece _).smul_mem
  apply (cochainPiece _).sum_mem
  intro m hm
  apply (cochainPiece _).smul_mem
  have hd : monomialDegree s = d := hu hs
  have herase := monomialDegree_erase_add hm
  have heq : ((1, (m.bCount : ℤ), (m.weight : ℤ)) + δ) +
      monomialDegree (s.erase m) = d + δ := by
    rw [← hd, ← herase]
    ac_rfl
  rw [← heq]
  exact cochain_wedge_mem (hf m) (cochain_single_mem _ 1)

theorem q_degree {d : Degree} {u : Cochain} (hu : u ∈ cochainPiece d) :
    q u ∈ cochainPiece (d + (1, 0, 0)) := by
  apply extendDerivation_degree qGenerator (1, 0, 0) _ hu
  intro m
  simpa using qGenerator_degree m

theorem colorAction_degree (a : Fin 3) {d : Degree} {u : Cochain}
    (hu : u ∈ cochainPiece d) : colorAction a u ∈ cochainPiece d := by
  simpa only [colorAction, add_zero] using extendDerivation_degree (colorGenerator a) 0
    (fun m => by simpa using colorGenerator_degree a m) hu

theorem translation_degree {d : Degree} {u : Cochain} (hu : u ∈ cochainPiece d) :
    translation u ∈ cochainPiece (d + (0, 0, 1)) :=
  extendDerivation_degree translationGenerator (0, 0, 1) translationGenerator_degree hu

end KhanSL2
