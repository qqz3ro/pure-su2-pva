module

public import KhanSL2.SourceBracketSkew
public import KhanSL2.SourceBracketDegree
public import KhanSL2.SourceBracketGeneratorJacobi
public import KhanSL2.SourceJacobiThird
public import KhanSL2.JacobiLastPermutation

@[expose] public section

/-! Full super-Jacobi on the source, extended from its eight generator cases. -/

noncomputable section

namespace KhanSL2.Source

open LambdaBracket SourceGeneratorChecks

/-- The Jacobi identity holds for every pair of homogeneous source elements
and an arbitrary third element. No Jacobi hypothesis is used. -/
theorem bracket_super_jacobi (d e : Degree) (a b c : Source)
    (ha : a ∈ piece d) (hb : b ∈ piece e) :
    bracket.jacobiLeft a b c =
      bracket.jacobiMiddle a b c + koszulSign d e • bracket.jacobiRight a b c := by
  have hL : HasSuperLeibniz sourceData bracket := bracket_super_leibniz
  have hdeg : HasBracketDegree sourceData bracket := bracket_degree
  have hR : HasSesquilinearRight translation bracket := bracket_right_translation
  have hT : HasSesquilinearLeft translation bracket := bracket_left_translation
  have hsk : HasSuperSkew sourceData bracket := bracket_super_skew
  have hGG : ∀ i j : Kind, ∀ c : Source,
      jacobiator bracket (koszulSign (SourceGeneratorChecks.generatorDegree i)
        (SourceGeneratorChecks.generatorDegree j))
        (generator i) (generator j) c = 0 := by
    intro i j
    exact jacobiator_third_of_generators hL hdeg hR (generator_mem i) (generator_mem j)
      (generator_jacobiator i j .X) (generator_jacobiator i j .Y)
  have hG : ∀ i : Kind, ∀ e b, b ∈ piece e → ∀ c : Source,
      jacobiator bracket (koszulSign (SourceGeneratorChecks.generatorDegree i) e)
        (generator i) b c = 0 := by
    intro i e b hb
    apply jacobiator_third_of_generators hL hdeg hR (generator_mem i) hb
    · change jacobiator bracket (koszulSign (SourceGeneratorChecks.generatorDegree i) e)
        (generator i) b (generator .X) = 0
      rw [jacobiator_lastSwap hR hsk hdeg (generator_mem i) hb (generator_mem .X)]
      rw [hGG i .X, map_zero, smul_zero]
    · change jacobiator bracket (koszulSign (SourceGeneratorChecks.generatorDegree i) e)
        (generator i) b (generator .Y) = 0
      rw [jacobiator_lastSwap hR hsk hdeg (generator_mem i) hb (generator_mem .Y)]
      rw [hGG i .Y, map_zero, smul_zero]
  have hbase : ∀ i : Kind, jacobiator bracket (koszulSign d e) a b (generator i) = 0 := by
    intro i
    rw [jacobiator_lastSwap hR hsk hdeg ha hb (generator_mem i)]
    rw [jacobiator_swap hT hsk ha (generator_mem i)]
    rw [hG i d a ha b, map_zero, smul_zero, map_zero, smul_zero]
  exact (jacobiator_eq_zero_iff _ _ _ _ _).mp
    (jacobiator_third_of_generators hL hdeg hR ha hb (hbase .X) (hbase .Y) c)

end KhanSL2.Source
