# Mathematical objects and Lean declarations

This is a navigation guide to the completed formalization. Names below are exact
declaration names. File links are relative to this release. The main target is Theorem 1.1 of [the paper](../paper/Pure_SU2_PVA_Proof.pdf).
Other entries identify mathematical components without claiming a line-by-line
correspondence of proof arguments.
Read [SCOPE.md](SCOPE.md) for the mathematical conventions and
[PROOF-GUIDE.md](PROOF-GUIDE.md) for the proof architecture.

## Main statement and fixed objects

| Mathematical role | Lean declaration | Source |
|---|---|---|
| Explicit theorem interface | `KhanSL2.mainStatement_explicit` | [Final.lean](../lean/Final.lean) |
| Completed theorem | `KhanSL2.mainStatement` | [MainProof.lean](../lean/MainProof.lean) |
| Proposition proved | `KhanSL2.MainStatement` | [MainStatement.lean](../lean/KhanSL2/MainStatement.lean) |
| Bijectivity of the specified map | `KhanSL2.phi_bijective` | [MainProof.lean](../lean/MainProof.lean) |
| Source presentation and its differential relations | `KhanSL2.SourcePresentation.Relation`, `KhanSL2.Source` | [Source.lean](../lean/KhanSL2/Source.lean) |
| Source operations and generator bracket specification | `KhanSL2.sourceData`, `KhanSL2.IsSourceBracket` | [SourceData.lean](../lean/KhanSL2/SourceData.lean) |
| Actual source bracket and generator formulas | `KhanSL2.Source.bracket`, `KhanSL2.Source.bracket_generator_formulas` | [SourceBracketQuotient.lean](../lean/KhanSL2/SourceBracketQuotient.lean) |
| Full PVA axioms | `KhanSL2.IsPVA` | [PVA.lean](../lean/KhanSL2/PVA.lean) |
| Source satisfies those axioms | `KhanSL2.source_isPVA` | [SourcePVA.lean](../lean/KhanSL2/SourcePVA.lean) |
| Finite cochains, relative invariants, cycles, boundaries, and cohomology | `KhanSL2.Cochain`, `relativeInvariants`, `relativeCycles`, `relativeBoundaries`, `Cohomology` | [CE.lean](../lean/KhanSL2/CE.lean) |
| CE differential squares to zero | `KhanSL2.q_square_zero` | [CESquareZero.lean](../lean/KhanSL2/CESquareZero.lean) |
| All relative complex laws | `KhanSL2.relativeComplex_laws` | [CEComplex.lean](../lean/KhanSL2/CEComplex.lean) |
| Target operations, PVA laws, and induced-bracket identification | `KhanSL2.targetData`, `targetBracket`, `target_isPVA`, `target_isInduced` | [TargetPVA.lean](../lean/KhanSL2/TargetPVA.lean) |
| Explicit cocycle classes | `KhanSL2.xClass`, `KhanSL2.yClass` | [Cocycles.lean](../lean/KhanSL2/Cocycles.lean) |
| Specified map and quotient well-definedness | `KhanSL2.phi`, `KhanSL2.phi_well_defined` | [CanonicalMap.lean](../lean/KhanSL2/CanonicalMap.lean) |
| Generator images and uniqueness | `KhanSL2.phi_X`, `phi_Y`, `phi_unique` | [CanonicalMap.lean](../lean/KhanSL2/CanonicalMap.lean) |
| PVA morphism structure | `KhanSL2.phiPVAMap` | [CanonicalMap.lean](../lean/KhanSL2/CanonicalMap.lean) |
| Isomorphism property for a fixed map | `KhanSL2.IsGradedDifferentialPVAIsomorphism` | [PVAIsomorphism.lean](../lean/KhanSL2/PVAIsomorphism.lean) |

In rows that list several short names, the namespace shown on the first name
applies to all names in that row.

## Main proof components

| Mathematical role | Lean declaration | Source |
|---|---|---|
| Injectivity of the original map | `KhanSL2.phi_injective` | [Injectivity.lean](../lean/KhanSL2/Injectivity.lean) |
| Relative CE homology and finite homogeneous duality | `KhanSL2.Current.K`, `K_finiteDimensional`, `dictionary` | [DictionaryStatement.lean](../lean/KhanSL2/DictionaryStatement.lean) |
| Transpose comparison and its surjectivity | `KhanSL2.Current.psiK`, `psiK_apply`, `psiK_surjective` | [DictionaryStatement.lean](../lean/KhanSL2/DictionaryStatement.lean) |
| Actual relative affine BGG resolution | `KhanSL2.BGG.relativeBGGResolution`, `KhanSL2.BGG.relative_bgg_resolution` | [RelativeBGG.lean](../lean/KhanSL2/BGG/RelativeBGG.lean) |
| Polynomial model of the restricted source dual | `KhanSL2.Modules.sourceDualEquiv` | [SourceDualModel.lean](../lean/KhanSL2/Modules/SourceDualModel.lean) |
| Linearity for the actual coefficient-ring action | `KhanSL2.Modules.psiBLinear` | [CoefficientLinearity.lean](../lean/KhanSL2/Modules/CoefficientLinearity.lean) |
| Finiteness of BGG terms | `KhanSL2.PolynomialBGG.bggTerm_finite` | [FiniteTerms.lean](../lean/KhanSL2/PolynomialBGG/FiniteTerms.lean) |
| Projectivity of BGG terms | `KhanSL2.PolynomialBGG.bggTerm_projective` | [ProjectiveTerms.lean](../lean/KhanSL2/PolynomialBGG/ProjectiveTerms.lean) |
| Top BGG term is free of rank one | `KhanSL2.Conditional.topTermEquiv` | [TopRankOne.lean](../lean/KhanSL2/Conditional/TopRankOne.lean) |
| Low-degree comparison | `KhanSL2.lowDegreeStep` | [LowDegree.lean](../lean/KhanSL2/Deformation/LowDegree.lean) |
| Source-side depth bound | `KhanSL2.Depth.depth_JB_ge` | [SourceDepth.lean](../lean/KhanSL2/Depth/SourceDepth.lean) |
| Strong Macdonald harmonic/cohomology equivalence | `KhanSL2.StrongMacdonald.harmEquivCohom` | [Hodge.lean](../lean/KhanSL2/StrongMacdonald/Hodge.lean) |
| Freeness description of harmonic invariants | `KhanSL2.StrongMacdonald.harm_free` | [SliceRing.lean](../lean/KhanSL2/StrongMacdonald/SliceRing.lean) |
| Actual symmetric coefficient shuffle | `KhanSL2.SymmetricFamily.symmetricTensorShuffle` | [SymmetricTensorShuffleProved.lean](../lean/KhanSL2/SymmetricFamily/SymmetricTensorShuffleProved.lean) |
| Kunneth with the original independent coefficient actions | `KhanSL2.Factorization.degreeBalancedKunnethEquiv` | [DegreeBalancedKunneth.lean](../lean/KhanSL2/Factorization/DegreeBalancedKunneth.lean) |
| Factorization of the original coefficient homology on coprime charts | `KhanSL2.Factorization.BGGTransfer.chartFactorizationEquiv` | [FiniteBGGChartFactorization.lean](../lean/KhanSL2/Factorization/FiniteBGGChartFactorization.lean) |
| Unconditional factorization theorem | `KhanSL2.Collision.kFactor` | [Proof.lean](../lean/KhanSL2/Collision/Proof.lean) |
| Factorization implies collision support | `KhanSL2.Collision.collisionSupportStep_of_kFactor` | [Reduction.lean](../lean/KhanSL2/Collision/Reduction.lean) |
| Final assembly from collision support | `KhanSL2.Conditional.mainStatement_of_collisionSupport` | [Assembly.lean](../lean/KhanSL2/Conditional/Assembly.lean) |
| Final assembly from factorization | `KhanSL2.Collision.mainStatement_of_kFactor` | [Completion.lean](../lean/KhanSL2/Collision/Completion.lean) |

The assembly lemmas take intermediate claims as parameters. The final theorem
supplies each parameter with a proved result.

## Verification entry points

[FinalAudit.lean](../lean/FinalAudit.lean) checks the explicit interface and imports
the full original audit. [MainProofAudit.lean](../lean/MainProofAudit.lean) checks the unconditional types
of `kFactor` and `mainStatement`, confirms that they are theorem declarations,
and checks transitive axiom dependencies with the relevant private proof bodies
available. [verify.ps1](../lean/verify.ps1) runs the native build and standalone
audits. These are proof checks, not a substitute for reviewing the mathematical
meaning of the definitions above.

