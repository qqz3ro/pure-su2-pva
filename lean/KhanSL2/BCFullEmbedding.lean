module

public import KhanSL2.BCFullCE
public import KhanSL2.ExteriorReindex

@[expose] public section

/-! The original finite cochains embed in the algebra with zero ghosts. -/

noncomputable section

namespace KhanSL2

def modeInclusion : Mode ↪ FullMode := ⟨Sum.inr, Sum.inr_injective⟩

def fullInclusion : Cochain →ₐ[ℂ] FullCochain :=
  FiniteExterior.reindexAlgHom modeInclusion FullMode.code_inr_lt

theorem fullInclusion_apply (u : Cochain) :
    fullInclusion u = FiniteExterior.reindex modeInclusion u := rfl

@[simp] theorem fullInclusion_single (s : ExteriorMonomial) (r : ℂ) :
    fullInclusion (Finsupp.single s r) = Finsupp.single (s.map modeInclusion) r :=
  FiniteExterior.reindex_single modeInclusion s r

@[simp] theorem fullInclusion_generator (m : Mode) :
    fullInclusion (generator m) = fullGenerator (.inr m) :=
  FiniteExterior.reindex_generator modeInclusion m

@[simp] theorem fullInclusion_one : fullInclusion cochainOne = fullOne := by
  exact map_one fullInclusion

theorem fullInclusion_injective : Function.Injective fullInclusion :=
  FiniteExterior.reindex_injective modeInclusion

theorem fullInclusion_wedge (u v : Cochain) :
    fullInclusion (wedge u v) = fullWedge (fullInclusion u) (fullInclusion v) :=
  map_mul fullInclusion u v

theorem fullInclusion_parity (u : Cochain) :
    fullInclusion (cochainParity u) = fullParity (fullInclusion u) :=
  FiniteExterior.reindex_parity modeInclusion u

theorem fullInclusion_translationGenerator (m : Mode) :
    fullInclusion (translationGenerator m) = fullTranslationGenerator (.inr m) := by
  simp only [translationGenerator, fullTranslationGenerator, map_smul, fullInclusion_generator,
    FullMode.translationCoefficient, FullMode.order, FullMode.next,
    Mode.translationCoefficient_order]

theorem fullInclusion_translation (u : Cochain) :
    fullInclusion (translation u) = fullTranslation (fullInclusion u) :=
  FiniteExterior.reindex_extendDerivation Mode.code FullMode.code modeInclusion
    FullMode.code_inr_lt translationGenerator fullTranslationGenerator
    fullInclusion_translationGenerator u

theorem fullInclusion_colorGenerator (a : Fin 3) (m : Mode) :
    fullInclusion (colorGenerator a m) = fullColorGenerator a (.inr m) := by
  simp [colorGenerator, fullColorGenerator, FullMode.color, FullMode.recolor]

theorem fullInclusion_colorAction (a : Fin 3) (u : Cochain) :
    fullInclusion (colorAction a u) = fullColorAction a (fullInclusion u) :=
  FiniteExterior.reindex_extendDerivation Mode.code FullMode.code modeInclusion
    FullMode.code_inr_lt (colorGenerator a) (fullColorGenerator a)
    (fullInclusion_colorGenerator a) u

end KhanSL2

