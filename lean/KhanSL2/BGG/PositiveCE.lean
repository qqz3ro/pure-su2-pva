module

public import KhanSL2.BGG.ExteriorModel
public import KhanSL2.CESquareZero
public import KhanSL2.CELeibniz

@[expose] public section

/-! The pure-c CE complex of positive currents, as a proved retract of the
concrete finite-cochain model already used by the main theorem. -/

noncomputable section
open scoped BigOperators

namespace KhanSL2.BGG.PositiveCE

@[ext] structure Mode where
  index : ℕ
  color : Fin 3
  deriving DecidableEq

def Mode.code (m : Mode) : ℕ := 3 * m.index + m.color.val

theorem Mode.code_injective : Function.Injective Mode.code := by
  intro m n h
  have hm := m.color.isLt
  have hn := n.color.isLt
  dsimp [Mode.code] at h
  apply Mode.ext
  · omega
  · apply Fin.ext
    omega

instance : FiniteExterior.GeneratorOrder Mode where
  code := Mode.code
  code_injective := Mode.code_injective

abbrev Cochain := FiniteExterior.Exterior Mode

/-- Include positive-current ghosts in the original relative CE coordinates. -/
def inclusion : Cochain →ₐ[ℂ] KhanSL2.Cochain :=
  FiniteExterior.substituteOdd
    (fun m : Mode => KhanSL2.generator (.c m.index m.color))
    (fun _ => FiniteExterior.parity_generator _)

/-- Kill every y-current ghost, retaining the positive-current ghosts. -/
def projectedGenerator : KhanSL2.Mode → Cochain
  | .b _ _ => 0
  | .c j a => FiniteExterior.generator ⟨j, a⟩

theorem projectedGenerator_parity (m : KhanSL2.Mode) :
    FiniteExterior.parityLinear (projectedGenerator m) = -projectedGenerator m := by
  cases m <;> simp [projectedGenerator]

def projection : KhanSL2.Cochain →ₐ[ℂ] Cochain :=
  FiniteExterior.substituteOdd projectedGenerator projectedGenerator_parity

@[simp] theorem inclusion_generator (m : Mode) :
    inclusion (FiniteExterior.generator m) = KhanSL2.generator (.c m.index m.color) :=
  FiniteExterior.substituteOdd_generator (α := Mode) (β := KhanSL2.Mode) _ _ m

@[simp] theorem projection_b (j : ℕ) (a : Fin 3) :
    projection (KhanSL2.generator (.b j a)) = 0 :=
  FiniteExterior.substituteOdd_generator (α := KhanSL2.Mode) (β := Mode)
    projectedGenerator projectedGenerator_parity (.b j a)

@[simp] theorem projection_c (j : ℕ) (a : Fin 3) :
    projection (KhanSL2.generator (.c j a)) = FiniteExterior.generator ⟨j, a⟩ :=
  FiniteExterior.substituteOdd_generator (α := KhanSL2.Mode) (β := Mode)
    projectedGenerator projectedGenerator_parity (.c j a)

theorem projection_comp_inclusion : projection.comp inclusion = AlgHom.id ℂ Cochain := by
  apply FiniteExterior.algHom_ext
  intro m
  cases m
  simp

@[simp] theorem projection_inclusion (u : Cochain) : projection (inclusion u) = u :=
  DFunLike.congr_fun projection_comp_inclusion u

theorem inclusion_injective : Function.Injective inclusion := by
  intro u v h
  simpa using congrArg projection h

/-- The coordinate inclusion preserves exterior parity. -/
theorem inclusion_parity (u : Cochain) :
    inclusion (FiniteExterior.parityLinear u) = KhanSL2.cochainParity (inclusion u) := by
  have h : inclusion.comp (FiniteExterior.parity (α := Mode)) =
      (FiniteExterior.parity (α := KhanSL2.Mode)).comp inclusion := by
    apply FiniteExterior.algHom_ext
    intro m
    simp [FiniteExterior.parity_apply]
    exact (FiniteExterior.parity_generator (KhanSL2.Mode.c m.index m.color)).symm
  exact DFunLike.congr_fun h u
/-- The actual positive-current cochain differential, obtained from the
original CE differential and the explicit inclusion and projection. -/
def d : Module.End ℂ Cochain :=
  projection.toLinearMap.comp (KhanSL2.q.comp inclusion.toLinearMap)

@[simp] theorem d_apply (u : Cochain) : d u = projection (KhanSL2.q (inclusion u)) := rfl

@[simp] theorem d_one : d 1 = 0 := by
  simp [KhanSL2.cochain_one_eq, KhanSL2.q]

/-- The positive-current differential is an odd derivation. -/
theorem d_mul (u v : Cochain) :
    d (u * v) = d u * v + FiniteExterior.parityLinear u * d v := by
  simp only [d_apply, map_mul, KhanSL2.q_mul, map_add, ← inclusion_parity,
    projection_inclusion]
/-- The pure-c generator formula, in physical positive modes index+1. -/
theorem d_generator (m : Mode) :
    d (FiniteExterior.generator m) =
      (-(1 / 2 : ℂ)) •
        ∑ i ∈ Finset.range m.index, ∑ b : Fin 3, ∑ c : Fin 3,
          epsilon m.color b c •
            (FiniteExterior.generator (⟨i, b⟩ : Mode) *
             FiniteExterior.generator (⟨m.index - 1 - i, c⟩ : Mode)) := by
  simp [KhanSL2.qGenerator, ← KhanSL2.cochain_mul_eq_wedge]

theorem inclusion_projection_q_generator (m : Mode) :
    inclusion (projection (KhanSL2.q (inclusion (FiniteExterior.generator m)))) =
      KhanSL2.q (inclusion (FiniteExterior.generator m)) := by
  simp [KhanSL2.qGenerator, ← KhanSL2.cochain_mul_eq_wedge]

/-- The pure-current image is preserved by the original CE differential. -/
theorem inclusion_projection_q (u : Cochain) :
    inclusion (projection (KhanSL2.q (inclusion u))) = KhanSL2.q (inclusion u) := by
  refine FiniteExterior.induction_on Mode.code
    (P := fun v : Cochain => inclusion (projection (KhanSL2.q (inclusion v))) =
      KhanSL2.q (inclusion v)) ?_ ?_ ?_ ?_ ?_ u
  · simp
  · change inclusion (projection (KhanSL2.q (inclusion 1))) = KhanSL2.q (inclusion 1)
    simp [KhanSL2.cochain_one_eq, KhanSL2.q]
  · intro v w hv hw
    simp only [map_add, hv, hw]
  · intro r v hv
    simp only [map_smul, hv]
  · intro m v hv
    change inclusion (projection (KhanSL2.q (inclusion (FiniteExterior.generator m * v)))) =
      KhanSL2.q (inclusion (FiniteExterior.generator m * v))
    have hp : KhanSL2.cochainParity (inclusion (FiniteExterior.generator m)) =
        -inclusion (FiniteExterior.generator m) := by
      rw [inclusion_generator]
      exact FiniteExterior.parity_generator _
    simp only [map_mul, KhanSL2.q_mul, hp, map_add, map_neg,
      projection_inclusion, inclusion_projection_q_generator, hv]

theorem inclusion_d (u : Cochain) : inclusion (d u) = KhanSL2.q (inclusion u) :=
  inclusion_projection_q u

/-- Square-zero follows from the already verified concrete CE square-zero theorem. -/
theorem d_square_zero (u : Cochain) : d (d u) = 0 := by
  apply inclusion_injective
  rw [inclusion_d, inclusion_d, KhanSL2.q_square_zero, map_zero]

end KhanSL2.BGG.PositiveCE