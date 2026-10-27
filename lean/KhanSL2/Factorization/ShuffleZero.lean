module

public import KhanSL2.Factorization.ShuffleRetracts

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The actual shuffle is an isomorphism when either coefficient module is zero. -/
noncomputable section
open scoped TensorProduct
open CategoryTheory
namespace KhanSL2.Factorization
open BGG BGGBridge

variable (M N : Type)
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]

/-- A zero coefficient module gives the actual zero relative chain space. -/
theorem relativeChains_subsingleton [Subsingleton M] : Subsingleton (RelativeChains M) := by
  let : Subsingleton (RawChains M) :=
    inferInstanceAs (Subsingleton (BGG.PositiveCE.Cochain ⊗[ℂ] M))
  infer_instance

/-- Zero source and ambient target tensors make every component of the original shuffle invertible. -/
theorem shuffle_quasiIso_of_zero_tensors [Subsingleton (M ⊗[ℂ] N)]
    [Subsingleton (RelativeChains M ⊗[ℂ] RelativeChains N)] :
    QuasiIso (shuffleComplex M N) := by
  let : Subsingleton (RelativeChains (M ⊗[ℂ] N)) := relativeChains_subsingleton (M ⊗[ℂ] N)
  let (j : ℕ) : Subsingleton ((complex (M ⊗[ℂ] N)).X j) :=
    inferInstanceAs (Subsingleton (degree (M ⊗[ℂ] N) j))
  let (j : ℕ) : Subsingleton ((tensorComplex M N).X j) :=
    ⟨fun x y => tensorDegreeForget_injective M N j (Subsingleton.elim _ _)⟩
  let (j : ℕ) : IsIso ((shuffleComplex M N).f j) :=
    (ConcreteCategory.isIso_iff_bijective ((shuffleComplex M N).f j)).mpr
      ⟨fun _ _ _ => Subsingleton.elim _ _,fun y => ⟨0,Subsingleton.elim _ y⟩⟩
  let : IsIso (shuffleComplex M N) := HomologicalComplex.Hom.isIso_of_components _
  infer_instance

/-- The specified shuffle is a quasi-isomorphism for a zero first coefficient. -/
theorem shuffle_quasiIso_subsingleton_first [Subsingleton M] : QuasiIso (shuffleComplex M N) := by
  let : Subsingleton (RelativeChains M) := relativeChains_subsingleton M
  exact shuffle_quasiIso_of_zero_tensors M N

/-- The specified shuffle is a quasi-isomorphism for a zero second coefficient. -/
theorem shuffle_quasiIso_subsingleton_second [Subsingleton N] : QuasiIso (shuffleComplex M N) := by
  let : Subsingleton (RelativeChains N) := relativeChains_subsingleton N
  exact shuffle_quasiIso_of_zero_tensors M N

end KhanSL2.Factorization
