module

public import KhanSL2.Factorization.ComplexExactness
public import KhanSL2.Factorization.QuasiIsoElements
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.LinearAlgebra.Pi

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace KhanSL2.Factorization.NonnegativeCone

universe u v
variable {R : Type u} [CommRing R]
variable (C D : ChainComplex (ModuleCat.{v} R) ℕ)

/-- The genuine nonnegative cone has no shifted source summand in degree zero. -/
def Term : ℕ → Type v
  | 0 => D.X 0
  | n+1 => D.X (n+1) × C.X n

instance termAddCommGroup (n : ℕ) : AddCommGroup (Term C D n) := by
  cases n <;> dsimp [Term] <;> infer_instance
instance termModule (n : ℕ) : Module R (Term C D n) := by
  cases n <;> dsimp [Term] <;> infer_instance

variable {C D} (φ : C ⟶ D)

/-- Cone differential `(y,x) ↦ (d y + φ x,-d x)`, including the degree-zero edge. -/
def differential : ∀ n, Term C D (n+1) →ₗ[R] Term C D n
  | 0 => (D.d 1 0).hom.comp (LinearMap.fst R _ _) +
      (φ.f 0).hom.comp (LinearMap.snd R _ _)
  | n+1 =>
      ((D.d (n+2) (n+1)).hom.comp (LinearMap.fst R _ _) +
        (φ.f (n+1)).hom.comp (LinearMap.snd R _ _)).prod
      (-(C.d (n+1) n).hom.comp (LinearMap.snd R _ _))

@[simp] theorem differential_zero (y : D.X 1) (x : C.X 0) :
    differential φ 0 (y,x) = D.d 1 0 y + φ.f 0 x := rfl

@[simp] theorem differential_succ (n : ℕ) (y : D.X (n+2)) (x : C.X (n+1)) :
    differential φ (n+1) (y,x) =
      (D.d (n+2) (n+1) y + φ.f (n+1) x,-C.d (n+1) n x) := rfl

theorem comm_apply (n : ℕ) (x : C.X (n+1)) :
    D.d (n+1) n (φ.f (n+1) x) = φ.f n (C.d (n+1) n x) :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.comm (n+1) n)) x

theorem square (n : ℕ) : (differential φ n).comp (differential φ (n+1)) = 0 := by
  apply LinearMap.ext
  intro z
  rcases z with ⟨y,x⟩
  cases n with
  | zero =>
    change D.d 1 0 (D.d 2 1 y + φ.f 1 x) + φ.f 0 (-C.d 1 0 x) = 0
    rw [map_add,map_neg,comm_apply]
    have hD := LinearMap.congr_fun (ComplexExactness.differential_square D 0) y
    change D.d 1 0 (D.d 2 1 y) = 0 at hD
    rw [hD,zero_add,add_neg_cancel]
  | succ n =>
    apply Prod.ext
    · change D.d (n+2) (n+1) (D.d (n+3) (n+2) y + φ.f (n+2) x) +
        φ.f (n+1) (-C.d (n+2) (n+1) x) = 0
      rw [map_add,map_neg,comm_apply]
      have hD := LinearMap.congr_fun (ComplexExactness.differential_square D (n+1)) y
      change D.d (n+2) (n+1) (D.d (n+3) (n+2) y) = 0 at hD
      rw [hD,zero_add,add_neg_cancel]
    · change -C.d (n+1) n (-C.d (n+2) (n+1) x) = 0
      rw [map_neg,neg_neg]
      exact LinearMap.congr_fun (ComplexExactness.differential_square C n) x

def complex : ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (Term C D n))
    (fun n => ModuleCat.ofHom (differential φ n))
    (fun n => ModuleCat.hom_ext (square φ n))

@[simp] theorem complex_X (n : ℕ) : (complex φ).X n = ModuleCat.of R (Term C D n) := rfl
@[simp] theorem complex_d (n : ℕ) :
    (complex φ).d (n+1) n = ModuleCat.ofHom (differential φ n) := by
  simp only [complex,ChainComplex.of,ChainComplex.of_d]

instance term_finite [∀ n, Module.Finite R (C.X n)] [∀ n, Module.Finite R (D.X n)]
    (n : ℕ) : Module.Finite R (Term C D n) := by
  cases n <;> dsimp [Term] <;> infer_instance

instance term_projective [∀ n, Module.Projective R (C.X n)] [∀ n, Module.Projective R (D.X n)]
    (n : ℕ) : Module.Projective R (Term C D n) := by
  cases n <;> dsimp [Term] <;> infer_instance

theorem flat_prod (M N : Type v) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Flat R M] [Module.Flat R N] :
    Module.Flat R (M × N) := by
  let T : Fin 2 → Type v := Fin.cases M (fun _ => N)
  let : ∀ i, AddCommGroup (T i) := by
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · dsimp [T]; infer_instance
    · dsimp [T]; infer_instance
  let : ∀ i, Module R (T i) := by
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · dsimp [T]; infer_instance
    · dsimp [T]; infer_instance
  let : ∀ i, Module.Flat R (T i) := by
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · dsimp [T]; infer_instance
    · dsimp [T]; infer_instance
  let e : (Π₀ i, T i) ≃ₗ[R] M × N :=
    (DFinsupp.linearEquivFunOnFintype (R := R) (M := T)).trans (LinearEquiv.piFinTwo R T)
  exact Module.Flat.of_linearEquiv e.symm

instance term_flat [∀ n, Module.Flat R (C.X n)] [∀ n, Module.Flat R (D.X n)]
    (n : ℕ) : Module.Flat R (Term C D n) := by
  cases n with
  | zero => exact inferInstanceAs (Module.Flat R (D.X 0))
  | succ n => exact flat_prod (D.X (n+1)) (C.X n)
end KhanSL2.Factorization.NonnegativeCone
