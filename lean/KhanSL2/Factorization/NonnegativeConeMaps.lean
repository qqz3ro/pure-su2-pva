module

public import KhanSL2.Factorization.ComplexDevissage

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace KhanSL2.Factorization.NonnegativeCone

universe u v
variable {R : Type u} [CommRing R]
variable {C D C' D' : ChainComplex (ModuleCat.{v} R) ℕ}
variable (φ : C ⟶ D) (ψ : C' ⟶ D')
variable (f : C ⟶ C') (g : D ⟶ D')

/-- The cone map associated to an actual commuting comparison square. -/
def mapTerm : ∀ n, Term C D n →ₗ[R] Term C' D' n
  | 0 => (g.f 0).hom
  | n+1 => ((g.f (n+1)).hom).prodMap ((f.f n).hom)

theorem square_apply (h : φ ≫ g = f ≫ ψ) (n : ℕ) (x : C.X n) :
    g.f n (φ.f n x) = ψ.f n (f.f n x) := by
  have he := congrArg (fun q => q.f n) h
  exact congrArg (fun q => q x) he

theorem mapTerm_d (h : φ ≫ g = f ≫ ψ) (n : ℕ) :
    (differential ψ n).comp (mapTerm f g (n+1)) =
      (mapTerm f g n).comp (differential φ n) := by
  apply LinearMap.ext
  intro z
  rcases z with ⟨y,x⟩
  cases n with
  | zero =>
    change D'.d 1 0 (g.f 1 y) + ψ.f 0 (f.f 0 x) =
      g.f 0 (D.d 1 0 y + φ.f 0 x)
    rw [ComplexExactness.map_d_apply,map_add,square_apply φ ψ f g h]
  | succ n =>
    apply Prod.ext
    · change D'.d (n+2) (n+1) (g.f (n+2) y) + ψ.f (n+1) (f.f (n+1) x) =
        g.f (n+1) (D.d (n+2) (n+1) y + φ.f (n+1) x)
      rw [ComplexExactness.map_d_apply,map_add,square_apply φ ψ f g h]
    · change -C'.d (n+1) n (f.f (n+1) x) = f.f n (-C.d (n+1) n x)
      rw [ComplexExactness.map_d_apply,map_neg]

def mapComplex (h : φ ≫ g = f ≫ ψ) : complex φ ⟶ complex ψ :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (mapTerm f g n)) (fun n => by
    rw [complex_d,complex_d]
    apply ModuleCat.hom_ext
    exact mapTerm_d φ ψ f g h n)

@[simp] theorem mapComplex_f (h : φ ≫ g = f ≫ ψ) (n : ℕ) :
    (mapComplex φ ψ f g h).f n = ModuleCat.ofHom (mapTerm f g n) := rfl

end KhanSL2.Factorization.NonnegativeCone