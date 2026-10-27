module

public import KhanSL2.ExteriorRing
public import KhanSL2.Injectivity.OrderedProducts

@[expose] public section

noncomputable section

namespace KhanSL2.FiniteExterior

open KhanSL2.Injectivity

variable {α : Type*} [DecidableEq α] [GeneratorOrder α]
variable {M : Type*} [AddCommMonoid M] [Module ℂ M]

/-- Exterior words determine a linear map. No sorting or independence assumption
on the word's generators is needed. -/
theorem linearMap_ext_orderedProducts (f g : Exterior α →ₗ[ℂ] M)
    (h : ∀ (n : ℕ) (a : Fin n → α),
      f (orderedProduct (fun i => generator (a i))) =
        g (orderedProduct (fun i => generator (a i)))) : f = g := by
  have hl : ∀ l : List α, f ((l.map generator).prod) = g ((l.map generator).prod) := by
    intro l
    simpa only [orderedProduct, List.ofFn_getElem_eq_map] using
      h l.length (fun i => l[(i : ℕ)])
  have hmul : ∀ u : Exterior α, ∀ l : List α,
      f ((l.map generator).prod * u) = g ((l.map generator).prod * u) := by
    intro u
    refine induction_on GeneratorOrder.code
      (P := fun u => ∀ l : List α,
        f ((l.map generator).prod * u) = g ((l.map generator).prod * u))
      ?_ ?_ ?_ ?_ ?_ u
    · intro l
      simp
    · intro l
      change f ((l.map generator).prod * 1) = g ((l.map generator).prod * 1)
      simpa only [mul_one] using hl l
    · intro v w hv hw l
      simp only [mul_add, map_add, hv l, hw l]
    · intro c v hv l
      simp only [mul_smul_comm, map_smul, hv l]
    · intro a v hv l
      change f ((l.map generator).prod * (generator a * v)) =
        g ((l.map generator).prod * (generator a * v))
      simpa only [List.map_append, List.map_singleton, List.prod_append,
        List.prod_singleton, mul_assoc] using hv (l ++ [a])
  apply LinearMap.ext
  intro u
  simpa only [List.map_nil, List.prod_nil, one_mul] using hmul u []

end KhanSL2.FiniteExterior
