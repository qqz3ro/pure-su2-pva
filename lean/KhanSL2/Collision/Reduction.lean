module

public import KhanSL2.Collision.JFactor
public import KhanSL2.Collision.Assembly

@[expose] public section

/-!
# Collision support from the factorization of `K`

With the factorization of `J` (`jFactor`) and the chart assembly, the collision-support step
reduces to the factorization of the coefficient homology `K` on charts.
-/

namespace KhanSL2.Collision

theorem collisionSupportStep_of_kFactor (hK : ∀ B, KFactor B) :
    Conditional.CollisionSupportStep :=
  collisionSupportStep_of_chartComparison fun B =>
    chartComparison_of_factor B (hK B) (jFactor B)

end KhanSL2.Collision
