module

public import KhanSL2.Collision.Reduction
public import KhanSL2.Conditional.Assembly

@[expose] public section

namespace KhanSL2.Collision

/-- Factorization of the actual relative homology on coprime polynomial charts
implies the original isomorphism statement for the specified map `KhanSL2.phi`. -/
theorem mainStatement_of_kFactor (hK : ∀ B, KFactor B) : KhanSL2.MainStatement :=
  Conditional.mainStatement_of_collisionSupport (collisionSupportStep_of_kFactor hK)

end KhanSL2.Collision
