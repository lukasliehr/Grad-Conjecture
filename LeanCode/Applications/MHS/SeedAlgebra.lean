import SeedInterface

noncomputable section

namespace Grad.Constraints.Seed

open Grad.GeometryClosure

theorem actualSeedAlgebra : AlgebraGoal := by
  intro parameter admissible angle
  change |parameter 0| < 1 at admissible
  have interval := abs_lt.mp admissible
  have traces := seed_trace interval.1 interval.2
    (seedAngle (parameter 1) (parameter 2) (parameter 3) angle)
  have determinant := seed_det interval.1 interval.2
    (seedAngle (parameter 1) (parameter 2) (parameter 3) angle)
  have inverses := seed_inverse_identities interval.1 interval.2
    (seedAngle (parameter 1) (parameter 2) (parameter 3) angle)
  exact ⟨traces.1, determinant.1, determinant.2, inverses.2, inverses.1⟩

end Grad.Constraints.Seed
