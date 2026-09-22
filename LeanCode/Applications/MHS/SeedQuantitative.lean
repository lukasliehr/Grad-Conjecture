import SeedInverseBounds

noncomputable section

open scoped BigOperators

namespace Grad.Constraints.Seed

open Grad.CartesianState Grad.GaugeCoefficients.Physical.Frame

theorem actualSeedQuantitative : QuantitativeGoal := by
  intro phase grade eccentricity radius nonnegative small radiusNonnegative
  let constant := envelopeComparison phase grade *
    (seedDeviationConstant phase.sigma0 radius grade +
      inverseDeviationConstant phase grade eccentricity radius +
      seedDerivativeConstant phase.sigma0 radius grade)
  have inverseNonnegative : 0 ≤ inverseDeviationConstant phase grade eccentricity radius := by
    unfold inverseDeviationConstant inverseDeterminant
    exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (add_nonneg (seedDeviationConstant_nonnegative _ _ _) (Nat.cast_nonneg _))
  refine ⟨constant, mul_nonneg (envelopeComparison_nonnegative phase grade)
    (add_nonneg (add_nonneg (seedDeviationConstant_nonnegative _ _ _) inverseNonnegative)
      (seedDerivativeConstant_nonnegative _ _ _)), ?_⟩
  intro parameter rhoBound otherSmall
  have first := actual_deviation_bound phase grade radiusNonnegative parameter (rhoBound.trans small.le) otherSmall
  have second := actual_inverse_bound phase grade nonnegative small radiusNonnegative parameter rhoBound otherSmall
  have third := actual_derivative_bound phase grade radiusNonnegative parameter (rhoBound.trans small.le) otherSmall
  constructor
  · intro kind
    fin_cases kind
    · exact first.1
    · exact second.1
    · exact third.1
  · rw [Fin.sum_univ_three]
    exact (add_le_add (add_le_add first.2 second.2) third.2).trans_eq (by dsimp [constant]; ring)

end Grad.Constraints.Seed
