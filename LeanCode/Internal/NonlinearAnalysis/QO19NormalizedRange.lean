import QO18ChartReality
import QS5Consumer

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 800000

open scoped ComplexConjugate BigOperators

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.CompletedReality Grad.QuotientProjection
open Grad.AxisJet Grad.AxisSplit Grad.RealFixedRanges

variable {parameters : PhaseParameters}

theorem traceZero_eq_of_coreValue_origin {dimension : ℕ} {first second : ACore parameters dimension}
    (equalValues : ∀ angle, coreValue first originPoint angle = coreValue second originPoint angle) :
    traceZero first = traceZero second := by
  apply Subtype.ext
  have equality := axialSeries_ext (fun cell => (first.val cell).value originPoint)
    (fun cell => (second.val cell).value originPoint)
    (Gauges.originalValueNorm_summable parameters first originPoint)
    (Gauges.originalValueNorm_summable parameters second originPoint) equalValues
  exact equality

theorem normalizedChart_affineTrace_zero (cellLength : ℝ) (epsilon : ℂ)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) (state : ChartState parameters)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (state.2.1.val cell))
    (real : RealTangent state.1) (axis : ChartAxisCondition state) :
    affineTrace parameters (quotientPolynomialRows parameters cellLength
      (epsilon, normalizedChart parameters seed inside state)) = 0 := by
  rw [quotientPolynomialRows_affineTrace]
  have traceTwo : traceZero
      (dotOperation parameters (partialCore parameters 0 (normalizedChart parameters seed inside state).1)
        (partialCore parameters 0 (normalizedChart parameters seed inside state).1) +
      dotOperation parameters (partialCore parameters 1 (normalizedChart parameters seed inside state).1)
        (partialCore parameters 1 (normalizedChart parameters seed inside state).1)) =
      traceZero (scalarConstantCore parameters 2) := by
    apply traceZero_eq_of_coreValue_origin
    intro angle
    rw [normalizedChart_traceTwo seed inside state zeroJets real axis]
    exact (coreValue_constant (EuclideanSpace.single 0 2) originPoint angle).symm
  change traceZero (scalarConstantCore parameters 1) - (1 / 2 : ℂ) •
    traceZero (dotOperation parameters (partialCore parameters 0 (normalizedChart parameters seed inside state).1)
      (partialCore parameters 0 (normalizedChart parameters seed inside state).1) +
      dotOperation parameters (partialCore parameters 1 (normalizedChart parameters seed inside state).1)
        (partialCore parameters 1 (normalizedChart parameters seed inside state).1)) = 0
  rw [traceTwo, scalarConstantCore_as_smul (parameters := parameters) 2, map_smul]
  module

/-- O21 for the literal normalized O14 quotient. Its mean, affine trace and
spin-reality laws are conclusions, not inserted projections or premises. -/
theorem normalizedQuotient_mem (cellLength : ℝ) (epsilon : ℝ)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) (state : ChartState parameters)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (state.2.1.val cell))
    (real : RealTangent state.1) (axis : ChartAxisCondition state)
    (vectorReal : cartesianCoreConjugation parameters state.2.1 = state.2.1)
    (scalarReal : cartesianCoreConjugation parameters state.2.2 = state.2.2)
    (scalarMean : angularCore parameters 0 state.2.2 = 0) :
    quotientPolynomialRows parameters cellLength
      ((epsilon : ℂ), normalizedChart parameters seed inside state) ∈ sourceSmoothRange parameters := by
  apply (mem_sourceSmoothRange parameters _).2
  constructor
  · apply quotientProjection_fixes
    refine ⟨quotientPolynomialRows_fourth_mean _ _, quotientPolynomialRows_third_mean _ _, ?_,
      normalizedChart_affineTrace_zero cellLength epsilon seed inside state zeroJets real axis⟩
    apply quotientPolynomialRows_mode_zero
    exact normalizedChart_mean_zero seed inside state scalarMean
  · have chartReal := normalizedChart_real seed inside state real axis vectorReal scalarReal
    exact quotientPolynomialRows_real cellLength _ (Complex.conj_ofReal epsilon) chartReal.1 chartReal.2

end Grad.NonlinearRange
