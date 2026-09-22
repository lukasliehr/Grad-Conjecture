import QO19NormalizedRange
import QW10Consumer
import TameFixedSliceInterface

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 800000

open scoped ComplexConjugate BigOperators

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.CompletedReality Grad.QuotientProjection
open Grad.RealFixedRanges

variable {parameters : PhaseParameters}

/-- The exact fixed-reference nonlinear quotient has its original real
compatible target. Gauges and the outer slice are not required by O21. -/
theorem fixedSliceMap_mem (cellLength : ℝ) (epsilon : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (state : ChartState parameters)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (state.2.1.val cell))
    (real : RealTangent state.1) (axis : ChartAxisCondition state)
    (vectorReal : cartesianCoreConjugation parameters state.2.1 = state.2.1)
    (scalarReal : cartesianCoreConjugation parameters state.2.2 = state.2.2)
    (scalarMean : angularCore parameters 0 state.2.2 = 0) :
    fixedSliceMap parameters cellLength reference insideR seed insideS ((epsilon : ℂ), state) ∈
      sourceSmoothRange parameters := by
  apply normalizedQuotient_mem
  · exact Gauges.seedTransfer_zero_first_jets parameters reference insideR seed insideS state.2.1 zeroJets
  · exact real
  · exact axis
  · change cartesianCoreConjugation parameters
      (Gauges.seedTransfer parameters reference insideR seed insideS state.2.1) = _
    rw [Grad.ConstrainedTransfer.seedTransfer_conjugate, vectorReal]
    rfl
  · exact scalarReal
  · exact scalarMean

/-- Full O21: literal normalized O14 and the literal fixed-reference Q21
map are simultaneously fixed by the original quotient projection and the
actual swapped real involution. Normalization and target membership are
proved from original input constraints, never supplied as hypotheses. -/
def NormalizedRangeGoal : Prop :=
  ∀ (parameters : PhaseParameters) (cellLength epsilon : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (state : ChartState parameters),
    (∀ cell, ZeroCartesianFirstJets (state.2.1.val cell)) →
    RealTangent state.1 → ChartAxisCondition state →
    cartesianCoreConjugation parameters state.2.1 = state.2.1 →
    cartesianCoreConjugation parameters state.2.2 = state.2.2 →
    angularCore parameters 0 state.2.2 = 0 →
      quotientPolynomialRows parameters cellLength
        ((epsilon : ℂ), normalizedChart parameters seed insideS state) ∈ sourceSmoothRange parameters ∧
      fixedSliceMap parameters cellLength reference insideR seed insideS ((epsilon : ℂ), state) ∈
        sourceSmoothRange parameters

theorem actualNormalizedRange : NormalizedRangeGoal := by
  intro parameters cellLength epsilon reference insideR seed insideS state zeroJets real axis vectorReal scalarReal scalarMean
  exact ⟨normalizedQuotient_mem cellLength epsilon seed insideS state zeroJets real axis vectorReal scalarReal scalarMean,
    fixedSliceMap_mem cellLength epsilon reference insideR seed insideS state zeroJets real axis vectorReal scalarReal scalarMean⟩

end Grad.NonlinearRange
