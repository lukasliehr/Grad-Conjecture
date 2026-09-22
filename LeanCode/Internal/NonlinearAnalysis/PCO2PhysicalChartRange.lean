import PCO1PhysicalCoordinates
import QO21ConstrainedConsumer
import Q24RealDomain

noncomputable section

namespace Grad.PhysicalCoordinates

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.CompletedReality Grad.NonlinearRange
open Grad.RealFixedRanges Grad.Q24Realization Grad.QuotientProjection

/-- Interpret only the stored vector slot physically; free axis and scalar
coordinates retain their exact original meaning. -/
def physicalChartState (parameters : PhaseParameters) :
    ChartState parameters →ₗ[ℂ] ChartState parameters :=
  LinearMap.id.prodMap ((toPhysicalCore parameters).prodMap LinearMap.id)

theorem physicalChartState_apply (parameters : PhaseParameters) (state : ChartState parameters) :
    physicalChartState parameters state = (state.1, toPhysicalCore parameters state.2.1, state.2.2) := rfl

theorem physicalChartState_norm (parameters : PhaseParameters) (grade : ℕ) (state : ChartState parameters) :
    chartStateNorm grade (physicalChartState parameters state) = chartStateNorm grade state := by
  change tangentNorm (grade + 1) state.1 + originalGradeNorm grade (toPhysicalCore parameters state.2.1) +
    originalGradeNorm grade state.2.2 = _
  rw [toPhysicalCore_norm]
  rfl

/-- Correct fixed-reference physical chart, using accepted N18 in its
storage coordinates and the explicit physical isometry afterwards. -/
def physicalReferenceState (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (state : JointState parameters) : QuotientState parameters :=
  (state.1, normalizedChart parameters seed insideS
    (physicalChartState parameters (referenceTransfer parameters reference insideR seed insideS state.2)))

def physicalFixedSliceMap (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (state : JointState parameters) : QuotientRows parameters :=
  quotientPolynomialRows parameters cellLength
    (physicalReferenceState parameters reference insideR seed insideS state)

theorem physicalReferenceState_formula (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (state : JointState parameters) :
    physicalReferenceState parameters reference insideR seed insideS state =
      (state.1, normalizedChart parameters seed insideS
        (state.2.1, toPhysicalCore parameters
          (Gauges.seedTransfer parameters reference insideR seed insideS state.2.2.1), state.2.2.2)) := rfl

/-- Physical O21: no target projection is inserted. All actual source
constraints follow from the original zero jets, reality and scalar gauge. -/
theorem physicalFixedSliceMap_mem (parameters : PhaseParameters) (cellLength epsilon : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (state : ChartState parameters)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (state.2.1.val cell))
    (real : RealTangent state.1) (axis : ChartAxisCondition state)
    (vectorReal : cartesianCoreConjugation parameters state.2.1 = state.2.1)
    (scalarReal : cartesianCoreConjugation parameters state.2.2 = state.2.2)
    (scalarMean : angularCore parameters 0 state.2.2 = 0) :
    physicalFixedSliceMap parameters cellLength reference insideR seed insideS ((epsilon : ℂ), state) ∈
      sourceSmoothRange parameters := by
  apply normalizedQuotient_mem
  · exact toPhysicalCore_zeroJets parameters _
      (Gauges.seedTransfer_zero_first_jets parameters reference insideR seed insideS state.2.1 zeroJets)
  · exact real
  · exact axis
  · change cartesianCoreConjugation parameters (toPhysicalCore parameters
      (Gauges.seedTransfer parameters reference insideR seed insideS state.2.1)) = _
    rw [toPhysicalCore_conjugate, Grad.ConstrainedTransfer.seedTransfer_conjugate, vectorReal]
    rfl
  · exact scalarReal
  · exact scalarMean

/-- Exact canonical constrained-core consumer of the corrected physical map. -/
theorem physicalFixedSliceMap_constrained_mem (parameters : PhaseParameters) (cellLength epsilon : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (state : stateSmoothRange parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters state.val)) :
    physicalFixedSliceMap parameters cellLength reference insideR seed insideS
      ((epsilon : ℂ), smoothingChartCore parameters state.val) ∈ sourceSmoothRange parameters := by
  have constraints := Grad.ConstrainedTransfer.smoothState_constraints parameters reference insideR state
  obtain ⟨real, vectorReal, scalarReal⟩ := stateChart_real parameters reference insideR state
  exact physicalFixedSliceMap_mem parameters cellLength epsilon reference insideR seed insideS _
    constraints.1.1 real axis vectorReal scalarReal constraints.2

theorem physicalFixedSliceMap_constrained_grade_mem (parameters : PhaseParameters) (cellLength epsilon : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 3 ≤ grade) (state : stateSmoothRange parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters state.val)) :
    quotientEta parameters grade (physicalFixedSliceMap parameters cellLength reference insideR seed insideS
      ((epsilon : ℂ), smoothingChartCore parameters state.val)) ∈ sourceRange parameters grade large :=
  (quotientEta_mem_iff parameters grade large _).2
    (physicalFixedSliceMap_constrained_mem parameters cellLength epsilon reference insideR seed insideS state axis)

end Grad.PhysicalCoordinates
