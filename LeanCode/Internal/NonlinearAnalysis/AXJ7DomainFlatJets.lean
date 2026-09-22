import AXJ6ChartFlatJets

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.ChartAxisProjections

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.ChartAxisLift
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.ChartAxisSplit
open Grad.Q24Realization Grad.RealFixedRanges Grad.PhysicalCoordinates

variable {parameters : PhaseParameters}

theorem realChartKappa_eq_zero_iff (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (direction : stateSmoothRange parameters reference insideR) :
    realChartKappa parameters reference insideR direction = 0 ↔
      smoothingToTangent parameters direction.val.1 = 0 ∧
        ∀ cell, scalarOriginGradient direction.val.2.2 cell = 0 := by
  constructor
  · intro zero
    constructor
    · apply Subtype.ext
      funext cell
      exact congrArg (fun data : RealAxis parameters => data.val.2.val cell) zero
    · intro cell
      exact congrArg (fun data : RealAxis parameters => data.val.1.val cell) zero
  · intro ⟨tangentZero, gradientZero⟩
    apply Subtype.ext
    apply axisData_ext
    apply Prod.ext
    · exact funext gradientZero
    · exact congrArg Subtype.val tangentZero

/-- AL24 for the actual first physical fixed-reference variation. Both
field values and both first derivatives vanish precisely in ker kappa. -/
theorem realDomainFlat_iff_jets
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (direction : stateSmoothRange parameters reference insideR) :
    direction ∈ LinearMap.ker (realChartKappa parameters reference insideR) ↔
      ∀ cell, ZeroCartesianFirstJets
          ((stateField (physicalFixedReferenceFamily parameters reference insideR seed insideS 1
            (realJointCoreToJoint parameters reference insideR base)
            (fun _ => realJointCoreToJoint parameters reference insideR (0, direction)))).val cell) ∧
        ZeroCartesianFirstJets
          ((statePotential (physicalFixedReferenceFamily parameters reference insideR seed insideS 1
            (realJointCoreToJoint parameters reference insideR base)
            (fun _ => realJointCoreToJoint parameters reference insideR (0, direction)))).val cell) := by
  let baseChart := physicalFixedReferenceTransfer parameters reference insideR seed insideS
    (smoothingChartCore parameters base.2.val)
  let directionChart := physicalFixedReferenceTransfer parameters reference insideR seed insideS
    (smoothingChartCore parameters direction.val)
  have zeroJets : ∀ cell, ZeroCartesianFirstJets (directionChart.2.1.val cell) :=
    toPhysicalCore_zeroJets parameters _
      (Gauges.seedTransfer_zero_first_jets parameters reference insideR seed insideS direction.val.2.1
        (Grad.ConstrainedTransfer.smoothState_constraints parameters reference insideR direction).1.1)
  have mean : angularCore parameters 0 directionChart.2.2 = 0 :=
    (Grad.ConstrainedTransfer.smoothState_constraints parameters reference insideR direction).2
  have criterion := chartFlat_iff_jets seed insideS baseChart directionChart zeroJets mean
  change realChartKappa parameters reference insideR direction = 0 ↔ _
  rw [realChartKappa_eq_zero_iff]
  exact criterion

end Grad.ChartAxisProjections
