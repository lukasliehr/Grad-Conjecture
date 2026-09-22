import QYP18PhysicalPrimitiveDerivatives
import AXC7ExtractionConsumer

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.PhysicalCoordinates

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.Q24Realization Grad.RealFixedRanges Grad.AxisSplit Grad.ChartAxisSplit

variable {parameters : PhaseParameters}

theorem physicalFixedSliceDerivative_one (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base direction : JointState parameters) :
    physicalFixedSliceDerivative parameters cellLength reference insideR seed insideS 1 base (fun _ => direction) =
      quotientRowsDerivative parameters cellLength 1
        (physicalReferenceState parameters reference insideR seed insideS base)
        (fun _ => physicalFixedReferenceFamily parameters reference insideR seed insideS 1 base (fun _ => direction)) := by
  unfold physicalFixedSliceDerivative
  rw [composedDerivative_one, physicalFixedReferenceFamily_zero]
  congr 1
  funext index
  fin_cases index
  rfl

theorem physicalReferenceState_realCore_origin_zero
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR) (cell : ℤ) :
    originValue ((stateField (physicalReferenceState parameters reference insideR seed insideS
      (realJointCoreToJoint parameters reference insideR base))).val cell) = 0 := by
  apply normalizedChart_origin_zero
  exact toPhysicalCore_zeroJets parameters _
    (Gauges.seedTransfer_zero_first_jets parameters reference insideR seed insideS base.2.val.2.1
      (Grad.ConstrainedTransfer.smoothState_constraints parameters reference insideR base.2).1.1)

theorem physicalFixedReferenceFamily_realCore_origin_zero
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (direction : stateSmoothRange parameters reference insideR) (cell : ℤ) :
    originValue ((stateField (physicalFixedReferenceFamily parameters reference insideR seed insideS 1
      (realJointCoreToJoint parameters reference insideR base)
      (fun _ => realJointCoreToJoint parameters reference insideR (0, direction)))).val cell) = 0 := by
  apply chartDerivative_one_origin_zero
  exact toPhysicalCore_zeroJets parameters _
    (Gauges.seedTransfer_zero_first_jets parameters reference insideR seed insideS direction.val.2.1
      (Grad.ConstrainedTransfer.smoothState_constraints parameters reference insideR direction).1.1)

theorem physicalFixedReferenceFamily_realCore_kappa
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (direction : stateSmoothRange parameters reference insideR) :
    kappaDirection (physicalFixedReferenceFamily parameters reference insideR seed insideS 1
      (realJointCoreToJoint parameters reference insideR base)
      (fun _ => realJointCoreToJoint parameters reference insideR (0, direction))) =
      chartKappa parameters reference insideR direction := by
  apply Prod.ext
  · rfl
  · funext cell
    apply chartDerivative_one_tangential_gradient
    exact toPhysicalCore_zeroJets parameters _
      (Gauges.seedTransfer_zero_first_jets parameters reference insideR seed insideS direction.val.2.1
        (Grad.ConstrainedTransfer.smoothState_constraints parameters reference insideR direction).1.1)

/-- Physical AL11 with the corrected storage permutation retained in both
the actual base chart and its actual first direction. -/
theorem axisExtraction_physicalFirstRows (cellLength : ℝ) (positive : 0 < cellLength)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (direction : stateSmoothRange parameters reference insideR) :
    axisExtraction cellLength (quotientRowsDerivative parameters cellLength 1
      (physicalReferenceState parameters reference insideR seed insideS
        (realJointCoreToJoint parameters reference insideR base))
      (fun _ => physicalFixedReferenceFamily parameters reference insideR seed insideS 1
        (realJointCoreToJoint parameters reference insideR base)
        (fun _ => realJointCoreToJoint parameters reference insideR (0, direction)))) =
      chartKappa parameters reference insideR direction := by
  have singleton (value : QuotientState parameters) : ![value] = (fun _ : Fin 1 => value) := by
    funext index
    fin_cases index
    rfl
  have step := axisExtraction_linearization cellLength positive _ _
    (physicalReferenceState_realCore_origin_zero reference insideR seed insideS base)
    (physicalFixedReferenceFamily_realCore_origin_zero reference insideR seed insideS base direction)
  rw [singleton] at step
  exact step.trans (physicalFixedReferenceFamily_realCore_kappa reference insideR seed insideS base direction)

end Grad.PhysicalCoordinates
