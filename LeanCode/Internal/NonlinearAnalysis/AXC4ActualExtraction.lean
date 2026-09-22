import AXC3TangentialTrace

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ChartAxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit Grad.Q24Realization Grad.SmoothForward
open Grad.NonlinearRange Grad.RealFixedRanges

variable {parameters : PhaseParameters}

theorem zeroJets_origin {dimension : ℕ} (field : ACore parameters dimension)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.val cell)) (cell : ℤ) :
    originValue (field.val cell) = 0 := by
  have value := zeroJets cell 0 (by omega) emptyCartesianWord
  rw [closedDerivative_zero_order] at value
  convert value using 1
  rfl

theorem normalizedChart_origin_zero (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (state : ChartState parameters) (zeroJets : ∀ cell, ZeroCartesianFirstJets (state.2.1.val cell))
    (cell : ℤ) : originValue (((normalizedChart parameters seed inside state).1).val cell) = 0 :=
  chartAffineField_origin_zero seed inside _ _ _ (zeroJets_origin _ zeroJets) cell

theorem chartDerivative_one_origin_zero (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (base direction : ChartState parameters)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (direction.2.1.val cell)) (cell : ℤ) :
    originValue (((chartDerivativeFamily parameters seed inside 1 base (fun _ => direction)).1).val cell) = 0 :=
  chartAffineField_origin_zero seed inside _ _ _ (zeroJets_origin _ zeroJets) cell

theorem chartDerivative_one_tangential_gradient (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (base direction : ChartState parameters)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (direction.2.1.val cell)) (cell : ℤ) :
    tangentialOriginGradient (chartDerivativeFamily parameters seed inside 1 base (fun _ => direction)).1 cell =
      direction.1.val cell :=
  chartAffineField_tangential_gradient seed inside _ _ _ zeroJets cell

def chartKappa (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain)
    (direction : stateSmoothRange parameters reference insideR) :
    (ℤ → ComplexEuclidean 2) × (ℤ → ComplexEuclidean 2) :=
  (scalarOriginGradient direction.val.2.2, direction.val.1.val)

theorem referenceState_realCore_origin_zero
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR) (cell : ℤ) :
    originValue ((stateField (referenceState parameters reference insideR seed insideS
      (realJointCoreToJoint parameters reference insideR base))).val cell) = 0 := by
  apply normalizedChart_origin_zero
  exact Gauges.seedTransfer_zero_first_jets parameters reference insideR seed insideS base.2.val.2.1
    (Grad.ConstrainedTransfer.smoothState_constraints parameters reference insideR base.2).1.1

theorem referenceFamily_realCore_origin_zero
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (direction : stateSmoothRange parameters reference insideR) (cell : ℤ) :
    originValue ((stateField (referenceFamily parameters reference insideR seed insideS 1
      (realJointCoreToJoint parameters reference insideR base)
      (fun _ => realJointCoreToJoint parameters reference insideR (0, direction)))).val cell) = 0 := by
  apply chartDerivative_one_origin_zero
  exact Gauges.seedTransfer_zero_first_jets parameters reference insideR seed insideS direction.val.2.1
    (Grad.ConstrainedTransfer.smoothState_constraints parameters reference insideR direction).1.1

theorem referenceFamily_realCore_kappa
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (direction : stateSmoothRange parameters reference insideR) :
    kappaDirection (referenceFamily parameters reference insideR seed insideS 1
      (realJointCoreToJoint parameters reference insideR base)
      (fun _ => realJointCoreToJoint parameters reference insideR (0, direction))) =
      chartKappa parameters reference insideR direction := by
  apply Prod.ext
  · rfl
  · funext cell
    apply chartDerivative_one_tangential_gradient
    exact Gauges.seedTransfer_zero_first_jets parameters reference insideR seed insideS direction.val.2.1
      (Grad.ConstrainedTransfer.smoothState_constraints parameters reference insideR direction).1.1

/-- AL11 for the actual fixed-reference normalized chart derivative. The
root derivative's transverse first jet is retained; only its tangential
component is zero. No affine chart direction has been removed. -/
theorem axisExtraction_literalSmoothForward (cellLength : ℝ) (positive : 0 < cellLength)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (direction : stateSmoothRange parameters reference insideR) :
    axisExtraction cellLength (literalSmoothForwardRows parameters cellLength reference insideR seed insideS base direction) =
      chartKappa parameters reference insideR direction := by
  unfold literalSmoothForwardRows
  rw [fixedSliceDerivative_one, axisExtraction_linearization cellLength positive _ _
    (referenceState_realCore_origin_zero reference insideR seed insideS base)
    (referenceFamily_realCore_origin_zero reference insideR seed insideS base direction)]
  exact referenceFamily_realCore_kappa reference insideR seed insideS base direction

end Grad.ChartAxisSplit
