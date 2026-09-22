import ASL5RawLocality

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

namespace Grad.AxisSourceLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.AxisSplit Grad.ChartAxisLift Grad.PhysicalCoordinates
open Grad.Q24Realization Grad.RealFixedRanges Grad.ConstrainedTransfer

variable {parameters : PhaseParameters}

theorem capAffineField_firstOutsideZero (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters) :
    FirstOutsideEqual (radius / 2)
      (capAffineField parameters radius positive seed inside coefficient tangent) 0 := by
  constructor
  · intro cell point outside
    change ((capAffineField parameters radius positive seed inside coefficient tangent).val cell).value point = 0
    exact capAffineField_zero_outside radius positive seed inside coefficient tangent cell point outside
  · intro direction cell point outside
    change partialCoefficient direction
      ((capAffineField parameters radius positive seed inside coefficient tangent).val cell) point = _
    rw [capAffineField_partial_zero radius positive seed inside coefficient tangent cell direction point outside,
      map_zero, map_zero]

theorem capScalarAffine_firstOutsideZero (radius : ℝ) (positive : 0 < radius)
    (sigma : TangentCoefficient parameters) :
    FirstOutsideEqual (radius / 2) (capScalarAffine parameters radius positive sigma) 0 := by
  constructor
  · intro cell point outside
    change ((capScalarAffine parameters radius positive sigma).val cell).value point = 0
    exact capScalarAffine_zero_outside radius positive sigma cell point outside
  · intro direction cell point outside
    change partialCoefficient direction ((capScalarAffine parameters radius positive sigma).val cell) point = _
    rw [capScalarAffine_partial_zero radius positive sigma cell direction point outside, map_zero, map_zero]

theorem physicalFixedReferenceTransfer_smoothing
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (direction : stateSmoothRange parameters reference insideR) :
    physicalFixedReferenceTransfer parameters reference insideR seed insideS
      (smoothingChartCore parameters direction.val) =
      physicalChartState parameters (smoothingChartCore parameters
        (constrainedCoreTransfer parameters reference insideR seed insideS direction).val) := by
  rw [constrainedCoreTransfer_coe, coreTransfer_apply]
  rfl

/-- The literal first reference-family input of the actual cap lift. Its
transferred physical vector is chi Q_b y, not the chart remainder. -/
theorem physicalFixedReferenceFamily_referenceCapLift
    (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (sigma tangent : TangentCoefficient parameters) (realS : RealTangent sigma) (realT : RealTangent tangent) :
    physicalFixedReferenceFamily parameters reference insideR seed insideS 1
      (realJointCoreToJoint parameters reference insideR base)
      (fun _ => realJointCoreToJoint parameters reference insideR
        (0, referenceCapLift parameters radius positive bounded reference insideR seed insideS base axis sigma tangent realS realT)) =
      (0, capAffineField parameters radius positive seed insideS
        (rootDerivativeFamily 1 (smoothingToTangent parameters base.2.val.1) (fun _ => tangent)) tangent,
        capScalarAffine parameters radius positive sigma) := by
  unfold physicalFixedReferenceFamily
  apply Prod.ext
  · rfl
  · change chartDerivativeFamily parameters seed insideS 1
      (physicalFixedReferenceTransfer parameters reference insideR seed insideS
        (smoothingChartCore parameters base.2.val))
      (fun _ => physicalFixedReferenceTransfer parameters reference insideR seed insideS
        (smoothingChartCore parameters
          (referenceCapLift parameters radius positive bounded reference insideR seed insideS base axis sigma tangent realS realT).val)) = _
    rw [physicalFixedReferenceTransfer_smoothing reference insideR seed insideS
      (referenceCapLift parameters radius positive bounded reference insideR seed insideS base axis sigma tangent realS realT),
      referenceCapLift_transfer]
    exact chartDerivative_actualCapLift radius positive seed insideS
      (physicalFixedReferenceTransfer parameters reference insideR seed insideS
        (smoothingChartCore parameters base.2.val)) sigma tangent

end Grad.AxisSourceLift
