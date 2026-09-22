import GQ2ActualRanges
import QO17ScalarMean
import TangentialPolar

noncomputable section

set_option maxHeartbeats 1400000

open Set
open scoped ContDiff

namespace Grad.GaugeCoefficients.Physical.GaugeTransfer

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.PhysicalFamily
open Grad.GaugeCoefficients.Radial Grad.NonlinearRange

theorem closedOrbit_hasDerivAt {dimension : ℕ} (field : ClosedJet dimension) (point : ClosedDisk) (angle : ℝ) :
    HasDerivAt (fun time => field.value (rotatedPoint time point))
      ((rotationJet field).value (rotatedPoint angle point)) angle := by
  have outer := (((smoothClosedExtension_smooth field).differentiable (by simp)).differentiableAt
    (x := planeRotationAction angle point.val)).hasFDerivAt
  have composed := outer.comp_hasDerivAt angle (planeRotationAction_hasDerivAt point.val angle)
  have equalFunctions : (fun time => smoothClosedExtension field (planeRotationAction time point.val)) =
      (fun time => field.value (rotatedPoint time point)) := by
    funext time
    simpa only [rotatedPoint, physicalRotation_eq_orthogonal, planeRotationEquiv_apply] using
      smoothClosedExtension_value field (rotatedPoint time point)
  simp only [Function.comp_def] at composed
  rw [equalFunctions] at composed
  rw [rotationJet_extension_value]
  simpa only [rotatedPoint, physicalRotation_eq_orthogonal, planeRotationEquiv_apply] using composed

theorem rotatedPoint_zero (point : ClosedDisk) : rotatedPoint 0 point = point := by
  apply Subtype.ext
  change planeRotation 0 point.val = point.val
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [planeRotation]

theorem tangentialJet_average_fixed (field : ClosedJet 2) :
    equivariantAverageJet (tangentialJet field) = tangentialJet field := by
  rw [tangentialJet_eq, equivariantAverageJet_smul, equivariantAverageJet_sub,
    equivariantAverageJet_idempotent, ← reflectedVectorJet_average, equivariantAverageJet_idempotent]

theorem tangentialJet_rotation_value (field : ClosedJet 2) (angle : ℝ) (point : ClosedDisk) :
    (tangentialJet field).value (rotatedPoint angle point) =
      rotationValueMap angle ((tangentialJet field).value point) := by
  have identity := equivariantAverageJet_rotation_value (tangentialJet field) angle point
  simpa only [tangentialJet_average_fixed] using identity

theorem rotationValue_hasDerivAt_zero (value : ComplexEuclidean 2) :
    HasDerivAt (fun angle => rotationValueMap angle value) (quarterValueMap value) 0 := by
  have derivative := ((Real.hasDerivAt_cos 0).smul_const value).add
    ((Real.hasDerivAt_sin 0).smul_const (quarterValueMap value))
  have equality : (fun angle => rotationValueMap angle value) =
      ((fun angle : ℝ => Real.cos angle • value) +
        (fun angle : ℝ => Real.sin angle • quarterValueMap value)) := by
    funext angle
    simp only [Pi.add_apply, rotationValueMap, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, Complex.coe_smul]
  rw [equality]
  simpa only [Real.sin_zero, Real.cos_zero, neg_zero, zero_smul, one_smul, zero_add] using derivative

/-- Literal R(T0v)=J(T0v), including the axis, from the actual rotation
orbit and the Cartesian derivative of a genuine closed jet. -/
theorem rotationJet_tangential_value (field : ClosedJet 2) (point : ClosedDisk) :
    (rotationJet (tangentialJet field)).value point = quarterValueMap ((tangentialJet field).value point) := by
  have derivative := closedOrbit_hasDerivAt (tangentialJet field) point 0
  have equality : (fun angle => (tangentialJet field).value (rotatedPoint angle point)) =
      (fun angle => rotationValueMap angle ((tangentialJet field).value point)) :=
    funext (fun angle => tangentialJet_rotation_value field angle point)
  rw [equality, rotatedPoint_zero] at derivative
  exact derivative.unique (rotationValue_hasDerivAt_zero _)

theorem rotationJet_tangential (field : ClosedJet 2) :
    rotationJet (tangentialJet field) = valueMapJet quarterValueMap (tangentialJet field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [valueMapJet_value, rotationJet_tangential_value]

/-- Literal R(Pi t)=0 on the whole closed disk. -/
theorem rotationJet_angular_zero {dimension : ℕ} (field : ClosedJet dimension) :
    rotationJet (angularClosedJet 0 field) = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have derivative := closedOrbit_hasDerivAt (angularClosedJet 0 field) point 0
  have equality : (fun angle => (angularClosedJet 0 field).value (rotatedPoint angle point)) =
      (fun _ : ℝ => (angularClosedJet 0 field).value point) := by
    funext angle
    rw [angularClosedJet_rotation_value, angularCharacter_zero_mode, one_smul]
  rw [equality, rotatedPoint_zero] at derivative
  exact derivative.unique (hasDerivAt_const 0 _)

end Grad.GaugeCoefficients.Physical.GaugeTransfer
