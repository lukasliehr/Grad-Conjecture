import ANG12CompletedRotation

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace Grad.CircularHighWeak
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange Grad.BoundaryTrace
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.GaugeTransfer

/-- Literal R has the coefficient i m on every actual closed-disk orbit. -/
theorem angular_rotationJet (mode : ℤ) (field : ClosedJet 1) :
    angularClosedJet mode (rotationJet field) = (Complex.I * (mode : ℂ)) • angularClosedJet mode field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have periodic : field.value (rotatedPoint Real.pi point) = field.value (rotatedPoint (-Real.pi) point) := by
    have rotation := diskOrbit_periodic point (-Real.pi)
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at rotation
    exact congrArg field.value rotation
  have coefficient := angularCoefficient_derivative
    (fun angle => field.value (rotatedPoint angle point))
    (fun angle => (rotationJet field).value (rotatedPoint angle point))
    (orbitValue_continuous field point) (orbitValue_continuous (rotationJet field) point)
    (closedOrbit_hasDerivAt field point) periodic mode
  exact (orbitCoefficient_projection (rotationJet field) point mode).symm.trans
    (coefficient.trans (congrArg (fun value : ComplexEuclidean 1 => (Complex.I * (mode : ℂ)) • value)
      (orbitCoefficient_projection field point mode)))

theorem diskMode_rotation (mode : ℤ) (field : diskGrade) :
    diskMode mode (diskRotation field) = (Complex.I * (mode : ℂ)) • diskMode mode (diskBulk field) := by
  apply isClosed_property diskCoreInto_denseRange
    (isClosed_eq ((diskMode mode).continuous.comp diskRotation.continuous)
      ((show Continuous (fun _ : diskGrade => (Complex.I * (mode : ℂ))) from continuous_const).smul
        ((diskMode mode).continuous.comp diskBulk.continuous))) _ field
  intro core
  have left := (congrArg (diskMode mode) (diskRotation_core core)).trans
    ((diskMode_core mode (rotationJet core)).trans
      ((congrArg closedL2Core (angular_rotationJet mode core)).trans
        (closedL2Core.map_smul (Complex.I * (mode : ℂ)) (angularClosedJet mode core))))
  refine left.trans ?_
  exact congrArg (fun value : DiskL2 1 => (Complex.I * (mode : ℂ)) • value)
    ((diskMode_core mode core).symm.trans (congrArg (diskMode mode) (diskBulk_core core).symm))

theorem diskRotation_angular (mode : ℤ) (field : diskGrade) :
    diskRotation (diskAngularMode mode field) = (Complex.I * (mode : ℂ)) • diskMode mode (diskBulk field) := by
  apply diskFourierIsometry.injective
  apply lp.ext
  funext other
  change diskMode other (diskRotation (diskAngularMode mode field)) =
    diskMode other ((Complex.I * (mode : ℂ)) • diskMode mode (diskBulk field))
  have left := (diskMode_rotation other (diskAngularMode mode field)).trans
    (congrArg (fun value : DiskL2 1 => (Complex.I * (other : ℂ)) • diskMode other value)
      (diskAngularMode_bulk mode field))
  refine left.trans ?_
  rw [map_smul, diskMode_projection]
  by_cases same : other = mode
  · subst other
    rfl
  · rw [if_neg same, smul_zero, smul_zero]

theorem highRotation_coefficient (mode : ℤ) (field : highDiskGrade) :
    diskMode mode (highRotation field) = (Complex.I * (mode : ℂ)) • diskMode mode (highDiskBulk field) :=
  diskMode_rotation mode field.val

theorem highRotation_angular (mode : ℤ) (field : highDiskGrade) :
    highRotation (highDiskMode mode field) = (Complex.I * (mode : ℂ)) • diskMode mode (highDiskBulk field) :=
  diskRotation_angular mode field.val

end Grad.CircularHighWeak
