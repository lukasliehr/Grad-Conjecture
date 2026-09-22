import ANH6CirclePoincare
import GQ3RotationCore

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.CircularHighWeak

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.PhysicalFamily Grad.NonlinearRange

theorem diskOrbit_periodic (point : ClosedDisk) :
    Function.Periodic (fun angle => rotatedPoint angle point) (2 * Real.pi) := by
  intro angle
  apply Subtype.ext
  change planeRotation (angle + 2 * Real.pi) point.val = planeRotation angle point.val
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [planeRotation]

theorem orbitValue_continuous {dimension : ℕ} (field : ClosedJet dimension) (point : ClosedDisk) :
    Continuous (fun angle => field.value (rotatedPoint angle point)) :=
  continuous_iff_continuousAt.2 (fun angle => (closedOrbit_hasDerivAt field point angle).continuousAt)

theorem orbitCoefficient_projection {dimension : ℕ} (field : ClosedJet dimension)
    (point : ClosedDisk) (mode : ℤ) :
    angularCoefficient (fun angle => field.value (rotatedPoint angle point)) mode =
      (angularClosedJet mode field).value point := by
  rw [angularCoefficient_integral, angularClosedJet_value]
  have character (angle : ℝ) : fourier (-mode) (angle : CellCircle) = angularCharacter mode angle :=
    cellCharacter_coe _ _
  simp_rw [character]
  change (2 * Real.pi)⁻¹ • (∫ angle in -Real.pi..Real.pi,
    angularCharacter mode angle • field.value (rotatedPoint angle point)) = _
  have periodic : Function.Periodic
      (fun angle => angularCharacter mode angle • field.value (rotatedPoint angle point))
      (2 * Real.pi) := by
    intro angle
    change angularCharacter mode (angle + 2 * Real.pi) •
      field.value (rotatedPoint (angle + 2 * Real.pi) point) =
        angularCharacter mode angle • field.value (rotatedPoint angle point)
    have rotation := diskOrbit_periodic point angle
    change rotatedPoint (angle + 2 * Real.pi) point = rotatedPoint angle point at rotation
    rw [angularCharacter_periodic, rotation]
  have shifted := periodic.intervalIntegral_add_eq (-Real.pi) 0
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at shifted
  exact congrArg (fun value : ComplexEuclidean dimension => (2 * Real.pi)⁻¹ • value) shifted

theorem excludedAngularJet_low_zero {dimension : ℕ} (field : ClosedJet dimension)
    (mode : ℤ) (low : mode ∈ lowAngularModes) :
    angularClosedJet mode (excludedAngularJet lowAngularModes field) = 0 := by
  change angularClosedJetLinear dimension mode
    (field - selectedAngularJet lowAngularModes field) = 0
  rw [map_sub]
  change angularClosedJet mode field - angularClosedJet mode (selectedAngularJet lowAngularModes field) = 0
  rw [angularClosedJet_selected, if_pos low, sub_self]

/-- Exact high-mode estimate on every orbit of the whole closed disk,
including its axis. The low-mode premise is discharged by the actual projector. -/
theorem highCore_orbit_poincare {dimension : ℕ} (field : ClosedJet dimension) (point : ClosedDisk) :
    9 * (∫ angle in -Real.pi..Real.pi,
      ‖(excludedAngularJet lowAngularModes field).value (rotatedPoint angle point)‖ ^ 2) ≤
      ∫ angle in -Real.pi..Real.pi,
        ‖(rotationJet (excludedAngularJet lowAngularModes field)).value (rotatedPoint angle point)‖ ^ 2 := by
  apply circle_high_poincare _ _
    (orbitValue_continuous _ point) (orbitValue_continuous _ point)
    (closedOrbit_hasDerivAt _ point)
  · have periodic := diskOrbit_periodic point (-Real.pi)
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at periodic
    exact congrArg (fun other => (excludedAngularJet lowAngularModes field).value other) periodic
  · intro mode low
    rw [orbitCoefficient_projection, excludedAngularJet_low_zero field mode low]
    rfl

end Grad.CircularHighWeak
