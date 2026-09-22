import PolarVectorAlgebra

noncomputable section

open Set MeasureTheory
open scoped ContDiff Interval

namespace Grad.Constraints

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Radial

/-- z when sign=1 and z-bar when sign=-1. -/
def signedComplexCoordinate (sign : ℝ) (point : SpatialPlane) : ℂ :=
  (point 0 : ℂ) + Complex.I * (sign : ℂ) * (point 1 : ℂ)

theorem signedComplexCoordinate_smooth (sign : ℝ) :
    ContDiff ℝ ∞ (signedComplexCoordinate sign) := by
  have castSmooth : ContDiff ℝ ∞ (fun value : ℝ => (value : ℂ)) := Complex.ofRealCLM.contDiff
  unfold signedComplexCoordinate
  fun_prop

def coordinateMultiplyJet {dimension : ℕ} (sign : ℝ) (field : ClosedJet dimension) :
    ClosedJet dimension :=
  globalClosedJet (fun point => signedComplexCoordinate sign point • smoothClosedExtension field point)
    ((signedComplexCoordinate_smooth sign).smul (smoothClosedExtension_smooth field))

theorem coordinateMultiplyJet_value {dimension : ℕ} (sign : ℝ) (field : ClosedJet dimension)
    (point : ClosedDisk) :
    (coordinateMultiplyJet sign field).value point = signedComplexCoordinate sign point.val • field.value point := by
  change signedComplexCoordinate sign point.val • smoothClosedExtension field point.val = _
  rw [smoothClosedExtension_value]

theorem complexCoordinate_rotated (angle : ℝ) (point : ClosedDisk) :
    signedComplexCoordinate 1 (rotatedPoint angle point).val =
      angularCharacter (-1) angle * signedComplexCoordinate 1 point.val := by
  simp [signedComplexCoordinate, rotatedPoint, planeRotation, angularCharacter_trig]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem conjugateCoordinate_rotated (angle : ℝ) (point : ClosedDisk) :
    signedComplexCoordinate (-1) (rotatedPoint angle point).val =
      angularCharacter 1 angle * signedComplexCoordinate (-1) point.val := by
  simp [signedComplexCoordinate, rotatedPoint, planeRotation, angularCharacter_trig]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem angular_coordinate_shift_general {dimension : ℕ} (sign : ℝ) (shift mode : ℤ)
    (transformation : ∀ angle (point : ClosedDisk),
      signedComplexCoordinate sign (rotatedPoint angle point).val =
        angularCharacter shift angle * signedComplexCoordinate sign point.val)
    (field : ClosedJet dimension) :
    angularClosedJet mode (coordinateMultiplyJet sign field) =
      coordinateMultiplyJet sign (angularClosedJet (mode + shift) field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [angularClosedJet_value, coordinateMultiplyJet_value, angularClosedJet_value]
  simp_rw [coordinateMultiplyJet_value, transformation]
  have integrand (angle : ℝ) :
      angularCharacter mode angle •
          ((angularCharacter shift angle * signedComplexCoordinate sign point.val) •
            field.value (rotatedPoint angle point)) =
        signedComplexCoordinate sign point.val •
          (angularCharacter (mode + shift) angle • field.value (rotatedPoint angle point)) := by
    simp only [← mul_smul, ← angularCharacter_mul]
    congr 1
    ring
  simp_rw [integrand]
  rw [intervalIntegral.integral_smul, smul_comm]

/-- N5, with the exact negative-character convention in N1. -/
theorem angularClosedJet_z {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension) :
    angularClosedJet mode (coordinateMultiplyJet 1 field) =
      coordinateMultiplyJet 1 (angularClosedJet (mode - 1) field) := by
  simpa only [sub_eq_add_neg] using
    angular_coordinate_shift_general 1 (-1) mode complexCoordinate_rotated field

theorem angularClosedJet_zbar {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension) :
    angularClosedJet mode (coordinateMultiplyJet (-1) field) =
      coordinateMultiplyJet (-1) (angularClosedJet (mode + 1) field) :=
  angular_coordinate_shift_general (-1) 1 mode conjugateCoordinate_rotated field

end Grad.Constraints
