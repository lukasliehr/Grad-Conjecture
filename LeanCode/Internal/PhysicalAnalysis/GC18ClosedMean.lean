import GC18CircleNormalization
import RotationAverageAlgebra

noncomputable section

set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped Topology BigOperators Interval

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.NonlinearDivision
open Grad.Constraints Grad.PhysicalFamily

def closedFieldExtension {Target : Type} [Zero Target] (field : ClosedDisk → Target)
    (point : SpatialPlane) : Target := by
  classical
  exact if inside : point ∈ closedUnitDisk then field ⟨point, inside⟩ else 0

theorem closedFieldExtension_value {Target : Type} [Zero Target]
    (field : ClosedDisk → Target) (point : ClosedDisk) :
    closedFieldExtension field point.val = field point := by
  simp only [closedFieldExtension, dif_pos point.property]

def closedAngularMean {Target : Type} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (field : ClosedDisk → Target) (point : ClosedDisk) : Target :=
  ∫ time in Icc (0 : ℝ) 1,
    field (Grad.GaugeCoefficients.Radial.rotatedPoint (2 * Real.pi * time) point)

theorem closedAngularMean_eq_rotationAverage {Target : Type}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target] [CompleteSpace Target]
    (field : ClosedDisk → Target) (point : ClosedDisk) :
    closedAngularMean field point = rotationAverage (closedFieldExtension field) point.val := by
  rw [closedAngularMean, normalizedAngularIntegral
    (fun angle => field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)),
    rotationAverage_eq_compactIntegral]
  congr 1
  apply integral_congr_ae
  filter_upwards with angle
  have identity := closedFieldExtension_value field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)
  simpa only [physicalRotation_eq_orthogonal, planeRotationEquiv_apply,
    Grad.GaugeCoefficients.Radial.rotatedPoint] using identity.symm

theorem closedAngularMean_rotation {Target : Type}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target] [CompleteSpace Target]
    (field : ClosedDisk → Target) (rotation : ℝ) (point : ClosedDisk) :
    closedAngularMean field (Grad.GaugeCoefficients.Radial.rotatedPoint rotation point) =
      closedAngularMean field point := by
  rw [closedAngularMean_eq_rotationAverage, closedAngularMean_eq_rotationAverage]
  have identity := rotationAverage_rotation (closedFieldExtension field) rotation point.val
  simpa only [physicalRotation_eq_orthogonal, planeRotationEquiv_apply,
    Grad.GaugeCoefficients.Radial.rotatedPoint] using identity

theorem angularFamily_physical_rotation {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (grade : ℕ) (angle rotation : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (angularFamily family grade) angle
        (Grad.GaugeCoefficients.Radial.rotatedPoint rotation point) =
      coefficientPhysicalValue (angularFamily family grade) angle point := by
  simp_rw [angularFamily_physicalValue admissible family coherent]
  exact closedAngularMean_rotation (fun point => coefficientPhysicalValue (family grade) angle point) rotation point

/-- IΔΠ is genuinely radial after full Fourier realization, at the axis
as well as off it. This follows from the proved division identity. -/
theorem radialDivisionFamily_physical_rotation {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (grade : ℕ) (angle rotation : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (radialDivisionFamily admissible family grade) angle
        (Grad.GaugeCoefficients.Radial.rotatedPoint rotation point) =
      coefficientPhysicalValue (radialDivisionFamily admissible family grade) angle point := by
  by_cases axis : point.val = 0
  · have pointOrigin : point = closedOrigin := Subtype.ext axis
    rw [pointOrigin, radialRotatedPoint_origin]
  · have identity := radialDivisionFamily_physical_identity admissible family coherent grade angle point
    have rotated := radialDivisionFamily_physical_identity admissible family coherent grade angle
      (Grad.GaugeCoefficients.Radial.rotatedPoint rotation point)
    rw [angularFamily_physical_rotation admissible family coherent, radialRotatedPoint_norm] at rotated
    have nonzero : ((‖point.val‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr axis))
    exact (smul_right_injective (OperatorValue input output) nonzero) (rotated.symm.trans identity)

end Grad.GaugeCoefficients.Physical.RadialLedger
