import AKU55LiteralDeterminantFourierValue
import AKU58ActualAxisMetricAndAffine

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Physical.Ledger

theorem localizedAxisConstantCore_physical_axis {parameters : PhaseParameters} {dimension : ℕ}
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) (angle : ℝ) :
    coreValue (localizedAxisConstantCore data) closedOrigin angle = axisPhysicalValue data angle := by
  rw [← traceZero_physical,traceZero_localizedAxisConstantCore]

theorem originalLift_determinant_axis_first (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (potential : ACore parameters 1)
    (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (index : Fin 3) (angle : ℝ) :
    axisPhysicalValue (traceZero (determinantOperation parameters
      (localizedAxisConstantCore (originalLiftPhysicalUAxis parameters length rho epsilon field low source index))
      (partialCore parameters 1 (planarReferenceCore parameters+field))
      (affineStateCore parameters length ((epsilon : ℂ),planarReferenceCore parameters+field,potential)))) angle 0 =
      (-((length : ℂ)*(originalAxisPlanarMatrix parameters length epsilon field angle).det)) *
        axisPhysicalValue (originalLiftMetricAxis parameters length rho epsilon field low source index) angle 0 := by
  rw [traceZero_physical,coreValue_determinantOperation,localizedAxisConstantCore_physical_axis,
    ← traceFirst_physical,originalTotalFirstJet_frame parameters length epsilon field 1 angle,
    affineStateCore_actual_axis parameters length epsilon field potential vanishes angle,complexDeterminant_smul_third]
  have margin := originalCoefficient_low_margin parameters length rho epsilon field
    (originalCubic_low_margin parameters length rho epsilon field low).1
  change (length : ℂ) * Grad.NonlinearQuotient.complexDeterminant _
    (physicalColumn (originalPhysicalFrameMatrix parameters length epsilon field angle closedOrigin) 1)
    (physicalColumn (originalPhysicalFrameMatrix parameters length epsilon field angle closedOrigin) 2) = _
  have recovered : matrixOperator (familyMatrix (originalInverseFamily parameters length epsilon field) 0 angle closedOrigin)
      (axisPhysicalValue (originalLiftPhysicalUAxis parameters length rho epsilon field low source index) angle) (0 : Fin 3) =
      axisPhysicalValue (originalLiftMetricAxis parameters length rho epsilon field low source index) angle (0 : Fin 2) :=
    originalLiftPhysicalUAxis_inverse_planar parameters length rho epsilon field low source index 0 angle
  rw [determinant_replace_first _ _
    (originalInverseFamily_matrix_identity parameters length epsilon field margin.2.2 0 angle closedOrigin).1,
    recovered,
    originalAxis_frame parameters length epsilon field vanishes angle,tiltedAxisFrame_det]
  ring

theorem originalLift_determinant_axis_second (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (potential : ACore parameters 1)
    (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (index : Fin 3) (angle : ℝ) :
    axisPhysicalValue (traceZero (determinantOperation parameters
      (partialCore parameters 0 (planarReferenceCore parameters+field))
      (localizedAxisConstantCore (originalLiftPhysicalUAxis parameters length rho epsilon field low source index))
      (affineStateCore parameters length ((epsilon : ℂ),planarReferenceCore parameters+field,potential)))) angle 0 =
      (-((length : ℂ)*(originalAxisPlanarMatrix parameters length epsilon field angle).det)) *
        axisPhysicalValue (originalLiftMetricAxis parameters length rho epsilon field low source index) angle 1 := by
  rw [traceZero_physical,coreValue_determinantOperation,localizedAxisConstantCore_physical_axis,
    ← traceFirst_physical,originalTotalFirstJet_frame parameters length epsilon field 0 angle,
    affineStateCore_actual_axis parameters length epsilon field potential vanishes angle,complexDeterminant_smul_third]
  have margin := originalCoefficient_low_margin parameters length rho epsilon field
    (originalCubic_low_margin parameters length rho epsilon field low).1
  change (length : ℂ) * Grad.NonlinearQuotient.complexDeterminant
    (physicalColumn (originalPhysicalFrameMatrix parameters length epsilon field angle closedOrigin) 0) _
    (physicalColumn (originalPhysicalFrameMatrix parameters length epsilon field angle closedOrigin) 2) = _
  have recovered : matrixOperator (familyMatrix (originalInverseFamily parameters length epsilon field) 0 angle closedOrigin)
      (axisPhysicalValue (originalLiftPhysicalUAxis parameters length rho epsilon field low source index) angle) (1 : Fin 3) =
      axisPhysicalValue (originalLiftMetricAxis parameters length rho epsilon field low source index) angle (1 : Fin 2) :=
    originalLiftPhysicalUAxis_inverse_planar parameters length rho epsilon field low source index 1 angle
  rw [determinant_replace_second _ _
    (originalInverseFamily_matrix_identity parameters length epsilon field margin.2.2 0 angle closedOrigin).1,
    recovered,
    originalAxis_frame parameters length epsilon field vanishes angle,tiltedAxisFrame_det]
  ring

end Grad.FinitePhysicalJetLift
