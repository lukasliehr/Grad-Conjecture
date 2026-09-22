import AKU58ActualAxisMetricAndAffine

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Physical.Ledger

theorem originalLiftMetricAxis_actual_divergence (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (positive : 0 < length) (field : ACore parameters 3)
    (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (angle : ℝ) :
    (-((length : ℂ)*(originalAxisPlanarMatrix parameters length epsilon field angle).det)) •
      quadraticDivergenceCoefficients (fun index =>
        axisPhysicalValue (originalLiftMetricAxis parameters length rho epsilon field low source index) angle) =
      axisPhysicalValue (originalG1Axis source) angle := by
  have same : (fun index => axisPhysicalValue (originalLiftMetricAxis parameters length rho epsilon field low source index) angle) =
      quadraticValueMap (matrixOperator (originalAxisInverseGram parameters length epsilon field angle))
        (leadingPlanarLiftCoefficients
          (originalLeadingCubicLinear parameters length epsilon field 0 angle
            (fun index => axisPhysicalValue (originalForce2Axis source index) angle)
            (axisPhysicalValue (originalG1Axis source) angle)
            (fun index => axisPhysicalValue (originalC2Axis length source index) angle 0))
          (fun index => axisPhysicalValue (originalForce2Axis source index) angle) -
          quadraticScalarVectorProduct (originalAxisTilt parameters length epsilon field angle)
            (fun index => axisPhysicalValue (originalC2Axis length source index) angle 0)) := by
    funext index
    rw [originalLiftMetricAxis,originalMetricAction_physical parameters length rho epsilon field vanishes
      (originalCubic_low_margin parameters length rho epsilon field low).1,
      originalLiftPlanarAxis_physical,originalLiftEllAxis_physical parameters length rho epsilon field vanishes low]
    rfl
  rw [same]
  exact originalLeadingCubic_divergence parameters length rho epsilon positive field vanishes low 0 angle _ _ _

end Grad.FinitePhysicalJetLift
