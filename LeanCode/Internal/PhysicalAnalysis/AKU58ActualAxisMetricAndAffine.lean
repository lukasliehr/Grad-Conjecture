import AKU53LiteralFourthSourceJetMatch
import AKU57ActualColumnDeterminantAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Physical.Ledger

theorem affineStateCore_actual_axis (parameters : PhaseParameters) (length epsilon : ℝ)
    (field : ACore parameters 3) (potential : ACore parameters 1)
    (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0) (angle : ℝ) :
    coreValue (affineStateCore parameters length ((epsilon : ℂ),planarReferenceCore parameters+field,potential)) closedOrigin angle =
      (length : ℂ) • physicalColumn (originalPhysicalFrameMatrix parameters length epsilon field angle closedOrigin) 2 := by
  rw [← traceZero_physical,affineStateCore_axis parameters length _ (originalTotal_axis_zero parameters field vanishes),
    axisPhysicalValue_smul,traceZero_physical]
  congr 1
  rw [eTConstantCore,coreValue_constant]
  apply PiLp.ext
  intro row
  fin_cases row <;> simp [physicalColumn,originalAxis_thirdColumn parameters length epsilon field vanishes angle]

theorem originalAxisMetricRowsFamily_matrix_full (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalAxisMetricRowsFamily parameters length epsilon field) grade angle point =
      firstTwoProjection * (familyMatrix (originalInverseFamily parameters length epsilon field) grade angle closedOrigin *
        (familyMatrix (originalInverseFamily parameters length epsilon field) grade angle closedOrigin).transpose) := by
  have coherent := (originalInverseFamily_estimate parameters length rho epsilon field low).actualCoherent
  change operatorMatrix (coefficientPhysicalValue (axisFrozenCoefficient _) angle point) = _
  rw [axisFrozenCoefficient_physicalValue (unitDiskAdmissible parameters)]
  exact firstTwoInverseGramFamily_matrix (unitDiskAdmissible parameters) _ coherent grade angle closedOrigin

def originalLiftMetricAxis (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (index : Fin 3) : Grad.AxisCore.AxisSmoothCore parameters 2 :=
  axisFamilyAction (originalAxisMetricRowsFamily parameters length epsilon field)
    (originalAxisMetricRowsFamily_estimate parameters length rho epsilon field
      (originalCubic_low_margin parameters length rho epsilon field low).1).actualCoherent
    (axisCovectorTriple (originalLiftPlanarAxis parameters length rho epsilon field low source index)
      (originalC2Axis length source index))

theorem firstTwoProjection_apply (value : ComplexEuclidean 3) (direction : Fin 2) :
    matrixOperator firstTwoProjection value direction = value direction.castSucc := by
  rw [threeColumnOperator_apply,operatorMatrix_matrixOperator]
  fin_cases direction <;> simp [firstTwoProjection]

/-- The two original metric rows are exactly F^-1 U for the SAME full
inverse-transpose vector construction, retaining its toroidal coupling. -/
theorem originalLiftPhysicalUAxis_inverse_planar (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (index : Fin 3) (direction : Fin 2) (angle : ℝ) :
    matrixOperator (familyMatrix (originalInverseFamily parameters length epsilon field) 0 angle closedOrigin)
      (axisPhysicalValue (originalLiftPhysicalUAxis parameters length rho epsilon field low source index) angle) direction.castSucc =
      axisPhysicalValue (originalLiftMetricAxis parameters length rho epsilon field low source index) angle direction := by
  rw [originalLiftPhysicalUAxis_physical,matrixOperator_comp_apply,originalLiftMetricAxis,
    axisFamilyAction_physical,axisCovectorTriple_physical,operator_eq_matrixOperator (coefficientPhysicalValue _ _ _)]
  change _ = matrixOperator (familyMatrix (originalAxisMetricRowsFamily parameters length epsilon field) 0 angle closedOrigin) _ direction
  rw [originalAxisMetricRowsFamily_matrix_full parameters length rho epsilon field
    (originalCubic_low_margin parameters length rho epsilon field low).1,← matrixOperator_comp_apply firstTwoProjection,firstTwoProjection_apply]

end Grad.FinitePhysicalJetLift
