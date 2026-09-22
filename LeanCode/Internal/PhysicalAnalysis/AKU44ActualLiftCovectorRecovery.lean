import AKU43SameFullAxisCovector

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct
open Grad.QuotientProjection Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger Grad.NonlinearDivision

theorem originalAxisInverseTransposeFamily_matrix_full (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalAxisInverseTransposeFamily parameters length epsilon field) grade angle point =
      (familyMatrix (originalInverseFamily parameters length epsilon field) grade angle closedOrigin).transpose := by
  have coherent := (originalInverseFamily_estimate parameters length rho epsilon field low).actualCoherent
  change operatorMatrix (coefficientPhysicalValue (axisFrozenCoefficient _) angle point) = _
  rw [axisFrozenCoefficient_physicalValue (unitDiskAdmissible parameters)]
  exact familyMatrix_transpose (unitDiskAdmissible parameters) _ coherent grade angle closedOrigin

theorem originalLiftPhysicalUAxis_physical (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (index : Fin 3) (angle : ℝ) :
    axisPhysicalValue (originalLiftPhysicalUAxis parameters length rho epsilon field low source index) angle =
      matrixOperator (familyMatrix (originalInverseFamily parameters length epsilon field) 0 angle closedOrigin).transpose
        (axisCovectorValue
          (axisPhysicalValue (originalLiftPlanarAxis parameters length rho epsilon field low source index) angle)
          (axisPhysicalValue (originalC2Axis length source index) angle 0)) := by
  rw [originalLiftPhysicalUAxis,axisFamilyAction_physical,axisCovectorTriple_physical,
    operator_eq_matrixOperator (coefficientPhysicalValue _ _ _)]
  change matrixOperator (familyMatrix (originalAxisInverseTransposeFamily parameters length epsilon field) 0 angle closedOrigin) _ = _
  rw [originalAxisInverseTransposeFamily_matrix_full parameters length rho epsilon field
    (originalCubic_low_margin parameters length rho epsilon field low).1]

/-- The actual full inverse-transpose construction recovers the SAME
planar covector under the current original Cartesian first derivative. -/
theorem originalLiftPhysicalUAxis_covector (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (index : Fin 3) (direction : Fin 2) :
    axisDot (traceFirst direction (planarReferenceCore parameters + field))
      (originalLiftPhysicalUAxis parameters length rho epsilon field low source index) =
      axisComponent direction (originalLiftPlanarAxis parameters length rho epsilon field low source index) := by
  apply axisPhysicalValue_ext
  intro angle
  apply PiLp.ext
  intro component
  have only : component = 0 := Subsingleton.elim _ _
  subst component
  rw [axisDot_physical,originalTotalFirstJet_frame parameters length epsilon field direction angle,
    originalLiftPhysicalUAxis_physical,axisComponent_physical]
  have margin := originalCoefficient_low_margin parameters length rho epsilon field
    (originalCubic_low_margin parameters length rho epsilon field low).1
  rw [fullColumn_dot_inverseTranspose _ _
    (originalInverseFamily_matrix_identity parameters length epsilon field margin.2.2 0 angle closedOrigin).2]
  fin_cases direction <;> simp [axisCovectorValue,Grad.FlatSourceProjection.componentValue_apply]

end Grad.FinitePhysicalJetLift
