import AKU26AxisPolynomialFourierAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisJet Grad.FlatSourceProjection Grad.QuotientProjection Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Algebra Grad.NonlinearDivision

theorem operator_eq_matrixOperator {input output : ℕ} (mapping : OperatorValue input output) :
    mapping = matrixOperator (operatorMatrix mapping) :=
  operatorMatrix_injective (operatorMatrix_matrixOperator _).symm

theorem scalarMatrix_operator (scalar : ℂ) :
    matrixOperator (scalarMatrix scalar) = scalar • ContinuousLinearMap.id ℂ (ComplexEuclidean 1) := by
  apply operatorMatrix_injective
  rw [operatorMatrix_matrixOperator,operatorMatrix_smul,operatorMatrix_one]
  ext row column
  have rowZero : row = 0 := Subsingleton.elim _ _
  have columnZero : column = 0 := Subsingleton.elim _ _
  subst row
  subst column
  simp [scalarMatrix]

theorem originalMetricAction_physical (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (planar : Grad.AxisCore.AxisSmoothCore parameters 2) (toroidal : Grad.AxisCore.AxisSmoothCore parameters 1) (angle : ℝ) :
    axisPhysicalValue (axisFamilyAction (originalAxisMetricRowsFamily parameters length epsilon field)
      (originalAxisMetricRowsFamily_estimate parameters length rho epsilon field low).actualCoherent
      (axisCovectorTriple planar toroidal)) angle =
    matrixOperator (originalAxisInverseGram parameters length epsilon field angle)
      (axisPhysicalValue planar angle - axisPhysicalValue toroidal angle 0 • originalAxisTilt parameters length epsilon field angle) := by
  rw [axisFamilyAction_physical,axisCovectorTriple_physical]
  rw [operator_eq_matrixOperator (coefficientPhysicalValue _ _ _)]
  change matrixOperator (familyMatrix (originalAxisMetricRowsFamily parameters length epsilon field) 0 angle closedOrigin) _ = _
  rw [originalAxisMetricRowsFamily_matrix parameters length rho epsilon field vanishes low]
  exact firstTwo_tiltedAxisGram_covector _ _ _ _

theorem originalDeterminantAction_physical (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (data : Grad.AxisCore.AxisSmoothCore parameters 1) (angle : ℝ) :
    axisPhysicalValue (axisFamilyAction (originalAxisInverseDeterminantFamily parameters length epsilon field)
      (originalAxisInverseDeterminantFamily_estimate parameters length rho epsilon field low).actualCoherent data) angle =
      (-(originalAxisPlanarMatrix parameters length epsilon field angle).det⁻¹) • axisPhysicalValue data angle := by
  rw [axisFamilyAction_physical,operator_eq_matrixOperator (coefficientPhysicalValue _ _ _)]
  change matrixOperator (familyMatrix (originalAxisInverseDeterminantFamily parameters length epsilon field) 0 angle closedOrigin) _ = _
  rw [originalAxisInverseDeterminantFamily_matrix parameters length rho epsilon field vanishes low,scalarMatrix_operator]
  rfl

/-- Exact Fourier evaluation of the constructed target, with the same full
source, tilt, determinant sign, and actual coefficient inverse. -/
theorem originalCubicTargetAxis_physical (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (angle : ℝ) :
    axisPhysicalValue (originalCubicTargetAxis parameters length rho epsilon field low source) angle =
      leadingCubicTarget length (originalAxisPlanarMatrix parameters length epsilon field angle).det
        (matrixOperator (originalAxisInverseGram parameters length epsilon field angle))
        (fun index => axisPhysicalValue (originalForce2Axis source index) angle)
        (axisPhysicalValue (originalG1Axis source) angle)
        (originalAxisTilt parameters length epsilon field angle)
        (fun index => axisPhysicalValue (originalC2Axis length source index) angle 0) := by
  dsimp only [originalCubicTargetAxis]
  rw [axisPhysicalValue_sub,axisPhysicalValue_smul,scalarAxisPair_physical,axisQuadraticDivergence_physical]
  simp only [originalDeterminantAction_physical parameters length rho epsilon field vanishes
      (originalCubic_low_margin parameters length rho epsilon field low).1,
    originalMetricAction_physical parameters length rho epsilon field vanishes
      (originalCubic_low_margin parameters length rho epsilon field low).1,
    axisPhysicalValue_neg,quadraticAxisPlanarInverse_physical]
  unfold leadingCubicTarget leadingForcedPlanarCoefficients quadraticScalarVectorProduct
    quadraticMappedDivergence quadraticValueMap
  rw [originalG1Axis,scalarAxisPair_physical]
  congr 1
  apply PiLp.ext
  intro component
  fin_cases component <;> simp [mul_inv_rev] <;> ring

theorem originalLiftEllAxis_physical (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (angle : ℝ) :
    axisPhysicalValue (originalLiftEllAxis parameters length rho epsilon field low source) angle =
      originalLeadingCubicLinear parameters length epsilon field 0 angle
        (fun index => axisPhysicalValue (originalForce2Axis source index) angle)
        (axisPhysicalValue (originalG1Axis source) angle)
        (fun index => axisPhysicalValue (originalC2Axis length source index) angle 0) := by
  rw [originalLiftEllAxis,axisFamilyAction_physical,originalCubicTargetAxis_physical parameters length rho epsilon field vanishes low]
  rfl

theorem originalLiftPlanarAxis_physical (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (angle : ℝ) (index : Fin 3) :
    axisPhysicalValue (originalLiftPlanarAxis parameters length rho epsilon field low source index) angle =
      leadingPlanarLiftCoefficients (axisPhysicalValue (originalLiftEllAxis parameters length rho epsilon field low source) angle)
        (fun slot => axisPhysicalValue (originalForce2Axis source slot) angle) index := by
  change axisPhysicalValue (_ - _) angle = _
  rw [axisPhysicalValue_sub,axisCubicComplementVector_physical,quadraticAxisPlanarInverse_physical]
  rfl

end Grad.FinitePhysicalJetLift
