import AKQ20SameCurrentCubicNeumannInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients
open Grad.NonlinearQuotientBounds Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.InverseAllocation Grad.GaugeCoefficients.Physical.Ledger Grad.NonlinearDivision

/-- Both inverse laws for the literal actual K0 cubic determinant map,
using one and the same original-width Neumann series at every grade. -/
theorem originalCubicInverseFamily_two_sided (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    let matrix := cubicDeterminantOperator (matrixOperator (originalAxisInverseGram parameters length epsilon field angle))
    let inverse := coefficientPhysicalValue (originalCubicInverseFamily parameters length epsilon field grade) angle point
    matrix.comp inverse = ContinuousLinearMap.id ℂ (ComplexEuclidean 2) ∧
      inverse.comp matrix = ContinuousLinearMap.id ℂ (ComplexEuclidean 2) := by
  dsimp only
  rw [originalCubicInverseFamily_physicalValue parameters length rho epsilon field low]
  have margin := originalCubic_low_margin parameters length rho epsilon field low
  have laws := analyticCapCoefficientNeumannInverse_pointwiseIdentification (unitDiskAdmissible parameters)
    (by norm_num : 0 < 2) (originalCubicInverseInput parameters length epsilon field 0)
    (1/4) margin.2.2 (by norm_num) angle point
  rw [originalCubicInverseInput_normalized parameters length rho epsilon field vanishes margin.1] at laws
  have injective : Function.Injective referenceCubicInverse := by
    intro first second same
    have mapped := congrArg referenceCubicOperator same
    simpa only [referenceCubicOperator_inverse] using mapped
  constructor
  · apply ContinuousLinearMap.ext
    intro value
    apply injective
    exact congrArg (fun mapping : OperatorValue 2 2 => mapping (referenceCubicInverse value)) laws.1
  · apply ContinuousLinearMap.ext
    intro value
    exact congrArg (fun mapping : OperatorValue 2 2 => mapping value) laws.2

theorem originalCubicInverseFamily_pointwise_bound (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    ‖coefficientPhysicalValue (originalCubicInverseFamily parameters length epsilon field grade) angle point‖ ≤ (1/2 : ℝ) := by
  have margin := originalCubic_low_margin parameters length rho epsilon field low
  have base := analyticCapCoefficientNeumannInverse_baseBound (unitDiskAdmissible parameters)
    (by norm_num : 0 < 2) (originalCubicInverseInput parameters length epsilon field 0) (1/4) margin.2.2 (by norm_num)
  have bound := (seedFourier_norm_le (unitDiskAdmissible parameters)
    (analyticCapCoefficientNeumannInverse (unitDiskAdmissible parameters) (originalCubicInverseInput parameters length epsilon field 0)) angle point).trans base
  norm_num at bound
  rw [originalCubicInverseFamily_physicalValue parameters length rho epsilon field low]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro value
  apply (ContinuousLinearMap.le_opNorm _ (referenceCubicInverse value)).trans
  rw [referenceCubicInverse_norm]
  exact (mul_le_mul_of_nonneg_right bound (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3/8) (norm_nonneg value))).trans_eq (by ring)

/-- Concrete consumer: the constructed same-width inverse solves the
literal Cartesian divergence of K0 Ucal(r²ell) on the whole closed disk. -/
theorem originalCubicInverse_solves_actual_divergence (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (grade : ℕ) (angle : ℝ) (evaluationPoint point : ClosedDisk) (target : ComplexEuclidean 2) :
    (Grad.CartesianScalarElimination.vectorDivJet
      (valueMapJet (matrixOperator (originalAxisInverseGram parameters length epsilon field angle))
        (cubicPlanarLift (cubicComplementCoefficients
          (coefficientPhysicalValue (originalCubicInverseFamily parameters length epsilon field grade) angle evaluationPoint target))))).value point 0 =
      (point.val 0 : ℂ) * target 0 + (point.val 1 : ℂ) * target 1 := by
  rw [cubicDeterminantOperator_actual]
  have solved := congrArg (fun mapping : OperatorValue 2 2 => mapping target)
    (originalCubicInverseFamily_two_sided parameters length rho epsilon field vanishes low grade angle evaluationPoint).1
  change cubicDeterminantOperator (matrixOperator (originalAxisInverseGram parameters length epsilon field angle))
    (coefficientPhysicalValue (originalCubicInverseFamily parameters length epsilon field grade) angle evaluationPoint target) = target at solved
  rw [solved]

end Grad.FinitePhysicalJetLift
