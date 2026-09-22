import AKU21ActualAxisLiftMatrixFamilies

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger Grad.NonlinearDivision

theorem firstTwoInverseGramFamily_matrix {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    (inverse : CoefficientFamily 1 sigma gamma 1 3 3) (coherent : FamilyCoherent inverse)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (firstTwoInverseGramFamily admissible inverse) grade angle point =
      firstTwoProjection * (familyMatrix inverse grade angle point * (familyMatrix inverse grade angle point).transpose) := by
  have transpose := transposeFamily_coherent admissible inverse coherent
  have product : FamilyCoherent (composeFamily admissible inverse (transposeFamily admissible inverse)) :=
    coherent.comp admissible transpose
  have projection := constantFamily_coherent 1 sigma gamma 1 (matrixOperator firstTwoProjection)
  rw [firstTwoInverseGramFamily,familyMatrix_comp admissible _ _ projection product,
    familyMatrix_comp admissible _ _ coherent transpose,familyMatrix_transpose admissible _ coherent,
    familyMatrix_constant admissible]

theorem originalAxisMetricRowsFamily_matrix (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalAxisMetricRowsFamily parameters length epsilon field) grade angle point =
      firstTwoProjection * tiltedAxisGram (originalAxisInverseGram parameters length epsilon field angle)
        (originalAxisTilt parameters length epsilon field angle) := by
  have coherent := (originalInverseFamily_estimate parameters length rho epsilon field low).actualCoherent
  change operatorMatrix (coefficientPhysicalValue (axisFrozenCoefficient _) angle point) = _
  rw [axisFrozenCoefficient_physicalValue (unitDiskAdmissible parameters)]
  change familyMatrix (firstTwoInverseGramFamily (unitDiskAdmissible parameters)
    (originalInverseFamily parameters length epsilon field)) grade angle closedOrigin = _
  rw [firstTwoInverseGramFamily_matrix (unitDiskAdmissible parameters) _ coherent,
    originalInverseFamily_eq_matrixInverse parameters length rho epsilon field low,
    originalAxis_frame parameters length epsilon field vanishes,
    tiltedAxisFrame_inv _ _ _ (Matrix.mul_nonsing_inv _
      (originalAxisPlanarMatrix_isUnit_det parameters length rho epsilon field vanishes low angle)),
    tiltedAxisInverse_gram,inverseGram_eq]
  rfl

theorem originalAxisInverseDeterminantFamily_matrix (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalAxisInverseDeterminantFamily parameters length epsilon field) grade angle point =
      scalarMatrix (-(originalAxisPlanarMatrix parameters length epsilon field angle).det⁻¹) := by
  have coherent := (originalInverseFamily_estimate parameters length rho epsilon field low).actualCoherent
  change operatorMatrix (coefficientPhysicalValue (axisFrozenCoefficient _) angle point) = _
  rw [axisFrozenCoefficient_physicalValue (unitDiskAdmissible parameters)]
  change familyMatrix (determinantFamily (unitDiskAdmissible parameters)
    (originalInverseFamily parameters length epsilon field)) grade angle closedOrigin = _
  rw [determinantFamily_matrix (unitDiskAdmissible parameters) _ coherent,
    originalInverseFamily_eq_matrixInverse parameters length rho epsilon field low,
    Matrix.det_nonsing_inv,originalAxis_frame parameters length epsilon field vanishes,
    tiltedAxisFrame_det]
  simp only [Ring.inverse_eq_inv,inv_neg]

theorem originalAxisInverseTransposeFamily_matrix (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalAxisInverseTransposeFamily parameters length epsilon field) grade angle point =
      (tiltedAxisInverse (originalAxisPlanarMatrix parameters length epsilon field angle)⁻¹
        (originalAxisTilt parameters length epsilon field angle)).transpose := by
  have coherent := (originalInverseFamily_estimate parameters length rho epsilon field low).actualCoherent
  change operatorMatrix (coefficientPhysicalValue (axisFrozenCoefficient _) angle point) = _
  rw [axisFrozenCoefficient_physicalValue (unitDiskAdmissible parameters)]
  change familyMatrix (transposeFamily (unitDiskAdmissible parameters)
    (originalInverseFamily parameters length epsilon field)) grade angle closedOrigin = _
  rw [familyMatrix_transpose (unitDiskAdmissible parameters) _ coherent,
    originalInverseFamily_eq_matrixInverse parameters length rho epsilon field low,
    originalAxis_frame parameters length epsilon field vanishes,
    tiltedAxisFrame_inv _ _ _ (Matrix.mul_nonsing_inv _
      (originalAxisPlanarMatrix_isUnit_det parameters length rho epsilon field vanishes low angle))]

end Grad.FinitePhysicalJetLift
