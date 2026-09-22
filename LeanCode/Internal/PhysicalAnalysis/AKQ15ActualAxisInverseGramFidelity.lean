import AKQ14ActualAxisInverseGramFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.NonlinearDivision

theorem inversePlanarGramFamily_matrix {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    (inverse : CoefficientFamily 1 sigma gamma 1 3 3) (coherent : FamilyCoherent inverse)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (inversePlanarGramFamily admissible inverse) grade angle point =
      firstTwoProjection * (familyMatrix inverse grade angle point * (familyMatrix inverse grade angle point).transpose) *
        firstTwoInclusion := by
  have transpose := transposeFamily_coherent admissible inverse coherent
  have product : FamilyCoherent (composeFamily admissible inverse (transposeFamily admissible inverse)) := coherent.comp admissible transpose
  have projection := constantFamily_coherent 1 sigma gamma 1 (matrixOperator firstTwoProjection)
  have inclusion := constantFamily_coherent 1 sigma gamma 1 (matrixOperator firstTwoInclusion)
  have combined : FamilyCoherent (composeFamily admissible (composeFamily admissible inverse (transposeFamily admissible inverse))
      (constantFamily 1 sigma gamma 1 (matrixOperator firstTwoInclusion))) := product.comp admissible inclusion
  rw [inversePlanarGramFamily,familyMatrix_comp admissible _ _ projection combined,
    familyMatrix_comp admissible _ _ product inclusion,familyMatrix_comp admissible _ _ coherent transpose,
    familyMatrix_transpose admissible _ coherent,familyMatrix_constant admissible,familyMatrix_constant admissible]
  simp only [Matrix.mul_assoc]

theorem inversePlanarGramFamily_coherent {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    (inverse : CoefficientFamily 1 sigma gamma 1 3 3) (coherent : FamilyCoherent inverse) :
    FamilyCoherent (inversePlanarGramFamily admissible inverse) :=
  (constantFamily_coherent 1 sigma gamma 1 (matrixOperator firstTwoProjection)).comp admissible
    ((coherent.comp admissible (transposeFamily_coherent admissible inverse coherent)).comp admissible
      (constantFamily_coherent 1 sigma gamma 1 (matrixOperator firstTwoInclusion)))

theorem firstTwo_tiltedAxisGram (gram : Matrix (Fin 2) (Fin 2) ℂ) (tilt : ComplexEuclidean 2) :
    firstTwoProjection * tiltedAxisGram gram tilt * firstTwoInclusion = gram := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [firstTwoProjection,firstTwoInclusion,tiltedAxisGram,Matrix.mul_apply,Fin.sum_univ_three]

theorem originalAxisGramReference_matrix (parameters : PhaseParameters) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalAxisGramReference parameters) grade angle point = 1 := by
  change operatorMatrix (coefficientPhysicalValue (axisFrozenCoefficient _) angle point) = _
  rw [axisFrozenCoefficient_physicalValue (unitDiskAdmissible parameters)]
  change familyMatrix (inversePlanarGramFamily (unitDiskAdmissible parameters)
    (constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceFrame)) grade angle closedOrigin = _
  rw [inversePlanarGramFamily_matrix (unitDiskAdmissible parameters) _
    (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 referenceFrame),
    familyMatrix_referenceFrame (unitDiskAdmissible parameters),referenceFrame_matrix_transpose,referenceFrame_matrix_square,Matrix.mul_one]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [firstTwoProjection,firstTwoInclusion,Matrix.mul_apply,Fin.sum_univ_three]

/-- All grades and every disk point represent exactly the SAME actual K0
at the axis, at the original analytic width and with the full tilt retained
in the underlying frame (it cancels only in this upper planar Gram block). -/
theorem originalAxisGramFamily_matrix (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalAxisGramFamily parameters length epsilon field) grade angle point =
      originalAxisInverseGram parameters length epsilon field angle := by
  have margin := originalCoefficient_low_margin parameters length rho epsilon field low
  have coherent := originalInverseFamily_coherent parameters length epsilon field margin.2.2
  change operatorMatrix (coefficientPhysicalValue (axisFrozenCoefficient _) angle point) = _
  rw [axisFrozenCoefficient_physicalValue (unitDiskAdmissible parameters)]
  change familyMatrix (inversePlanarGramFamily (unitDiskAdmissible parameters)
    (originalInverseFamily parameters length epsilon field)) grade angle closedOrigin = _
  rw [inversePlanarGramFamily_matrix (unitDiskAdmissible parameters) _ coherent,
    originalInverseFamily_eq_matrixInverse parameters length rho epsilon field low,
    originalAxis_frame parameters length epsilon field vanishes]
  rw [tiltedAxisFrame_inv _ _ _ (Matrix.mul_nonsing_inv _
    (originalAxisPlanarMatrix_isUnit_det parameters length rho epsilon field vanishes low angle)),
    tiltedAxisInverse_gram,firstTwo_tiltedAxisGram,inverseGram_eq]
  rfl

end Grad.FinitePhysicalJetLift
