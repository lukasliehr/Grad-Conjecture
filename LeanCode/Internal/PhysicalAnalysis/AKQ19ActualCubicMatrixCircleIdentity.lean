import AKQ18ActualCubicMatrixLowMargin

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Physical.Ledger
open Grad.NonlinearDivision

theorem originalCubicMatrixFamily_physicalValue (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (originalCubicMatrixFamily parameters length epsilon field grade) angle point =
      cubicDeterminantOperator (matrixOperator (originalAxisInverseGram parameters length epsilon field angle)) := by
  apply operatorMatrix_injective
  change familyMatrix (cubicMatrixFamily (unitDiskAdmissible parameters) (originalAxisGramFamily parameters length epsilon field)) grade angle point = _
  rw [cubicMatrixFamily_matrix (unitDiskAdmissible parameters) _
    (originalAxisGramFamily_estimate parameters length rho epsilon field low).actualCoherent,
    originalAxisGramFamily_matrix parameters length rho epsilon field vanishes low,
    cubicDeterminantOperator_matrix,operatorMatrix_matrixOperator]

theorem originalCubicMatrixReference_physicalValue (parameters : PhaseParameters) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (originalCubicMatrixReference parameters grade) angle point = referenceCubicOperator := by
  have coherent : FamilyCoherent (originalAxisGramReference parameters) :=
    axisFrozenFamily_coherent (unitDiskAdmissible parameters) _
      (inversePlanarGramFamily_coherent (unitDiskAdmissible parameters) _
        (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 referenceFrame))
  apply operatorMatrix_injective
  change familyMatrix (cubicMatrixFamily (unitDiskAdmissible parameters) (originalAxisGramReference parameters)) grade angle point = _
  rw [cubicMatrixFamily_matrix (unitDiskAdmissible parameters) _ coherent,originalAxisGramReference_matrix,
    ← cubicDeterminantOperator_reference,cubicDeterminantOperator_matrix,operatorMatrix_one]

theorem referenceCubicInverse_comp_operator : referenceCubicInverse.comp referenceCubicOperator =
    ContinuousLinearMap.id ℂ (ComplexEuclidean 2) := by
  apply ContinuousLinearMap.ext
  intro value
  exact referenceCubicInverse_operator value

theorem referenceCubicOperator_comp_inverse : referenceCubicOperator.comp referenceCubicInverse =
    ContinuousLinearMap.id ℂ (ComplexEuclidean 2) := by
  apply ContinuousLinearMap.ext
  intro value
  exact referenceCubicOperator_inverse value

/-- The actual perturbation is normalized with the exact D_I inverse.
Both original signs are retained in I−H = D_I^-1 D_K0. -/
theorem originalCubicInverseInput_normalized (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (angle : ℝ) (point : ClosedDisk) :
    ContinuousLinearMap.id ℂ (ComplexEuclidean 2) -
      fourierEvaluation (originalCubicInverseInput parameters length epsilon field 0) angle point =
        referenceCubicInverse.comp
          (cubicDeterminantOperator (matrixOperator (originalAxisInverseGram parameters length epsilon field angle))) := by
  have estimate := originalCubicMatrixFamily_estimate parameters length rho epsilon field low
  change ContinuousLinearMap.id ℂ (ComplexEuclidean 2) -
    coefficientPhysicalValue (originalCubicInverseInput parameters length epsilon field 0) angle point = _
  rw [originalCubicInverseInput,composeFamily,family_physicalValue_comp (unitDiskAdmissible parameters) _ _
    (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 (-referenceCubicInverse))
    (estimate.actualCoherent.sub estimate.referenceCoherent),
    constantFamily_physicalValue (unitDiskAdmissible parameters),
    family_physicalValue_sub (unitDiskAdmissible parameters) _ _ estimate.actualCoherent estimate.referenceCoherent,
    originalCubicMatrixFamily_physicalValue parameters length rho epsilon field vanishes low,
    originalCubicMatrixReference_physicalValue]
  apply ContinuousLinearMap.ext
  intro value
  change value - (-(referenceCubicInverse
    ((cubicDeterminantOperator (matrixOperator (originalAxisInverseGram parameters length epsilon field angle))) value -
      referenceCubicOperator value))) =
    referenceCubicInverse ((cubicDeterminantOperator (matrixOperator (originalAxisInverseGram parameters length epsilon field angle))) value)
  rw [map_sub,referenceCubicInverse_operator]
  abel

end Grad.FinitePhysicalJetLift
