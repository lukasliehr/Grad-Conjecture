import GQF34FiniteRecipeControl

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

def gaugeColumnPolynomial (grade : ℕ) (derivative : Polynomial ℝ) : Polynomial ℝ :=
  fixedCoefficientPolynomial (matrixOperator toroidalPhysicalColumn) grade +
    productPolynomial grade (fixedCoefficientPolynomial (matrixOperator planarPhysicalInclusion) grade)
      (productPolynomial grade derivative (spatialColumnPolynomial grade))

def gaugePlanarPolynomial (grade : ℕ) (seed : Polynomial ℝ) : Polynomial ℝ :=
  productPolynomial grade (fixedCoefficientPolynomial (matrixOperator planarFrameColumns) grade)
    (productPolynomial grade (transposeRecipePolynomial grade 2 2 seed)
      (fixedCoefficientPolynomial (matrixOperator planarPhysicalInclusion.transpose) grade))

def gaugeStackPolynomial (grade : ℕ) (seed derivative : Polynomial ℝ) : Polynomial ℝ :=
  gaugePlanarPolynomial grade seed +
    productPolynomial grade (fixedCoefficientPolynomial (matrixOperator thirdFrameColumn) grade)
      (transposeRecipePolynomial grade 1 3 (gaugeColumnPolynomial grade derivative))

def gaugeRecipePolynomial (grade : ℕ) (seed derivative inverse : Polynomial ℝ) : Polynomial ℝ :=
  productPolynomial grade (gaugeStackPolynomial grade seed derivative) (transposeRecipePolynomial grade 3 3 inverse)

theorem gaugeFamily_control {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade : ℕ} {seedP derivativeP inverseP : Polynomial ℝ} {value : ℝ}
    {seed referenceSeed derivative referenceDerivative : CoefficientFamily L sigma gamma ell 2 2}
    {inverse referenceInverse : CoefficientFamily L sigma gamma ell 3 3}
    (seedControl : PolynomialControl seedP value (seed grade) (referenceSeed grade))
    (derivativeControl : PolynomialControl derivativeP value (derivative grade) (referenceDerivative grade))
    (inverseControl : PolynomialControl inverseP value (inverse grade) (referenceInverse grade)) :
    PolynomialControl (gaugeRecipePolynomial grade seedP derivativeP inverseP) value
      (gaugeFamily admissible seed derivative inverse grade)
      (gaugeFamily admissible referenceSeed referenceDerivative referenceInverse grade) := by
  have column := (constantFamily_control admissible (matrixOperator toroidalPhysicalColumn) grade value).add
    ((constantFamily_control admissible (matrixOperator planarPhysicalInclusion) grade value).comp admissible
      (derivativeControl.comp admissible (spatialColumnFamily_control L sigma gamma ell grade value)))
  have planar := (constantFamily_control admissible (matrixOperator planarFrameColumns) grade value).comp admissible
    ((transposeFamily_control admissible seedControl).comp admissible
      (constantFamily_control admissible (matrixOperator planarPhysicalInclusion.transpose) grade value))
  have stack := planar.add ((constantFamily_control admissible (matrixOperator thirdFrameColumn) grade value).comp admissible
    (transposeFamily_control admissible (actual := gaugeColumnFamily admissible derivative)
      (reference := gaugeColumnFamily admissible referenceDerivative) column))
  exact stack.comp admissible (transposeFamily_control admissible inverseControl)

def traceRecipePolynomial (grade : ℕ) (seedInverse frameInverse : Polynomial ℝ) : Polynomial ℝ :=
  productPolynomial grade
    (productPolynomial grade
      (productPolynomial grade (transposeRecipePolynomial grade 1 2 (spatialColumnPolynomial grade)) seedInverse)
      (fixedCoefficientPolynomial (matrixOperator planarPhysicalInclusion.transpose) grade))
    (transposeRecipePolynomial grade 3 3 frameInverse)

theorem traceFamily_control {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade : ℕ} {seedP inverseP : Polynomial ℝ} {value : ℝ}
    {seed referenceSeed : CoefficientFamily L sigma gamma ell 2 2}
    {inverse referenceInverse : CoefficientFamily L sigma gamma ell 3 3}
    (seedControl : PolynomialControl seedP value (seed grade) (referenceSeed grade))
    (inverseControl : PolynomialControl inverseP value (inverse grade) (referenceInverse grade)) :
    PolynomialControl (traceRecipePolynomial grade seedP inverseP) value
      (traceFamily admissible seed inverse grade) (traceFamily admissible referenceSeed referenceInverse grade) :=
  (((transposeFamily_control admissible (spatialColumnFamily_control L sigma gamma ell grade value)).comp admissible seedControl).comp
    admissible (constantFamily_control admissible (matrixOperator planarPhysicalInclusion.transpose) grade value)).comp
      admissible (transposeFamily_control admissible inverseControl)

def rotatedRecipePolynomial {columns : ℕ} (grade : ℕ) (selector : Matrix (Fin 3) (Fin columns) ℂ)
    (rotated inverse : Polynomial ℝ) : Polynomial ℝ :=
  productPolynomial grade
    (transposeRecipePolynomial grade columns 3
      (productPolynomial grade rotated (fixedCoefficientPolynomial (matrixOperator selector) grade)))
    (transposeRecipePolynomial grade 3 3 inverse)

theorem rotatedProductFamily_control {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade columns : ℕ} {rotatedP inverseP : Polynomial ℝ} {value : ℝ}
    (selector : Matrix (Fin 3) (Fin columns) ℂ)
    {rotated referenceRotated inverse referenceInverse : CoefficientFamily L sigma gamma ell 3 3}
    (rotatedControl : PolynomialControl rotatedP value (rotated grade) (referenceRotated grade))
    (inverseControl : PolynomialControl inverseP value (inverse grade) (referenceInverse grade)) :
    PolynomialControl (rotatedRecipePolynomial grade selector rotatedP inverseP) value
      (rotatedProductFamily admissible selector rotated inverse grade)
      (rotatedProductFamily admissible selector referenceRotated referenceInverse grade) :=
  (transposeFamily_control admissible (rotatedControl.comp admissible
    (constantFamily_control admissible (matrixOperator selector) grade value))).comp
      admissible (transposeFamily_control admissible inverseControl)

end Grad.GaugeCoefficients.Physical.Compensated
