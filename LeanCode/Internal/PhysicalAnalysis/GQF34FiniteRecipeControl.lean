import GQF33PolynomialControl

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

def fixedCoefficientPolynomial {input output : ℕ} (operator : OperatorValue input output) (grade : ℕ) : Polynomial ℝ :=
  Polynomial.C (fixedFamilyConstant operator grade)

def fixedJetPolynomial {input output : ℕ} (jet : SmoothOperatorJet input output) (grade : ℕ) : Polynomial ℝ :=
  Polynomial.C (fixedJetConstant jet grade)

theorem constantFamily_control {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (operator : OperatorValue input output) (grade : ℕ) (value : ℝ) :
    PolynomialControl (fixedCoefficientPolynomial operator grade) value
      (constantFamily L sigma gamma ell operator grade) (constantFamily L sigma gamma ell operator grade) :=
  polynomialControl_constant _ _ _ (constantFamily_norm_le admissible operator grade)

theorem fixedJetFamily_control {L sigma gamma ell : ℝ}
    {input output : ℕ} (jet : SmoothOperatorJet input output) (grade : ℕ) (value : ℝ) :
    PolynomialControl (fixedJetPolynomial jet grade) value
      (fixedJetFamily L sigma gamma ell jet grade) (fixedJetFamily L sigma gamma ell jet grade) :=
  polynomialControl_constant _ _ _ (fixedJetFamily_norm_le L sigma gamma ell jet grade)

def spatialColumnPolynomial (grade : ℕ) : Polynomial ℝ :=
  fixedJetPolynomial (coordinateOperatorJet 0 (matrixUnit (input := 1) (output := 2) 0 0)) grade +
    fixedJetPolynomial (coordinateOperatorJet 1 (matrixUnit (input := 1) (output := 2) 1 0)) grade

theorem spatialColumnFamily_control (L sigma gamma ell : ℝ) (grade : ℕ) (value : ℝ) :
    PolynomialControl (spatialColumnPolynomial grade) value
      (spatialColumnFamily L sigma gamma ell grade) (spatialColumnFamily L sigma gamma ell grade) :=
  (fixedJetFamily_control (L := L) (sigma := sigma) (gamma := gamma) (ell := ell) _ grade value).add
    (fixedJetFamily_control _ grade value)

def transposeRecipePolynomial (grade input output : ℕ) (polynomial : Polynomial ℝ) : Polynomial ℝ :=
  ∑ pair : Fin input × Fin output,
    productPolynomial grade (fixedCoefficientPolynomial (matrixUnit pair.1 pair.2) grade)
      (productPolynomial grade polynomial (fixedCoefficientPolynomial (matrixUnit pair.1 pair.2) grade))

theorem transposeFamily_control {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade input output : ℕ} {polynomial : Polynomial ℝ} {value : ℝ}
    {actual reference : CoefficientFamily L sigma gamma ell input output}
    (control : PolynomialControl polynomial value (actual grade) (reference grade)) :
    PolynomialControl (transposeRecipePolynomial grade input output polynomial) value
      (transposeFamily admissible actual grade) (transposeFamily admissible reference grade) :=
  PolynomialControl.finiteSum _ _ _ _ (fun pair =>
    (constantFamily_control admissible (matrixUnit pair.1 pair.2) grade value).comp admissible
      (control.comp admissible (constantFamily_control admissible (matrixUnit pair.1 pair.2) grade value)))

def scalarEntryRecipePolynomial {input output : ℕ} (grade : ℕ) (row : Fin output) (column : Fin input)
    (polynomial : Polynomial ℝ) : Polynomial ℝ :=
  productPolynomial grade (fixedCoefficientPolynomial (matrixUnit (output := 1) 0 row) grade)
    (productPolynomial grade polynomial (fixedCoefficientPolynomial (matrixUnit (input := 1) column 0) grade))

theorem scalarEntryFamily_control {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade input output : ℕ} {polynomial : Polynomial ℝ} {value : ℝ}
    {actual reference : CoefficientFamily L sigma gamma ell input output}
    (row : Fin output) (column : Fin input)
    (control : PolynomialControl polynomial value (actual grade) (reference grade)) :
    PolynomialControl (scalarEntryRecipePolynomial grade row column polynomial) value
      (scalarEntryFamily admissible row column actual grade) (scalarEntryFamily admissible row column reference grade) :=
  (constantFamily_control admissible (matrixUnit (output := 1) 0 row) grade value).comp admissible
    (control.comp admissible (constantFamily_control admissible (matrixUnit (input := 1) column 0) grade value))

def scalarLiftRecipePolynomial (grade dimension : ℕ) (polynomial : Polynomial ℝ) : Polynomial ℝ :=
  ∑ row : Fin dimension,
    productPolynomial grade (fixedCoefficientPolynomial (matrixUnit (input := 1) row 0) grade)
      (productPolynomial grade polynomial (fixedCoefficientPolynomial (matrixUnit (output := 1) 0 row) grade))

theorem scalarLiftFamily_control {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade : ℕ} {polynomial : Polynomial ℝ} {value : ℝ}
    {actual reference : CoefficientFamily L sigma gamma ell 1 1} (dimension : ℕ)
    (control : PolynomialControl polynomial value (actual grade) (reference grade)) :
    PolynomialControl (scalarLiftRecipePolynomial grade dimension polynomial) value
      (scalarLiftFamily admissible dimension actual grade) (scalarLiftFamily admissible dimension reference grade) :=
  PolynomialControl.finiteSum _ _ _ _ (fun row =>
    (constantFamily_control admissible (matrixUnit (input := 1) row 0) grade value).comp admissible
      (control.comp admissible (constantFamily_control admissible (matrixUnit (output := 1) 0 row) grade value)))

end Grad.GaugeCoefficients.Physical.Compensated
