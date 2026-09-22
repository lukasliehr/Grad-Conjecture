import GQF38PrimitiveInverses

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

theorem fixedJetPolynomial_nonnegative {input output : ℕ} (jet : SmoothOperatorJet input output) (grade : ℕ) :
    NonnegativeCoefficients (fixedJetPolynomial jet grade) := nonnegativeCoefficients_const _ (fixedJetConstant_nonnegative jet grade)

theorem spatialColumnPolynomial_nonnegative (grade : ℕ) : NonnegativeCoefficients (spatialColumnPolynomial grade) :=
  (fixedJetPolynomial_nonnegative _ grade).add (fixedJetPolynomial_nonnegative _ grade)

theorem transposeRecipePolynomial_nonnegative (grade input output : ℕ) {polynomial : Polynomial ℝ}
    (positive : NonnegativeCoefficients polynomial) : NonnegativeCoefficients (transposeRecipePolynomial grade input output polynomial) :=
  NonnegativeCoefficients.sum Finset.univ _ (fun _ _ => productPolynomial_nonnegative grade
    (fixedCoefficientPolynomial_nonnegative _ grade)
    (productPolynomial_nonnegative grade positive (fixedCoefficientPolynomial_nonnegative _ grade)))

theorem scalarEntryRecipePolynomial_nonnegative {input output : ℕ} (grade : ℕ) (row : Fin output) (column : Fin input)
    {polynomial : Polynomial ℝ} (positive : NonnegativeCoefficients polynomial) :
    NonnegativeCoefficients (scalarEntryRecipePolynomial grade row column polynomial) :=
  productPolynomial_nonnegative grade (fixedCoefficientPolynomial_nonnegative _ grade)
    (productPolynomial_nonnegative grade positive (fixedCoefficientPolynomial_nonnegative _ grade))

theorem scalarLiftRecipePolynomial_nonnegative (grade dimension : ℕ) {polynomial : Polynomial ℝ}
    (positive : NonnegativeCoefficients polynomial) : NonnegativeCoefficients (scalarLiftRecipePolynomial grade dimension polynomial) :=
  NonnegativeCoefficients.sum Finset.univ _ (fun _ _ => productPolynomial_nonnegative grade
    (fixedCoefficientPolynomial_nonnegative _ grade)
    (productPolynomial_nonnegative grade positive (fixedCoefficientPolynomial_nonnegative _ grade)))

theorem determinantRecipePolynomial_nonnegative (grade : ℕ) {polynomial : Polynomial ℝ}
    (positive : NonnegativeCoefficients polynomial) : NonnegativeCoefficients (determinantRecipePolynomial grade polynomial) :=
  NonnegativeCoefficients.sum Finset.univ _ (fun term _ =>
    (nonnegativeCoefficients_const _ (norm_nonneg (determinantSign term))).mul
      (productPolynomial_nonnegative grade
        (productPolynomial_nonnegative grade
          (scalarEntryRecipePolynomial_nonnegative grade _ _ positive)
          (scalarEntryRecipePolynomial_nonnegative grade _ _ positive))
        (scalarEntryRecipePolynomial_nonnegative grade _ _ positive)))

theorem gaugeRecipePolynomial_nonnegative (grade : ℕ) {seed derivative inverse : Polynomial ℝ}
    (seedPositive : NonnegativeCoefficients seed) (derivativePositive : NonnegativeCoefficients derivative)
    (inversePositive : NonnegativeCoefficients inverse) :
    NonnegativeCoefficients (gaugeRecipePolynomial grade seed derivative inverse) := by
  have column : NonnegativeCoefficients (gaugeColumnPolynomial grade derivative) :=
    (fixedCoefficientPolynomial_nonnegative _ grade).add
      (productPolynomial_nonnegative grade (fixedCoefficientPolynomial_nonnegative _ grade)
        (productPolynomial_nonnegative grade derivativePositive (spatialColumnPolynomial_nonnegative grade)))
  have planar : NonnegativeCoefficients (gaugePlanarPolynomial grade seed) :=
    productPolynomial_nonnegative grade (fixedCoefficientPolynomial_nonnegative _ grade)
      (productPolynomial_nonnegative grade (transposeRecipePolynomial_nonnegative grade 2 2 seedPositive)
        (fixedCoefficientPolynomial_nonnegative _ grade))
  have stack : NonnegativeCoefficients (gaugeStackPolynomial grade seed derivative) := planar.add
    (productPolynomial_nonnegative grade (fixedCoefficientPolynomial_nonnegative _ grade)
      (transposeRecipePolynomial_nonnegative grade 1 3 column))
  exact productPolynomial_nonnegative grade stack (transposeRecipePolynomial_nonnegative grade 3 3 inversePositive)

theorem traceRecipePolynomial_nonnegative (grade : ℕ) {seed inverse : Polynomial ℝ}
    (seedPositive : NonnegativeCoefficients seed) (inversePositive : NonnegativeCoefficients inverse) :
    NonnegativeCoefficients (traceRecipePolynomial grade seed inverse) :=
  productPolynomial_nonnegative grade
    (productPolynomial_nonnegative grade
      (productPolynomial_nonnegative grade
        (transposeRecipePolynomial_nonnegative grade 1 2 (spatialColumnPolynomial_nonnegative grade)) seedPositive)
      (fixedCoefficientPolynomial_nonnegative _ grade))
    (transposeRecipePolynomial_nonnegative grade 3 3 inversePositive)

theorem rotatedRecipePolynomial_nonnegative {columns : ℕ} (grade : ℕ) (selector : Matrix (Fin 3) (Fin columns) ℂ)
    {rotated inverse : Polynomial ℝ} (rotatedPositive : NonnegativeCoefficients rotated)
    (inversePositive : NonnegativeCoefficients inverse) :
    NonnegativeCoefficients (rotatedRecipePolynomial grade selector rotated inverse) :=
  productPolynomial_nonnegative grade
    (transposeRecipePolynomial_nonnegative grade columns 3
      (productPolynomial_nonnegative grade rotatedPositive (fixedCoefficientPolynomial_nonnegative _ grade)))
    (transposeRecipePolynomial_nonnegative grade 3 3 inversePositive)

theorem fluxRecipePolynomial_nonnegative (grade : ℕ) {frame inverse : Polynomial ℝ}
    (framePositive : NonnegativeCoefficients frame) (inversePositive : NonnegativeCoefficients inverse) :
    NonnegativeCoefficients (fluxRecipePolynomial grade frame inverse) :=
  productPolynomial_nonnegative grade
    (scalarLiftRecipePolynomial_nonnegative grade 3 (determinantRecipePolynomial_nonnegative grade framePositive))
    (productPolynomial_nonnegative grade inversePositive (transposeRecipePolynomial_nonnegative grade 3 3 inversePositive))

theorem framePrimitivePolynomial_nonnegative (grade : ℕ) : NonnegativeCoefficients (framePrimitivePolynomial grade) :=
  (fixedCoefficientPolynomial_nonnegative _ grade).add (primitiveLinearPolynomial_nonnegative grade)

theorem seedPrimitivePolynomial_nonnegative (grade : ℕ) : NonnegativeCoefficients (seedPrimitivePolynomial grade) :=
  (identityNormPolynomial_nonnegative grade).add (primitiveLinearPolynomial_nonnegative grade)

end Grad.GaugeCoefficients.Physical.Compensated
