import CompletedAverages
import AW3Exponential
import AW1Submultiplicative

noncomputable section

open scoped BigOperators

namespace Grad.Constraints.Multipliers

open Grad.ClosedJets Grad.CartesianState

def envelopeTerm {sourceDimension targetDimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (cell : ℤ) : ℝ :=
  Real.exp (parameters.sigma0 * cellFrequency cell) *
    cellPolynomialWeight cell ^ grade * ‖coefficients cell‖

def envelope {sourceDimension targetDimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) : ℝ :=
  ∑' cell, envelopeTerm parameters grade coefficients cell

/-- The literal original-grade Hilbert coordinates, extended to its actual
norm completion. No alternative norm or weighted-state substitution. -/
def completedCoordinates {dimension grade : ℕ} (parameters : PhaseParameters) :
    AGrade parameters dimension grade →L[ℂ]
      lp (fun _ : ℤ => CartesianGradeRow dimension grade) 2 :=
  (gradeCoreCoordinateIsometry parameters).toContinuousLinearMap.fromCompletion

theorem completedCoordinates_eta {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension grade) :
    completedCoordinates parameters (aGradeEta parameters field) =
      gradeCoreCoordinateIsometry parameters field :=
  ContinuousLinearMap.fromCompletion_apply_coe _ field

/-- The actual coefficient of one Fourier mode multiplier, before summing.
Its weight and every derivative are taken at the output cell. -/
def multiplierRow {sourceDimension targetDimension grade : ℕ} (parameters : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : GradeCore parameters sourceDimension grade) (output shift : ℤ) :
    CartesianGradeRow targetDimension grade :=
  cellGradeRowLinear parameters output
    (valueMapJet (coefficients shift) (field.toCore.1 (output - shift)))

/-- N6–N9 with precisely c_q finite. The resulting product is in the actual
A^q completion; no unjustified all-grade smoothness is required of a.
The all-cell HasSum law identifies all literal weighted derivative rows. -/
def MultiplierGoal : Prop :=
  ∀ (grade : ℕ) (gamma : ℝ), 0 < gamma → gamma < 1 →
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (parameters : PhaseParameters), parameters.gamma = gamma →
      ∀ (sourceDimension targetDimension : ℕ)
        (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension),
        Summable (envelopeTerm parameters grade coefficients) →
        ∃ mapping : AGrade parameters sourceDimension grade →L[ℂ]
            AGrade parameters targetDimension grade,
          (∀ field : AGrade parameters sourceDimension grade,
            ‖mapping field‖ ≤ constant * envelope parameters grade coefficients * ‖field‖) ∧
          (∀ (field : GradeCore parameters sourceDimension grade) (output : ℤ),
            HasSum (multiplierRow parameters coefficients field output)
              (completedCoordinates parameters (mapping (aGradeEta parameters field)) output))

end Grad.Constraints.Multipliers
