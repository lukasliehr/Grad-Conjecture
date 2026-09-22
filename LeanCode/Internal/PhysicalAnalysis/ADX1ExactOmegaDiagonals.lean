import ADW6LiteralOmegaDenseConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularOmegaGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularGrades Grad.AnnularFluxTrace
open Grad.CircularHighRegularity Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- A Fourier diagonal commutes exactly with the original omega-to-nu
normalization. This keeps every split/inserted weight on the same mode. -/
theorem annularOmegaToNu_diagonal (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (coefficient : HighAnnularMode → ℝ)
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (coefficientBound : ∀ mode, |coefficient mode| ≤ constant) (field : AnnularBulk lower) :
    annularOmegaToNu lower length positive lengthPositive
      (realLpDiagonal coefficient constant nonnegative coefficientBound field) =
      realLpDiagonal coefficient constant nonnegative coefficientBound
        (annularOmegaToNu lower length positive lengthPositive field) := by
  unfold annularOmegaToNu annularScalarFamily
  exact (realLpDiagonal_commutes coefficient constant nonnegative coefficientBound _ _ _ _ field).symm

/-- The proved reciprocal normalization commutes with the same diagonal. -/
theorem annularNuToOmega_diagonal (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (coefficient : HighAnnularMode → ℝ)
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (coefficientBound : ∀ mode, |coefficient mode| ≤ constant) (field : AnnularBulk lower) :
    annularNuToOmega lower length positive lengthPositive
      (realLpDiagonal coefficient constant nonnegative coefficientBound field) =
      realLpDiagonal coefficient constant nonnegative coefficientBound
        (annularNuToOmega lower length positive lengthPositive field) := by
  unfold annularNuToOmega annularScalarFamily
  exact (realLpDiagonal_commutes coefficient constant nonnegative coefficientBound _ _ _ _ field).symm

section Diagonal
variable (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (coefficient : HighAnnularMode → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (coefficientBound : ∀ mode, |coefficient mode| ≤ constant)

/-- The literal Domega diagonal, transported through the exact reciprocal
equivalence to the accepted distributional Dnu graph. -/
def annularOmegaGraphDiagonal :
    annularOmegaGraph lower length positive lengthPositive →L[ℂ]
      annularOmegaGraph lower length positive lengthPositive :=
  (annularOmegaNormalizationEquivalence lower length positive lengthPositive).symm.toContinuousLinearMap.comp
    ((annularFluxGraphDiagonal lower positive coefficient constant nonnegative coefficientBound).comp
      (annularOmegaNormalizationEquivalence lower length positive lengthPositive).toContinuousLinearMap)

theorem annularOmegaNormalization_diagonal
    (field : annularOmegaGraph lower length positive lengthPositive) :
    annularOmegaNormalizationEquivalence lower length positive lengthPositive
      (annularOmegaGraphDiagonal lower length positive lengthPositive coefficient constant nonnegative
        coefficientBound field) =
      annularFluxGraphDiagonal lower positive coefficient constant nonnegative coefficientBound
        (annularOmegaNormalizationEquivalence lower length positive lengthPositive field) := by
  change (annularOmegaNormalizationEquivalence lower length positive lengthPositive)
    ((annularOmegaNormalizationEquivalence lower length positive lengthPositive).symm
      (annularFluxGraphDiagonal lower positive coefficient constant nonnegative coefficientBound
        (annularOmegaNormalizationEquivalence lower length positive lengthPositive field))) = _
  exact (annularOmegaNormalizationEquivalence lower length positive lengthPositive).apply_symm_apply _

/-- The value coordinate is literally multiplied by the chosen Fourier scalar. -/
theorem annularOmegaGraphDiagonal_value
    (field : annularOmegaGraph lower length positive lengthPositive) :
    (annularOmegaGraphDiagonal lower length positive lengthPositive coefficient constant nonnegative
      coefficientBound field).val 0 =
      realLpDiagonal coefficient constant nonnegative coefficientBound (field.val 0) := by
  have normalized := congrArg (fun output : annularFluxWeakGraph lower positive => output.val.1)
    (annularOmegaNormalization_diagonal lower length positive lengthPositive coefficient constant
      nonnegative coefficientBound field)
  change (annularOmegaGraphDiagonal lower length positive lengthPositive coefficient constant nonnegative
    coefficientBound field).val 0 =
      realLpDiagonal coefficient constant nonnegative coefficientBound (field.val 0) at normalized
  exact normalized

/-- The normalized derivative coordinate is also literally multiplied by
the chosen scalar; injectivity of omega-to-nu removes the comparison map. -/
theorem annularOmegaGraphDiagonal_slope
    (field : annularOmegaGraph lower length positive lengthPositive) :
    (annularOmegaGraphDiagonal lower length positive lengthPositive coefficient constant nonnegative
      coefficientBound field).val 1 =
      realLpDiagonal coefficient constant nonnegative coefficientBound (field.val 1) := by
  apply annularOmegaToNu_injective lower length positive lengthPositive
  have normalized := congrArg (fun output : annularFluxWeakGraph lower positive => output.val.2)
    (annularOmegaNormalization_diagonal lower length positive lengthPositive coefficient constant
      nonnegative coefficientBound field)
  change annularOmegaToNu lower length positive lengthPositive
      ((annularOmegaGraphDiagonal lower length positive lengthPositive coefficient constant nonnegative
        coefficientBound field).val 1) =
    realLpDiagonal coefficient constant nonnegative coefficientBound
      (annularOmegaToNu lower length positive lengthPositive (field.val 1)) at normalized
  exact normalized.trans
    (annularOmegaToNu_diagonal lower length positive lengthPositive coefficient constant nonnegative
      coefficientBound (field.val 1)).symm

theorem annularOmegaGraphDiagonal_injective
    (coefficientNonzero : ∀ mode, coefficient mode ≠ 0) :
    Function.Injective (annularOmegaGraphDiagonal lower length positive lengthPositive coefficient constant
      nonnegative coefficientBound) := by
  intro first second equality
  apply Subtype.ext
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · have same := congrArg
      (fun output : annularOmegaGraph lower length positive lengthPositive => output.val 0) equality
    rw [annularOmegaGraphDiagonal_value, annularOmegaGraphDiagonal_value] at same
    simpa using (realLpDiagonal_injective coefficient constant nonnegative coefficientBound
      coefficientNonzero same)
  · have same := congrArg
      (fun output : annularOmegaGraph lower length positive lengthPositive => output.val 1) equality
    rw [annularOmegaGraphDiagonal_slope, annularOmegaGraphDiagonal_slope] at same
    simpa using (realLpDiagonal_injective coefficient constant nonnegative coefficientBound
      coefficientNonzero same)

end Diagonal
end Grad.AnnularOmegaGraph
