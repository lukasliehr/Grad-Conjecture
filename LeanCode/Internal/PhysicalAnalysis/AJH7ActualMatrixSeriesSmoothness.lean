import AJH5ClosedIntervalSeriesCalculus
import AJH6LiteralMatrixShiftCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter
open scoped BigOperators ENNReal Topology ContDiff
namespace Grad.AnnularRadialSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.BoundaryLift Grad.AnnularKernelContinuity

private theorem polynomialDecay_cancel (frequency constant : ℝ) (positive : 0 < frequency) (power : ℕ) :
    frequency ^ power * (constant * (frequency ^ (power + 4))⁻¹) = constant * (frequency ^ 4)⁻¹ := by
  rw [pow_add]
  field_simp [positive.ne']

/-- Actual matrix coefficients with their checked radial tower act smoothly
in each polynomial Fourier Hilbert norm on the original closed collar. -/
theorem matrixSeries_smooth {source target : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (lower upper : ℝ) (ordered : lower < upper)
    (coefficients : ℕ → ℝ → (ℤ × ℤ) → (ComplexEuclidean source →L[ℂ] ComplexEuclidean target))
    (derivative : ∀ order shift radius, HasDerivAt (fun point => coefficients order point shift)
      (coefficients (order + 1) radius shift) radius)
    (bounds : ∀ order, ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ radius ∈ Icc lower upper, ∀ shift,
        ‖coefficients order radius shift‖ ≤ constant * (annularFrequency shift.1 shift.2 ^ (power + 4))⁻¹)
    (order : ℕ) :
    ContDiffOn ℝ ∞ (fun radius => ∑' shift,
      polynomialMatrixShift parameters power shift (coefficients order radius shift)) (Icc lower upper) := by
  choose constants nonnegative estimates using bounds
  let family := fun order shift radius => polynomialMatrixShift parameters power shift (coefficients order radius shift)
  have derivatives : ∀ order shift radius, HasDerivAt (family order shift) (family (order + 1) shift radius) radius := by
    intro order shift radius
    exact ((polynomialMatrixShift parameters power shift).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt radius
      (derivative order shift radius)
  let majorant := fun (order : ℕ) (shift : ℤ × ℤ) => constants order * (annularFrequency shift.1 shift.2 ^ 4)⁻¹
  have summable : ∀ order, Summable (majorant order) := fun order => fullLattice_decay_summable.mul_left (constants order)
  have bound : ∀ order shift radius, radius ∈ Icc lower upper → ‖family order shift radius‖ ≤ majorant order shift := by
    intro order shift radius inside
    exact (polynomialMatrixShift_bound parameters power shift (coefficients order radius shift)).trans
      ((mul_le_mul_of_nonneg_left (estimates order radius inside shift) (pow_nonneg (annularFrequency_pos shift).le power)).trans_eq
        (polynomialDecay_cancel _ _ (annularFrequency_pos shift) power))
  exact intervalSeries_smooth lower upper ordered family derivatives majorant summable bound order

/-- Exact identity with the accepted input-independent row or matrix kernel;
only the coordinate observation is new. -/
theorem polynomialKernelAction_matrixSeries {source target : ℕ}
    (parameters kernelParameters : PhaseParameters) (power : ℕ)
    (kernel : FullTwoFrequencyKernel kernelParameters source target)
    (coefficients : (ℤ × ℤ) → (ComplexEuclidean source →L[ℂ] ComplexEuclidean target))
    (same : ∀ shift input, kernel.entry shift input = coefficients shift) :
    polynomialKernelAction kernelParameters power kernel =
      ∑' shift, polynomialMatrixShift parameters power shift (coefficients shift) := by
  apply tsum_congr
  intro shift
  exact polynomialShiftAction_constantEntry parameters power shift kernelParameters kernel _ (same shift)

end Grad.AnnularRadialSmoothness
