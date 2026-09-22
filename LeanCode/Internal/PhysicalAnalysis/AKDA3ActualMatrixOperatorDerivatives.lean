import AKDA2SameOriginalInverseDerivative
import AJH7ActualMatrixSeriesSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter
open scoped ContDiff BigOperators Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2
open Grad.AnnularRadialSmoothness Grad.AnnularKernelContinuity

/-- Actual derivative of the original unreserved polynomial matrix series,
using the accepted closed-interval summable derivative theorem. -/
theorem matrixSeries_zero_hasDerivWithinAt {source target : ℕ} (parameters : PhaseParameters)
    (lower upper : ℝ) (ordered : lower < upper)
    (coefficients : ℕ → ℝ → (ℤ × ℤ) → (ComplexEuclidean source →L[ℂ] ComplexEuclidean target))
    (derivative : ∀ order shift radius, HasDerivAt (fun point => coefficients order point shift)
      (coefficients (order+1) radius shift) radius)
    (bounds : ∀ order, ∃ constant : ℝ, 0 ≤ constant ∧ ∀ radius ∈ Icc lower upper, ∀ shift,
      ‖coefficients order radius shift‖ ≤ constant*(annularFrequency shift.1 shift.2^4)⁻¹)
    (order : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower upper) :
    HasDerivWithinAt (fun point => ∑' shift, polynomialMatrixShift parameters 0 shift (coefficients order point shift))
      (∑' shift, polynomialMatrixShift parameters 0 shift (coefficients (order+1) radius shift))
      (Icc lower upper) radius := by
  choose constants nonnegative estimates using bounds
  let family := fun order shift point => polynomialMatrixShift parameters 0 shift (coefficients order point shift)
  have derivatives : ∀ order shift point, HasDerivAt (family order shift) (family (order+1) shift point) point := by
    intro order shift point
    exact ((polynomialMatrixShift parameters 0 shift).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt point
      (derivative order shift point)
  let majorant := fun order (shift : ℤ × ℤ) => constants order*(annularFrequency shift.1 shift.2^4)⁻¹
  have summable : ∀ order, Summable (majorant order) := fun order => fullLattice_decay_summable.mul_left (constants order)
  have bound : ∀ order shift point, point ∈ Icc lower upper → ‖family order shift point‖ ≤ majorant order shift := by
    intro order shift point member
    have matrix := polynomialMatrixShift_bound parameters 0 shift (coefficients order point shift)
    simp only [pow_zero,one_mul] at matrix
    exact matrix.trans (estimates order point member shift)
  exact intervalSeries_hasFDerivWithinAt lower upper ordered family derivatives majorant summable bound order radius inside

/-- Full original matrix radial jets realize the actual bounded-operator
radial derivative on the closed positive collar. No forward-operator
smoothness or derivative is inserted as an assumption. -/
theorem actualMatrixKernelAction_hasDerivWithinAt {source target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (kernels : ℕ → (radius : RadialPoint) → RadialKernel parameters radius source target)
    (coefficients : ℕ → ℝ → (ℤ × ℤ) → (ComplexEuclidean source →L[ℂ] ComplexEuclidean target))
    (same : ∀ order radius shift input, (kernels order radius).entry shift input = coefficients order radius.val shift)
    (derivative : ∀ order shift radius, HasDerivAt (fun point => coefficients order point shift)
      (coefficients (order+1) radius shift) radius)
    (regular : ∀ order, RegularKernelFamily (kernels order))
    (order : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (radialPolynomialAction parameters lower positive bounded.le (kernels order) 0)
      (radialPolynomialAction parameters lower positive bounded.le (kernels (order+1)) 0 radius)
      (Icc lower 1) radius := by
  have bounds : ∀ order, ∃ constant : ℝ, 0 ≤ constant ∧ ∀ point ∈ Icc lower 1, ∀ shift,
      ‖coefficients order point shift‖ ≤ constant*(annularFrequency shift.1 shift.2^4)⁻¹ := by
    intro order
    obtain ⟨constant,nonnegative,bound⟩ := (regular order).2 4
    refine ⟨constant,nonnegative,?_⟩
    intro point member shift
    let actual : RadialPoint := ⟨point,positive.le.trans member.1,member.2⟩
    rw [← same order actual shift (0,0)]
    exact ((kernels order actual).entry_le shift (0,0)).trans
      (fullKernelEntryNorm_decay _ (kernels order actual) 4 constant (bound actual) shift)
  have derived := matrixSeries_zero_hasDerivWithinAt parameters lower 1 bounded coefficients derivative bounds order radius inside
  have exactSeries (raw : ℕ) (point : ℝ) (member : point ∈ Icc lower 1) :
      radialPolynomialAction parameters lower positive bounded.le (kernels raw) 0 point =
        ∑' shift, polynomialMatrixShift parameters 0 shift (coefficients raw point shift) := by
    unfold radialPolynomialAction
    rw [polynomialKernelAction_matrixSeries parameters _ 0 _
      (coefficients raw (collarRadius lower positive bounded.le point).val) (same raw _)]
    rw [collarRadius_literal lower positive bounded.le point member]
  rw [← exactSeries (order+1) radius inside] at derived
  apply derived.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with point member
    exact exactSeries order point member
  · exact exactSeries order radius inside

end Grad.OriginalCartesianTameEstimate
