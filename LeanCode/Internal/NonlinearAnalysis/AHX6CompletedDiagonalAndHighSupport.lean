import AHX5CompletedKernelLinearAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift Grad.ActualBoundaryPrimitives

variable {src tgt : ℕ} (parameters : PhaseParameters) (power : ℕ) (lower : ℝ)
    (radius : ℝ → RadialPoint) (radiusContinuous : Continuous radius)

/-- Literal diagonal coefficients on the completed original annular carrier. -/
theorem completedBulkKernel_diagonal_ae
    (diagonal : ℝ → (ℤ × ℤ) → ComplexEuclidean src →L[ℂ] ComplexEuclidean tgt)
    (diagonalBound : ℝ → ℝ) (diagonalNorm : ∀ x mode, ‖diagonal x mode‖ ≤ diagonalBound x)
    (measurable : ∀ shift mode, AEStronglyMeasurable
      (fun x => (modeDiagonalKernel (radialKernelParameters parameters (radius x)) src tgt
        (diagonal x) (diagonalBound x) (diagonalNorm x)).entry shift mode) (volume.restrict (Icc lower 1)))
    (bound : ℝ) (moment : ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (radius x)) power
        (modeDiagonalKernel (radialKernelParameters parameters (radius x)) src tgt
          (diagonal x) (diagonalBound x) (diagonalNorm x)) ≤ bound)
    (field : DivisionRow src lower) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1), ∀ mode,
      completedBulkKernel parameters power lower radius radiusContinuous
        (fun x => modeDiagonalKernel (radialKernelParameters parameters (radius x)) src tgt
          (diagonal x) (diagonalBound x) (diagonalNorm x)) measurable bound moment field mode x =
      diagonal x mode (field mode x) := by
  let action := completedBulkKernel parameters power lower radius radiusContinuous
    (fun x => modeDiagonalKernel (radialKernelParameters parameters (radius x)) src tgt
      (diagonal x) (diagonalBound x) (diagonalNorm x)) measurable bound moment
  filter_upwards [collectRadial_ae lower field, collectRadial_ae lower (action field),
    completedBulkKernel_collect_ae parameters power lower radius radiusContinuous
      (fun x => modeDiagonalKernel (radialKernelParameters parameters (radius x)) src tgt
        (diagonal x) (diagonalBound x) (diagonalNorm x)) measurable bound moment field]
      with x input output actual
  intro mode
  change action field mode x = _
  rw [← output mode]
  rw [actual, bulkKernelAction_diagonal, input mode]

/-- Exact high support of a completed kernel already left-projected by Q. -/
theorem completedBulkKernel_high
    (kernel : (x : ℝ) → RadialKernel parameters (radius x) src tgt)
    (measurable : ∀ shift mode, AEStronglyMeasurable (fun x => (kernel x).entry shift mode) (volume.restrict (Icc lower 1)))
    (bound : ℝ) (moment : ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (radius x)) power (kernel x) ≤ bound)
    (high : ∀ x, fullKernelComposition (highAngularKernel (radialKernelParameters parameters (radius x)) tgt)
      (kernel x) = kernel x) (field : DivisionRow src lower) (mode : ℤ × ℤ) (low : |mode.1| < 3) :
    completedBulkKernel parameters power lower radius radiusContinuous kernel measurable bound moment field mode = 0 := by
  apply Lp.ext
  filter_upwards [completedBulkKernel_ae parameters power lower radius radiusContinuous kernel measurable bound moment field,
    Lp.coeFn_zero (ComplexEuclidean tgt) 2 (volume.restrict (Icc lower 1))] with x actual zeroValue
  rw [zeroValue]
  change _ = (0 : ComplexEuclidean tgt)
  have allZero (shift : ℤ × ℤ) :
      (bulkWeightRatio parameters power (radius x).val shift mode : ℂ) •
        (kernel x).entry shift (twoFrequencyTranslation shift mode) (field (twoFrequencyTranslation shift mode) x) = 0 := by
    rw [← high x, highAngularKernel_comp_entry_low _ _ _ _ (by
      change |(mode.1 - shift.1) + shift.1| < 3
      simpa only [sub_add_cancel] using low), zero_apply, smul_zero]
  exact (actual mode).unique (by simpa only [allZero] using (hasSum_zero : HasSum (fun _ : ℤ × ℤ => (0 : ComplexEuclidean tgt)) 0))

end Grad.AnnularKernelL2
