import AHT5RadialCoordinateEquivalence

noncomputable section
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift

theorem bulkWeightRatio_decode (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (positive : 0 < radius) (shift mode : ℤ × ℤ) :
    (originalRowWeight parameters power radius mode : ℂ)⁻¹ *
      (bulkWeightRatio parameters power radius shift mode : ℂ) =
      (originalRowWeight parameters power radius (twoFrequencyTranslation shift mode) : ℂ)⁻¹ := by
  rw [bulkWeightRatio_original parameters power radius positive]
  push_cast
  field_simp [(originalRowWeight_pos parameters power radius positive mode).ne']

variable {src tgt : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (lower : ℝ) (positive : 0 < lower)
    (radius : ℝ → RadialPoint) (radiusContinuous : Continuous radius)
    (radiusLiteral : ∀ᵐ x ∂volume.restrict (Icc lower 1), (radius x).val = x)
    (kernel : (x : ℝ) → RadialKernel parameters (radius x) src tgt)
    (entryMeasurable : ∀ shift mode, AEStronglyMeasurable
      (fun x => (kernel x).entry shift mode) (volume.restrict (Icc lower 1)))
    (bound : ℝ)
    (momentBound : ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (radius x)) power (kernel x) ≤ bound)

include positive radiusLiteral in
/-- Exact original physical Fourier action on the completed annular r dr
space, with the original analytic phase and total grade. -/
theorem completedBulkKernel_physical (field : DivisionRow src lower) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (kernel x).entry shift (twoFrequencyTranslation shift mode)
        (originalRowCoefficient parameters power lower field x (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower
          (completedBulkKernel parameters power lower radius radiusContinuous kernel entryMeasurable bound momentBound field) x mode) := by
  filter_upwards [completedBulkKernel_ae parameters power lower radius radiusContinuous kernel
    entryMeasurable bound momentBound field, radiusLiteral, ae_restrict_mem measurableSet_Icc]
    with x coefficients radiusAt inside
  intro mode
  have sum := coefficients mode
  rw [radiusAt] at sum
  have scaled := ((originalRowWeight parameters power x mode : ℂ)⁻¹ •
    ContinuousLinearMap.id ℂ (ComplexEuclidean tgt)).hasSum sum
  change HasSum (fun shift => (originalRowWeight parameters power x mode : ℂ)⁻¹ •
    ((bulkWeightRatio parameters power x shift mode : ℂ) •
      (kernel x).entry shift (twoFrequencyTranslation shift mode)
        (field (twoFrequencyTranslation shift mode) x)))
    (originalRowCoefficient parameters power lower
      (completedBulkKernel parameters power lower radius radiusContinuous kernel entryMeasurable bound momentBound field) x mode) at scaled
  apply scaled.congr_fun
  intro shift
  rw [originalRowCoefficient, map_smul, smul_smul,
    bulkWeightRatio_decode parameters power x (positive.trans_le inside.1)]

end Grad.AnnularKernelL2
