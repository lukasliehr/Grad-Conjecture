import AHX3BulkKernelAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift

variable {src mid tgt : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (measure : Measure ℝ) (radius : ℝ → RadialPoint) (radiusContinuous : Continuous radius)
    (outer : (x : ℝ) → RadialKernel parameters (radius x) mid tgt)
    (inner : (x : ℝ) → RadialKernel parameters (radius x) src mid)
    (outerMeasurable : ∀ shift mode, AEStronglyMeasurable (fun x => (outer x).entry shift mode) measure)
    (innerMeasurable : ∀ shift mode, AEStronglyMeasurable (fun x => (inner x).entry shift mode) measure)
    (compositionMeasurable : ∀ shift mode, AEStronglyMeasurable
      (fun x => (fullKernelComposition (outer x) (inner x)).entry shift mode) measure)
    (outerBound innerBound compositionBound : ℝ)
    (outerMoment : ∀ᵐ x ∂measure, fullKernelMoment (radialKernelParameters parameters (radius x)) power (outer x) ≤ outerBound)
    (innerMoment : ∀ᵐ x ∂measure, fullKernelMoment (radialKernelParameters parameters (radius x)) power (inner x) ≤ innerBound)
    (compositionMoment : ∀ᵐ x ∂measure,
      fullKernelMoment (radialKernelParameters parameters (radius x)) power
        (fullKernelComposition (outer x) (inner x)) ≤ compositionBound)

/-- Composition passes through the actual Bochner L2 realization. All
coefficient hypotheses are precisely those of the existing construction. -/
theorem kernelLp_comp (field : Lp (CellL2 src) 2 measure) :
    kernelLp parameters power measure radius radiusContinuous
      (fun x => fullKernelComposition (outer x) (inner x)) compositionMeasurable
      compositionBound compositionMoment field =
    kernelLp parameters power measure radius radiusContinuous outer outerMeasurable outerBound outerMoment
      (kernelLp parameters power measure radius radiusContinuous inner innerMeasurable innerBound innerMoment field) := by
  apply Lp.ext
  filter_upwards [kernelLp_ae parameters power measure radius radiusContinuous
      (fun x => fullKernelComposition (outer x) (inner x)) compositionMeasurable compositionBound compositionMoment field,
    kernelLp_ae parameters power measure radius radiusContinuous inner innerMeasurable innerBound innerMoment field,
    kernelLp_ae parameters power measure radius radiusContinuous outer outerMeasurable outerBound outerMoment
      (kernelLp parameters power measure radius radiusContinuous inner innerMeasurable innerBound innerMoment field)]
      with x composed first second
  rw [composed, second, first, bulkKernelAction_comp, ContinuousLinearMap.comp_apply]

/-- The completed original annular Fourier/radial operator respects exact
kernel composition, independently of the bound witnesses used to build it. -/
theorem completedBulkKernel_comp (lower : ℝ)
    (outerMeasurable : ∀ shift mode, AEStronglyMeasurable (fun x => (outer x).entry shift mode) (volume.restrict (Icc lower 1)))
    (innerMeasurable : ∀ shift mode, AEStronglyMeasurable (fun x => (inner x).entry shift mode) (volume.restrict (Icc lower 1)))
    (compositionMeasurable : ∀ shift mode, AEStronglyMeasurable
      (fun x => (fullKernelComposition (outer x) (inner x)).entry shift mode) (volume.restrict (Icc lower 1)))
    (outerMoment : ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (radius x)) power (outer x) ≤ outerBound)
    (innerMoment : ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (radius x)) power (inner x) ≤ innerBound)
    (compositionMoment : ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (radius x)) power
        (fullKernelComposition (outer x) (inner x)) ≤ compositionBound) :
    completedBulkKernel parameters power lower radius radiusContinuous
      (fun x => fullKernelComposition (outer x) (inner x)) compositionMeasurable compositionBound compositionMoment =
      (completedBulkKernel parameters power lower radius radiusContinuous outer outerMeasurable outerBound outerMoment).comp
        (completedBulkKernel parameters power lower radius radiusContinuous inner innerMeasurable innerBound innerMoment) := by
  apply ContinuousLinearMap.ext
  intro field
  rw [ContinuousLinearMap.comp_apply, completedBulkKernel_apply, completedBulkKernel_apply,
    completedBulkKernel_apply, collect_separateRadial]
  exact congrArg (separateRadial lower) (kernelLp_comp parameters power (volume.restrict (Icc lower 1))
    radius radiusContinuous outer inner outerMeasurable innerMeasurable compositionMeasurable
    outerBound innerBound compositionBound outerMoment innerMoment compositionMoment (collectRadial lower field))

end Grad.AnnularKernelL2
