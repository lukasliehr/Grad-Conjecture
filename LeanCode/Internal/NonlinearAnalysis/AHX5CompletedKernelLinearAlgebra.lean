import AHX4CompletedKernelComposition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift

variable {src tgt : ℕ} (parameters : PhaseParameters) (power : ℕ) (lower : ℝ)
    (radius : ℝ → RadialPoint) (radiusContinuous : Continuous radius)
    (first second : (x : ℝ) → RadialKernel parameters (radius x) src tgt)
    (firstMeasurable : ∀ shift mode, AEStronglyMeasurable (fun x => (first x).entry shift mode) (volume.restrict (Icc lower 1)))
    (secondMeasurable : ∀ shift mode, AEStronglyMeasurable (fun x => (second x).entry shift mode) (volume.restrict (Icc lower 1)))
    (firstBound secondBound : ℝ)
    (firstMoment : ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (radius x)) power (first x) ≤ firstBound)
    (secondMoment : ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (radius x)) power (second x) ≤ secondBound)

/-- Literal collected representative of the existing completed operator. -/
theorem completedBulkKernel_collect_ae (field : DivisionRow src lower) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1),
      collectRadial lower
        (completedBulkKernel parameters power lower radius radiusContinuous first firstMeasurable firstBound firstMoment field) x =
      bulkKernelAction parameters power (radius x) (first x) (collectRadial lower field x) := by
  rw [completedBulkKernel_apply, collect_separateRadial]
  exact kernelLp_ae parameters power _ radius radiusContinuous first firstMeasurable firstBound firstMoment _

/-- Bound witnesses do not change the actual completed operator. -/
theorem completedBulkKernel_congr
    (same : ∀ᵐ x ∂volume.restrict (Icc lower 1), first x = second x) :
    completedBulkKernel parameters power lower radius radiusContinuous first firstMeasurable firstBound firstMoment =
      completedBulkKernel parameters power lower radius radiusContinuous second secondMeasurable secondBound secondMoment := by
  apply ContinuousLinearMap.ext
  intro field
  apply (radialCoordinateEquivalence tgt lower).symm.injective
  apply Lp.ext
  filter_upwards [completedBulkKernel_collect_ae parameters power lower radius radiusContinuous
      first firstMeasurable firstBound firstMoment field,
    completedBulkKernel_collect_ae parameters power lower radius radiusContinuous
      second secondMeasurable secondBound secondMoment field, same] with x left right equal
  change collectRadial lower _ x = collectRadial lower _ x
  rw [left, right, equal]

/-- Exact subtraction of full kernel families passes to original completed L2. -/
theorem completedBulkKernel_sub
    (differenceMeasurable : ∀ shift mode, AEStronglyMeasurable
      (fun x => (fullKernelSub (first x) (second x)).entry shift mode) (volume.restrict (Icc lower 1)))
    (differenceBound : ℝ)
    (differenceMoment : ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (radius x)) power
        (fullKernelSub (first x) (second x)) ≤ differenceBound) :
    completedBulkKernel parameters power lower radius radiusContinuous
      (fun x => fullKernelSub (first x) (second x)) differenceMeasurable differenceBound differenceMoment =
      completedBulkKernel parameters power lower radius radiusContinuous first firstMeasurable firstBound firstMoment -
        completedBulkKernel parameters power lower radius radiusContinuous second secondMeasurable secondBound secondMoment := by
  apply ContinuousLinearMap.ext
  intro field
  apply (radialCoordinateEquivalence tgt lower).symm.injective
  change collectRadial lower
    (completedBulkKernel parameters power lower radius radiusContinuous
      (fun x => fullKernelSub (first x) (second x)) differenceMeasurable differenceBound differenceMoment field) =
    (radialCoordinateEquivalence tgt lower).symm
      (completedBulkKernel parameters power lower radius radiusContinuous first firstMeasurable firstBound firstMoment field -
        completedBulkKernel parameters power lower radius radiusContinuous second secondMeasurable secondBound secondMoment field)
  rw [map_sub]
  apply Lp.ext
  filter_upwards [completedBulkKernel_collect_ae parameters power lower radius radiusContinuous
      (fun x => fullKernelSub (first x) (second x)) differenceMeasurable differenceBound differenceMoment field,
    completedBulkKernel_collect_ae parameters power lower radius radiusContinuous
      first firstMeasurable firstBound firstMoment field,
    completedBulkKernel_collect_ae parameters power lower radius radiusContinuous
      second secondMeasurable secondBound secondMoment field,
    Lp.coeFn_sub
      (collectRadial lower (completedBulkKernel parameters power lower radius radiusContinuous first firstMeasurable firstBound firstMoment field))
      (collectRadial lower (completedBulkKernel parameters power lower radius radiusContinuous second secondMeasurable secondBound secondMoment field))]
    with x difference left right subtraction
  change collectRadial lower
      (completedBulkKernel parameters power lower radius radiusContinuous
        (fun x => fullKernelSub (first x) (second x)) differenceMeasurable differenceBound differenceMoment field) x =
    (collectRadial lower (completedBulkKernel parameters power lower radius radiusContinuous first firstMeasurable firstBound firstMoment field) -
      collectRadial lower (completedBulkKernel parameters power lower radius radiusContinuous second secondMeasurable secondBound secondMoment field)) x
  rw [subtraction, Pi.sub_apply, difference, left, right, bulkKernelAction_sub, sub_apply]

end Grad.AnnularKernelL2
