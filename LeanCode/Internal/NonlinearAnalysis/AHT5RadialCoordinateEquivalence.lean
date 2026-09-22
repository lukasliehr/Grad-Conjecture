import AHT4CompletedKernelLp

noncomputable section
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift

theorem separateRadial_add {dim : ℕ} (lower : ℝ)
    (first second : Lp (CellL2 dim) 2 (volume.restrict (Icc lower 1))) :
    separateRadial lower (first + second) = separateRadial lower first + separateRadial lower second := by
  apply Subtype.ext
  funext mode
  apply Lp.ext
  filter_upwards [separateRadial_ae lower (first + second), separateRadial_ae lower first,
    separateRadial_ae lower second, Lp.coeFn_add first second,
    Lp.coeFn_add (separateRadial lower first mode) (separateRadial lower second mode)]
    with radius total left right inputSum outputSum
  change separateRadial lower (first + second) mode radius =
    (separateRadial lower first mode + separateRadial lower second mode) radius
  rw [total mode, outputSum, Pi.add_apply, left mode, right mode, inputSum]
  rfl

theorem separateRadial_smul {dim : ℕ} (lower : ℝ) (scalar : ℂ)
    (field : Lp (CellL2 dim) 2 (volume.restrict (Icc lower 1))) :
    separateRadial lower (scalar • field) = scalar • separateRadial lower field := by
  apply Subtype.ext
  funext mode
  apply Lp.ext
  filter_upwards [separateRadial_ae lower (scalar • field), separateRadial_ae lower field,
    Lp.coeFn_smul scalar field, Lp.coeFn_smul scalar (separateRadial lower field mode)]
    with radius total original inputScale outputScale
  change separateRadial lower (scalar • field) mode radius =
    (scalar • separateRadial lower field mode) radius
  rw [total mode, outputScale, Pi.smul_apply, original mode, inputScale]
  rfl

/-- The already-proved radial/Fourier realization as an exact linear
isometry, retaining its literal AE coordinate identities. -/
def radialCoordinateEquivalence (dim : ℕ) (lower : ℝ) :
    Lp (CellL2 dim) 2 (volume.restrict (Icc lower 1)) ≃ₗᵢ[ℂ] DivisionRow dim lower where
  toLinearEquiv :=
    { toFun := separateRadial lower
      invFun := collectRadial lower
      left_inv := collect_separateRadial lower
      right_inv := separate_collectRadial lower
      map_add' := separateRadial_add lower
      map_smul' := separateRadial_smul lower }
  norm_map' := separateRadial_norm lower

variable {src tgt : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (lower : ℝ) (radius : ℝ → RadialPoint) (radiusContinuous : Continuous radius)
    (kernel : (x : ℝ) → RadialKernel parameters (radius x) src tgt)
    (entryMeasurable : ∀ shift mode, AEStronglyMeasurable
      (fun x => (kernel x).entry shift mode) (volume.restrict (Icc lower 1)))
    (bound : ℝ)
    (momentBound : ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (radius x)) power (kernel x) ≤ bound)

def completedBulkKernel : DivisionRow src lower →L[ℂ] DivisionRow tgt lower :=
  (radialCoordinateEquivalence tgt lower).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((kernelLpCLM parameters power _ radius radiusContinuous kernel entryMeasurable bound momentBound).comp
      (radialCoordinateEquivalence src lower).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem completedBulkKernel_apply (field : DivisionRow src lower) :
    completedBulkKernel parameters power lower radius radiusContinuous kernel entryMeasurable bound momentBound field =
      separateRadial lower (kernelLp parameters power _ radius radiusContinuous kernel entryMeasurable bound
        momentBound (collectRadial lower field)) := rfl

theorem completedBulkKernel_bound (field : DivisionRow src lower) :
    ‖completedBulkKernel parameters power lower radius radiusContinuous kernel entryMeasurable bound momentBound field‖ ≤
      bound * ‖field‖ := by
  rw [completedBulkKernel_apply, separateRadial_norm]
  simpa only [collectRadial_norm] using kernelLp_norm parameters power _ radius radiusContinuous kernel
    entryMeasurable bound momentBound (collectRadial lower field)

theorem completedBulkKernel_ae (field : DivisionRow src lower) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (bulkWeightRatio parameters power (radius x).val shift mode : ℂ) •
        (kernel x).entry shift (twoFrequencyTranslation shift mode)
          (field (twoFrequencyTranslation shift mode) x))
        (completedBulkKernel parameters power lower radius radiusContinuous kernel entryMeasurable bound momentBound field mode x) := by
  filter_upwards [collectRadial_ae lower field,
    kernelLp_ae parameters power _ radius radiusContinuous kernel entryMeasurable bound momentBound (collectRadial lower field),
    separateRadial_ae lower (kernelLp parameters power _ radius radiusContinuous kernel entryMeasurable bound
      momentBound (collectRadial lower field))] with x collected acted separated
  intro mode
  rw [completedBulkKernel_apply, separated mode, acted]
  simpa only [collected] using bulkKernelAction_coordinate parameters power (radius x) (kernel x)
    (collectRadial lower field x) mode

end Grad.AnnularKernelL2
