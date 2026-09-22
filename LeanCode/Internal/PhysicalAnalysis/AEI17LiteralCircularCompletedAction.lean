import AEI16ActualNormalizedLowResponse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.ActualBoundaryPrimitives Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger

open Grad.SourceCollarCoefficients

/-- The accepted completed kernel action collapses to its literal zero-shift
entry when all nonzero shifts vanish. -/
theorem lowZeroShiftAction_ae {src tgt : ℕ} (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius src tgt)
    (regular : RegularKernelFamily kernel) (diagonal : ∀ radius, ZeroShiftKernel (kernel radius))
    (field : DivisionRow src lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      regularRadialBulkAction parameters 0 lower positive bounded kernel regular field mode radius =
        (kernel (collarRadius lower positive bounded radius)).entry (0, 0) mode (field mode radius) := by
  unfold regularRadialBulkAction
  filter_upwards [completedBulkKernel_ae parameters 0 lower (collarRadius lower positive bounded)
    (collarRadius_continuous lower positive bounded) (fun radius => kernel (collarRadius lower positive bounded radius))
    (regularRadialBulk_measurable parameters lower positive bounded kernel regular)
    (regularRadialBulkBound parameters 0 kernel regular)
    (regularRadialBulk_moment parameters 0 lower positive bounded kernel regular) field] with radius actual
  intro mode
  rw [← (actual mode).tsum_eq]
  rw [tsum_eq_single (0, 0) (by
    intro shift nonzero
    rw [diagonal (collarRadius lower positive bounded radius) shift nonzero]
    simp only [zero_apply, smul_zero])]
  rw [bulkWeightRatio_zero]
  simp only [Complex.ofReal_one, one_smul, twoFrequencyTranslation_apply, sub_zero]

theorem lowCircularRowKernel_zeroShift (parameters : PhaseParameters) (length : ℝ) (row : Fin 3) (radius : RadialPoint) :
    ZeroShiftKernel (lowCircularRowKernel parameters length row radius) := by
  fin_cases row
  · exact circularNormalizedUnprojectedFirstRowKernel_zeroShift _ _
  · exact circularNormalizedUnprojectedCKernel_zeroShift _ _
  · exact circularNormalizedPhysicalRVKernel_zeroShift _ _

theorem lowCircularRowAction_ae (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (row : Fin 3) (field : DivisionRow 7 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      lowCircularRowAction parameters length lower positive bounded row field mode radius =
        (lowCircularRowKernel parameters length row (collarRadius lower positive bounded radius)).entry (0, 0) mode (field mode radius) :=
  lowZeroShiftAction_ae parameters lower positive bounded (lowCircularRowKernel parameters length row)
    (lowCircularRowKernel_regular parameters length row) (lowCircularRowKernel_zeroShift parameters length row) field

end Grad.AnnularCurrentLow
