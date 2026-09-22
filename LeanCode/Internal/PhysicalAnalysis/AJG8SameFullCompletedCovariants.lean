import AJG7ActualSharedSevenCompatibility
import AHT10UniformNormalizedActions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Grad.AnnularPhysicalReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularReconstruction
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularKernelContinuity
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularCurrentLow

theorem regularRadialBulkAction_collected {source target : ℕ} (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target)
    (regular : RegularKernelFamily kernel) (field : DivisionRow source lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      collectRadial lower (regularRadialBulkAction parameters 0 lower positive bounded kernel regular field) radius =
        bulkKernelAction parameters 0 (collarRadius lower positive bounded radius)
          (kernel (collarRadius lower positive bounded radius)) (collectRadial lower field radius) :=
  completedBulkKernel_collect_ae parameters 0 lower (collarRadius lower positive bounded)
    (collarRadius_continuous lower positive bounded) _
    (regularRadialBulk_measurable parameters lower positive bounded kernel regular)
    (regularRadialBulkBound parameters 0 kernel regular)
    (regularRadialBulk_moment parameters 0 lower positive bounded kernel regular) field

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < L)
    (state : AnnularReconstructionState parameters L compact)

def fullCovariantAction : DivisionRow 7 lower →L[ℂ] DivisionRow 3 lower :=
  regularRadialBulkAction parameters 0 lower positive bounded
    (fun radius => radialNormalizedCovariantKernel parameters L compact state.val radius state.property)
    (radialNormalizedCovariantKernel_regular parameters L compact state)

def fullRotatedCovariantAction : DivisionRow 7 lower →L[ℂ] DivisionRow 3 lower :=
  regularRadialBulkAction parameters 0 lower positive bounded
    (fun radius => radialNormalizedRotatedCovariantKernel parameters L compact state.val radius state.property)
    (radialNormalizedRotatedCovariantKernel_regular parameters L compact state)

theorem fullCovariantAction_same : fullCovariantAction parameters L compact lower positive bounded state =
    normalizedCovariantAction parameters L compact lower positive bounded state 0 :=
  regularRadialBulkAction_eq_completed parameters 0 lower positive bounded _
    (radialNormalizedCovariantKernel_regular parameters L compact state)
    (normalizedCovariantFamily_measurable parameters L compact lower positive bounded state)
    _ (normalizedCovariantFamily_moment parameters L compact lower positive bounded state 0)

theorem fullRotatedCovariantAction_same : fullRotatedCovariantAction parameters L compact lower positive bounded state =
    normalizedRotatedAction parameters L compact lower positive bounded state 0 :=
  regularRadialBulkAction_eq_completed parameters 0 lower positive bounded _
    (radialNormalizedRotatedCovariantKernel_regular parameters L compact state)
    (normalizedRotatedFamily_measurable parameters L compact lower positive bounded state)
    _ (normalizedRotatedFamily_moment parameters L compact lower positive bounded state 0)

/-- The covariant and its genuine angular derivative are reconstructed once
from the SAME high/low solution and SAME shared F0/RF0/F2. -/
def sharedFullCovariant (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (solution : CoupledSpace lower L positive lengthPositive) : DivisionRow 3 lower :=
  fullCovariantAction parameters L compact lower positive bounded state
    (fullStrongSevenInput parameters L lower lengthPositive positive bounded data solution)

def sharedFullRotatedCovariant (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (solution : CoupledSpace lower L positive lengthPositive) : DivisionRow 3 lower :=
  fullRotatedCovariantAction parameters L compact lower positive bounded state
    (fullStrongSevenInput parameters L lower lengthPositive positive bounded data solution)

theorem sharedFullCovariant_collected (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (solution : CoupledSpace lower L positive lengthPositive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      collectRadial lower (sharedFullCovariant parameters L compact lower positive bounded lengthPositive state data solution) radius =
        bulkCovariant parameters L compact state (collarRadius lower positive bounded radius)
          (collectRadial lower (fullStrongSevenInput parameters L lower lengthPositive positive bounded data solution) radius) :=
  regularRadialBulkAction_collected parameters lower positive bounded _
    (radialNormalizedCovariantKernel_regular parameters L compact state) _

theorem sharedFullRotatedCovariant_collected (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (solution : CoupledSpace lower L positive lengthPositive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      collectRadial lower (sharedFullRotatedCovariant parameters L compact lower positive bounded lengthPositive state data solution) radius =
        bulkRotatedCovariant parameters L compact state (collarRadius lower positive bounded radius)
          (collectRadial lower (fullStrongSevenInput parameters L lower lengthPositive positive bounded data solution) radius) :=
  regularRadialBulkAction_collected parameters lower positive bounded _
    (radialNormalizedRotatedCovariantKernel_regular parameters L compact state) _

/-- Literal convolution of the original physical coefficients, with the
shared rho weight removed by the already accepted exact cancellation. -/
theorem sharedFullCovariant_physical (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (solution : CoupledSpace lower L positive lengthPositive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift =>
        (radialNormalizedCovariantKernel parameters L compact state.val (collarRadius lower positive bounded radius) state.property).entry
          shift (twoFrequencyTranslation shift mode)
          (lowRhoPhysicalCoefficient parameters lower positive
            (fullStrongSevenInput parameters L lower lengthPositive positive bounded data solution) radius (twoFrequencyTranslation shift mode)))
        (lowRhoPhysicalCoefficient parameters lower positive
          (sharedFullCovariant parameters L compact lower positive bounded lengthPositive state data solution) radius mode) :=
  lowRegularAction_physical parameters lower positive bounded _
    (radialNormalizedCovariantKernel_regular parameters L compact state) _

theorem sharedFullRotatedCovariant_physical (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (solution : CoupledSpace lower L positive lengthPositive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift =>
        (radialNormalizedRotatedCovariantKernel parameters L compact state.val (collarRadius lower positive bounded radius) state.property).entry
          shift (twoFrequencyTranslation shift mode)
          (lowRhoPhysicalCoefficient parameters lower positive
            (fullStrongSevenInput parameters L lower lengthPositive positive bounded data solution) radius (twoFrequencyTranslation shift mode)))
        (lowRhoPhysicalCoefficient parameters lower positive
          (sharedFullRotatedCovariant parameters L compact lower positive bounded lengthPositive state data solution) radius mode) :=
  lowRegularAction_physical parameters lower positive bounded _
    (radialNormalizedRotatedCovariantKernel_regular parameters L compact state) _

end Grad.AnnularPhysicalReconstruction
