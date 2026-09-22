import AEI13OriginalLowStoredPhysicalFidelity
import AHW28LiteralMeanFreePhysicalRV
import AHX7RegularRadialActionAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.ActualBoundaryPrimitives Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger

/-- The three actual physical rows, before any high projection. The third
provider includes the literal P in rV. -/
def lowPhysicalRowKernel (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact) (row : Fin 3) (radius : RadialPoint) :
    RadialKernel parameters radius 7 1 :=
  if row = 0 then radialNormalizedUnprojectedFirstRowKernel parameters length compact state radius
  else if row = 1 then radialNormalizedUnprojectedCKernel parameters length compact state radius
  else radialNormalizedPhysicalRVKernel parameters length compact state radius

def lowCircularRowKernel (parameters : PhaseParameters) (length : ℝ) (row : Fin 3) (radius : RadialPoint) :
    RadialKernel parameters radius 7 1 :=
  if row = 0 then circularNormalizedUnprojectedFirstRowKernel (radialKernelParameters parameters radius) length
  else if row = 1 then circularNormalizedUnprojectedCKernel (radialKernelParameters parameters radius) length
  else circularNormalizedPhysicalRVKernel (radialKernelParameters parameters radius) length

theorem lowPhysicalRowKernel_regular (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact) (row : Fin 3) :
    RegularKernelFamily (lowPhysicalRowKernel parameters length compact state row) := by
  fin_cases row
  · exact radialNormalizedUnprojectedFirstRowKernel_regular parameters length compact state
  · exact radialNormalizedUnprojectedCKernel_regular parameters length compact state
  · exact radialNormalizedPhysicalRVKernel_regular parameters length compact state

theorem lowCircularRowKernel_regular (parameters : PhaseParameters) (length : ℝ) (row : Fin 3) :
    RegularKernelFamily (lowCircularRowKernel parameters length row) := by
  fin_cases row
  · exact fixedRadialKernel_regular parameters _ (fun _ _ => sameCircularNormalizedUnprojectedFirstRowKernel _ _ length)
  · exact fixedRadialKernel_regular parameters _ (fun _ _ => sameCircularNormalizedUnprojectedCKernel _ _ length)
  · exact fixedRadialKernel_regular parameters _ (fun _ _ => sameCircularNormalizedPhysicalRVKernel _ _ length)

theorem lowPhysicalRowKernel_referenceDifference (parameters : PhaseParameters) (length compact : ℝ) (row : Fin 3) :
    RetainedReferenceDifference parameters length compact
      (fun state radius => lowPhysicalRowKernel parameters length compact state row radius)
      (fun _ radius => lowCircularRowKernel parameters length row radius) := by
  fin_cases row
  · exact radialNormalizedUnprojectedFirstRowKernel_referenceDifference parameters length compact
  · exact radialNormalizedUnprojectedCKernel_referenceDifference parameters length compact
  · exact radialNormalizedPhysicalRVKernel_referenceDifference parameters length compact

def lowPhysicalRowErrorConstant (parameters : PhaseParameters) (length compact : ℝ) (row : Fin 3) : ℝ :=
  Classical.choose (lowPhysicalRowKernel_referenceDifference parameters length compact row 0)

theorem lowPhysicalRowErrorConstant_nonnegative (parameters : PhaseParameters) (length compact : ℝ) (row : Fin 3) :
    0 ≤ lowPhysicalRowErrorConstant parameters length compact row :=
  (Classical.choose_spec (lowPhysicalRowKernel_referenceDifference parameters length compact row 0)).1

theorem lowPhysicalRowError_moment (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact) (row : Fin 3) (radius : RadialPoint) :
    fullKernelMoment (radialKernelParameters parameters radius) 0
      (fullKernelSub (lowPhysicalRowKernel parameters length compact state row radius) (lowCircularRowKernel parameters length row radius)) ≤
      lowPhysicalRowErrorConstant parameters length compact row * state.val.errorBudget 0 :=
  (Classical.choose_spec (lowPhysicalRowKernel_referenceDifference parameters length compact row 0)).2 state radius

end Grad.AnnularCurrentLow
