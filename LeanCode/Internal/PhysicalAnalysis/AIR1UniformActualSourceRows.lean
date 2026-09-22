import AEI29OriginalPhysicalCurrentInverseConsumer
import AEK16ExactBaseBF13Consumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKnownLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.BoundaryKernelAction

/-- The three actual pre-Q rows have uniform absolute moments on the SAME physical state. -/
theorem knownLowRow_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) (row : Fin 3) :
    RetainedPhysicalMoments parameters L compact (fun state radius => lowPhysicalRowKernel parameters L compact state row radius) := by
  fin_cases row
  · exact radialNormalizedUnprojectedFirstRowKernel_physicalMoments parameters L compact
  · exact radialNormalizedUnprojectedCKernel_physicalMoments parameters L compact
  · exact radialNormalizedPhysicalRVKernel_physicalMoments parameters L compact

def knownLowRowConstant (parameters : PhaseParameters) (L compact : ℝ) (row : Fin 3) : ℝ :=
  Classical.choose (knownLowRow_physicalMoments parameters L compact row 0)

theorem knownLowRowConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) (row : Fin 3) :
    0 ≤ knownLowRowConstant parameters L compact row :=
  (Classical.choose_spec (knownLowRow_physicalMoments parameters L compact row 0)).1

/-- Uniform actual completed row bound; radius and collar do not enter the constant. -/
theorem knownLowRow_bound (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters L compact)
    (row : Fin 3) (field : DivisionRow 7 lower) :
    ‖lowPhysicalRowAction parameters L compact lower positive bounded state row field‖ ≤
      knownLowRowConstant parameters L compact row * state.val.val.size 0 * ‖field‖ := by
  let kernel := lowPhysicalRowKernel parameters L compact state row
  let regular := lowPhysicalRowKernel_regular parameters L compact state row
  have moment : ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (collarRadius lower positive bounded radius)) 0
        (kernel (collarRadius lower positive bounded radius)) ≤
      knownLowRowConstant parameters L compact row * state.val.val.size 0 :=
    Filter.Eventually.of_forall (fun radius =>
      (Classical.choose_spec (knownLowRow_physicalMoments parameters L compact row 0)).2 state
        (collarRadius lower positive bounded radius))
  have represented := regularRadialBulkAction_eq_completed parameters 0 lower positive bounded kernel regular
    (regularRadialBulk_measurable parameters lower positive bounded kernel regular)
    (knownLowRowConstant parameters L compact row * state.val.val.size 0) moment
  change ‖regularRadialBulkAction parameters 0 lower positive bounded kernel regular field‖ ≤ _
  rw [represented]
  exact completedBulkKernel_bound _ _ _ _ _ _ _ _ _ field

end Grad.AnnularKnownLow
