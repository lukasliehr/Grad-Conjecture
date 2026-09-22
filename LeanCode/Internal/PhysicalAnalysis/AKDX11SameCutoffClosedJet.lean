import AKDX10FixedCutoffMassEnergy
import AKDR9ActualRetainedScalarRecoveryNorm
import AKDP62OriginalCutoffMixedNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace Grad.OriginalCollarNorm
open Grad.Constraints Grad.ClosedJets Grad.CartesianState Grad.CartesianStartup
open Grad.OriginalCoreRealization Grad.ActualOriginalSourceMoments

/-- Equality of actual cutoff fields identifies every weighted closed jet,
including all boundary derivatives, with the literal smooth cutoff product. -/
theorem sameOriginalCutoff_closedJet (parameters : PhaseParameters)
    (cutoff : SpatialPlane→ℝ) (smooth : ContDiff ℝ ∞ cutoff) (compact : HasCompactSupport cutoff)
    (core image : ACore parameters 3)
    (same : (originalSourceMoments parameters image).field=
      startupCutoffL2 cutoff smooth compact (originalSourceMoments parameters core).field)
    (cell : ℤ) :
    phaseWeightedJet parameters cell (image.val cell)=
      globalClosedJet (fun point => cutoff point • smoothClosedExtension
        (phaseWeightedJet parameters cell (core.val cell)) point)
        (smooth.smul (smoothClosedExtension_smooth _)) := by
  apply closedJet_eq_of_value_eq
  apply Grad.GaugeCoefficients.Physical.Compensated.closedValueL2_injective 3
  change closedContinuousToDiskL2 _ = closedContinuousToDiskL2 _
  apply Lp.ext
  filter_upwards [originalSource_field_closed parameters image,originalSource_field_closed parameters core,
    startupCutoffL2_ae cutoff smooth compact (originalSourceMoments parameters core).field,
    closedContinuousToDiskL2_ae (phaseWeightedJet parameters cell (image.val cell)).value,
    closedContinuousToDiskL2_ae (globalClosedJet (fun point => cutoff point • smoothClosedExtension
      (phaseWeightedJet parameters cell (core.val cell)) point)
      (smooth.smul (smoothClosedExtension_smooth _))).value,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point imageAt coreAt cutAt left right inside
  rw [left,right]
  have closed : point∈closedUnitDisk := openDiskMembershipClosed point inside
  have equality := congrArg (fun field => field point cell) same
  rw [imageAt cell,cutAt cell,coreAt cell] at equality
  simp only [closedDiskLift,dif_pos closed] at equality ⊢
  change (phaseWeightedJet parameters cell (image.val cell)).value ⟨point,closed⟩ =
    cutoff point • smoothClosedExtension (phaseWeightedJet parameters cell (core.val cell)) point
  rw [smoothClosedExtension_value _ ⟨point,closed⟩]
  exact equality

end Grad.OriginalCollarNorm
