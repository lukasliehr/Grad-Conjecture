import AKAG3CompactWeakTemperedDerivative

noncomputable section

set_option maxHeartbeats 1600000

open MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap

namespace Grad.CartesianStartup

open Grad.PDEBootstrap Grad.WeakTesting Grad.WeakTesting.Commutation

/-- The converse test identity uses only the actual tempered derivative.
 No support assumption is needed to recover compact weak derivatives. -/
theorem startupTempered_compactWeak (field derivative : Grad.GenericCarriers.FieldL2 3 Set.univ)
    (direction : Fin 2)
    (equation : distributionDerivative direction (distributionEmbedding (startupWholePlaneField field)) =
      distributionEmbedding (startupWholePlaneField derivative)) :
    HasWeakOrderedDerivative 3 Set.univ 1 (startupFirstWord direction) field derivative := by
  apply (hasWeakOrderedDerivative_iff_integral 3 Set.univ 1 (startupFirstWord direction) field derivative).mpr
  intro cell vector test smooth compact _supported
  let schwartz : 𝓢(Spatial, ℝ) := compact.toSchwartzMap smooth
  have evaluated := congrArg (fun distribution : FieldDistribution =>
    distribution (startupRealSchwartz schwartz)) equation
  rw [startupRealSchwartz_distributionDerivative] at evaluated
  have paired := congrArg (fun value : CellValues => inner ℂ vector (value cell)) evaluated
  rw [lp.coeFn_neg, Pi.neg_apply, inner_neg_right, startupRealSchwartz_pairing, startupRealSchwartz_pairing,
    ← startupSchwartz_ordered_first] at paired
  have same : (schwartz : Spatial → ℝ) = test := rfl
  simpa only [same, pow_one, neg_one_mul] using paired.symm

end Grad.CartesianStartup
