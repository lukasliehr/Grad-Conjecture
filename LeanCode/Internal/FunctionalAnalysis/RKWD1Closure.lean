import RKWD1Interface

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open Grad.RepresentedKernel.SpatialProduct
open scoped ContDiff Topology

namespace Grad.RepresentedKernel.WeakDerivatives

theorem closedWeak : ClosedWeakGoal := by
  intro dimension rank domain word fields derivatives field derivative fieldsLimit derivativesLimit weak
    cell vector test smooth compact supported
  let left := Grad.WeakTesting.compactPairing dimension domain cell vector test smooth compact
  let right := Grad.WeakTesting.Commutation.signedDerivativePairing
    dimension domain cell vector test smooth compact rank word
  have leftLimit : Filter.Tendsto (fun number => left (derivatives number)) Filter.atTop
      (𝓝 (left derivative)) :=
    left.continuous.continuousAt.tendsto.comp derivativesLimit
  have rightLimit : Filter.Tendsto (fun number => right (fields number)) Filter.atTop
      (𝓝 (right field)) :=
    right.continuous.continuousAt.tendsto.comp fieldsLimit
  have sequenceEquality : (fun number => left (derivatives number)) =
      (fun number => right (fields number)) := by
    funext number
    exact weak number cell vector test smooth compact supported
  rw [sequenceEquality] at leftLimit
  exact tendsto_nhds_unique leftLimit rightLimit

end Grad.RepresentedKernel.WeakDerivatives
