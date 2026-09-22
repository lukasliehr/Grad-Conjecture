import RKWD1Interface
import SD1Stage
import OJConsumer

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open Grad.RepresentedKernel.SpatialProduct
open scoped BigOperators ContDiff Topology

namespace Grad.RepresentedKernel.WeakDerivatives

theorem orderedDerivative_cast {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {first second : ℕ} (equality : first = second) (word : Word first)
    (function : Spatial → Value) :
    Grad.Mollifier.Pointwise.orderedDerivative first word function =
      Grad.Mollifier.Pointwise.orderedDerivative second
        (fun position => word (Fin.cast equality.symm position)) function := by
  subst second
  rfl

theorem inputDerivative_realized (dimension order rank weight : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (bound : rank ≤ order)
    (jet : Grad.WeightedJets.GraphGrade dimension order weight domain)
    (function : Spatial → CellValues dimension) (cells : Finset ℤ)
    (core : Grad.SmoothDensity.CoreLaws dimension function cells)
    (realized : Grad.SmoothDensity.Realizes dimension domain (.graph order weight) function jet)
    (selected : Finset (Fin rank)) (target : Word (selectedᶜ).card) :
    inputDerivative dimension order rank weight domain bound jet selected target
      =ᵐ[volume.restrict domain]
        Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function := by
  unfold inputDerivative
  rw [Grad.WeightedJets.Ordered.orderedDerivative_apply]
  let complementBound : (selectedᶜ).card ≤ order := by
    have complementLe : (selectedᶜ).card ≤ rank := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ selectedᶜ
    exact complementLe.trans bound
  let index := Grad.WeightedJets.Ordered.wordIndex complementBound target
  have recovery := Grad.SmoothDensity.realizes_recovery dimension domain (.graph order weight)
    function jet realized index
  have degreeEquality : Grad.WeightedJets.degree index = (selectedᶜ).card :=
    Grad.WeightedJets.Ordered.wordIndex_degree complementBound target
  have canonical := Grad.RepresentedKernel.SpatialProduct.wordDerivative_sameCounts openDomain
    (selectedᶜ).card target (Grad.WeightedJets.Ordered.jetCanonicalWord complementBound target)
    (Grad.WeightedJets.Ordered.word_sameCounts complementBound target) core.1.contDiffOn
  filter_upwards [recovery, ae_restrict_mem openDomain.measurableSet] with point recovered inside
  calc
    _ = Grad.Mollifier.Pointwise.orderedDerivative (Grad.WeightedJets.degree index)
        (Grad.WeightedJets.derivativeWord index) function point := recovered
    _ = Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function point := by
      calc
        _ = Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card
            (Grad.WeightedJets.Ordered.jetCanonicalWord complementBound target) function point := by
          exact congrFun (orderedDerivative_cast degreeEquality
            (Grad.WeightedJets.derivativeWord index) function) point
        _ = _ := (canonical inside).symm

theorem inputDerivative_finite_support (dimension order rank weight : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (bound : rank ≤ order)
    (jet : Grad.WeightedJets.GraphGrade dimension order weight domain)
    (function : Spatial → CellValues dimension) (cells : Finset ℤ)
    (core : Grad.SmoothDensity.CoreLaws dimension function cells)
    (realized : Grad.SmoothDensity.Realizes dimension domain (.graph order weight) function jet)
    (selected : Finset (Fin rank)) (target : Word (selectedᶜ).card) :
    ∀ input ∉ cells,
      fieldCellProjection dimension domain input
        (inputDerivative dimension order rank weight domain bound jet selected target) = 0 := by
  intro input outside
  apply Lp.ext
  filter_upwards [Grad.GenericCarriers.fieldCellProjection_ae dimension domain
      (inputDerivative dimension order rank weight domain bound jet selected target),
    inputDerivative_realized dimension order rank weight domain openDomain bound jet function cells
      core realized selected target,
    Lp.coeFn_zero (PhysicalValue dimension) 2 (volume.restrict domain)]
    with point coordinate realizedAt zeroAt
  have realizedCell := congrArg (fun value : CellValues dimension => value input) realizedAt
  exact (coordinate input).trans (realizedCell.trans
    ((Grad.SmoothDensity.derivative_zero_cell dimension function core.1 input
      (fun source => core.2.2 source input outside) (selectedᶜ).card target point).trans zeroAt.symm))

theorem base_finite_support (dimension order weight : ℕ) (domain : Set Spatial)
    (jet : Grad.WeightedJets.GraphGrade dimension order weight domain)
    (function : Spatial → CellValues dimension) (cells : Finset ℤ)
    (core : Grad.SmoothDensity.CoreLaws dimension function cells)
    (realized : Grad.SmoothDensity.Realizes dimension domain (.graph order weight) function jet) :
    ∀ input ∉ cells,
      fieldCellProjection dimension domain input
        (Grad.WeightedJets.base dimension order domain (fun _ => weight) jet) = 0 := by
  intro input outside
  apply Lp.ext
  filter_upwards [Grad.GenericCarriers.fieldCellProjection_ae dimension domain
      (Grad.WeightedJets.base dimension order domain (fun _ => weight) jet),
    realized.1, Lp.coeFn_zero (PhysicalValue dimension) 2 (volume.restrict domain)]
    with point coordinate realizedAt zeroAt
  have cellAt := congrArg (fun value : CellValues dimension => value input) realizedAt
  exact (coordinate input).trans (cellAt.trans
    ((core.2.2 point input outside).trans zeroAt.symm))

end Grad.RepresentedKernel.WeakDerivatives
