import AIQ7LiteralCompletedXCoordinate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularPhysicalSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularKernelContinuity
open Grad.SourceCollarCoefficients

/-- Addition of the SAME regular physical kernels on the original completed carrier. -/
theorem regularRadialBulkAction_add {input output : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (first second : (radius : RadialPoint) → RadialKernel parameters radius input output)
    (firstRegular : RegularKernelFamily first) (secondRegular : RegularKernelFamily second) :
    regularRadialBulkAction parameters power lower positive bounded
      (fun radius => fullKernelAdd (first radius) (second radius)) (firstRegular.add secondRegular) =
      regularRadialBulkAction parameters power lower positive bounded first firstRegular +
        regularRadialBulkAction parameters power lower positive bounded second secondRegular := by
  apply ContinuousLinearMap.ext
  intro field
  apply (radialCoordinateEquivalence output lower).symm.injective
  change collectRadial lower (regularRadialBulkAction parameters power lower positive bounded
    (fun radius => fullKernelAdd (first radius) (second radius)) (firstRegular.add secondRegular) field) =
    (radialCoordinateEquivalence output lower).symm
      (regularRadialBulkAction parameters power lower positive bounded first firstRegular field +
        regularRadialBulkAction parameters power lower positive bounded second secondRegular field)
  rw [map_add]
  apply Lp.ext
  let radius := collarRadius lower positive bounded
  have firstLaw := completedBulkKernel_collect_ae parameters power lower radius (collarRadius_continuous lower positive bounded)
    (fun x => first (radius x)) (regularRadialBulk_measurable parameters lower positive bounded first firstRegular)
    (regularRadialBulkBound parameters power first firstRegular) (regularRadialBulk_moment parameters power lower positive bounded first firstRegular) field
  have secondLaw := completedBulkKernel_collect_ae parameters power lower radius (collarRadius_continuous lower positive bounded)
    (fun x => second (radius x)) (regularRadialBulk_measurable parameters lower positive bounded second secondRegular)
    (regularRadialBulkBound parameters power second secondRegular) (regularRadialBulk_moment parameters power lower positive bounded second secondRegular) field
  have sumLaw := completedBulkKernel_collect_ae parameters power lower radius (collarRadius_continuous lower positive bounded)
    (fun x => fullKernelAdd (first (radius x)) (second (radius x)))
    (regularRadialBulk_measurable parameters lower positive bounded _ (firstRegular.add secondRegular))
    (regularRadialBulkBound parameters power _ (firstRegular.add secondRegular))
    (regularRadialBulk_moment parameters power lower positive bounded _ (firstRegular.add secondRegular)) field
  filter_upwards [firstLaw, secondLaw, sumLaw,
    Lp.coeFn_add
      (collectRadial lower (regularRadialBulkAction parameters power lower positive bounded first firstRegular field))
      (collectRadial lower (regularRadialBulkAction parameters power lower positive bounded second secondRegular field))]
    with x firstValue secondValue sumValue addition
  change collectRadial lower (regularRadialBulkAction parameters power lower positive bounded
      (fun radius => fullKernelAdd (first radius) (second radius)) (firstRegular.add secondRegular) field) x =
    (collectRadial lower (regularRadialBulkAction parameters power lower positive bounded first firstRegular field) +
      collectRadial lower (regularRadialBulkAction parameters power lower positive bounded second secondRegular field)) x
  change collectRadial lower (regularRadialBulkAction parameters power lower positive bounded first firstRegular field) x = _ at firstValue
  change collectRadial lower (regularRadialBulkAction parameters power lower positive bounded second secondRegular field) x = _ at secondValue
  change collectRadial lower (regularRadialBulkAction parameters power lower positive bounded
    (fun radius => fullKernelAdd (first radius) (second radius)) (firstRegular.add secondRegular) field) x = _ at sumValue
  rw [addition, Pi.add_apply, sumValue, firstValue, secondValue, bulkKernelAction_add, add_apply]

end Grad.AnnularPhysicalSolution
