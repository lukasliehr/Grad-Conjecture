import AHX6CompletedDiagonalAndHighSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift Grad.AnnularKernelContinuity

variable {src tgt : ℕ} (parameters : PhaseParameters) (power : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (r : RadialPoint) → RadialKernel parameters r src tgt)
    (regular : RegularKernelFamily kernel)

/-- A proved regular radial kernel already supplies every hypothesis of
AHT's actual completed action; this selects its existing moment witness. -/
def regularRadialBulkBound : ℝ := Classical.choose (regular.2 power)

include regular in
theorem regularRadialBulk_measurable (shift mode : ℤ × ℤ) :
    AEStronglyMeasurable (fun x => (kernel (collarRadius lower positive bounded x)).entry shift mode)
      (volume.restrict (Icc lower 1)) :=
  ((regular.1 shift mode).comp (collarRadius_continuous lower positive bounded)).aestronglyMeasurable

theorem regularRadialBulk_moment : ∀ᵐ x ∂volume.restrict (Icc lower 1),
    fullKernelMoment (radialKernelParameters parameters (collarRadius lower positive bounded x)) power
      (kernel (collarRadius lower positive bounded x)) ≤ regularRadialBulkBound parameters power kernel regular :=
  Eventually.of_forall (fun x => (Classical.choose_spec (regular.2 power)).2 (collarRadius lower positive bounded x))

def regularRadialBulkAction : DivisionRow src lower →L[ℂ] DivisionRow tgt lower :=
  completedBulkKernel parameters power lower (collarRadius lower positive bounded)
    (collarRadius_continuous lower positive bounded) (fun x => kernel (collarRadius lower positive bounded x))
    (regularRadialBulk_measurable parameters lower positive bounded kernel regular)
    (regularRadialBulkBound parameters power kernel regular)
    (regularRadialBulk_moment parameters power lower positive bounded kernel regular)

theorem regularRadialBulkAction_eq_completed
    (measurable : ∀ shift mode, AEStronglyMeasurable
      (fun x => (kernel (collarRadius lower positive bounded x)).entry shift mode) (volume.restrict (Icc lower 1)))
    (bound : ℝ) (moment : ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (collarRadius lower positive bounded x)) power
        (kernel (collarRadius lower positive bounded x)) ≤ bound) :
    regularRadialBulkAction parameters power lower positive bounded kernel regular =
      completedBulkKernel parameters power lower (collarRadius lower positive bounded)
        (collarRadius_continuous lower positive bounded) (fun x => kernel (collarRadius lower positive bounded x))
        measurable bound moment := by
  unfold regularRadialBulkAction
  apply completedBulkKernel_congr
  exact Eventually.of_forall (fun _ => rfl)

theorem regularRadialBulkAction_congr
    (second : (r : RadialPoint) → RadialKernel parameters r src tgt)
    (secondRegular : RegularKernelFamily second) (same : ∀ r, kernel r = second r) :
    regularRadialBulkAction parameters power lower positive bounded kernel regular =
      regularRadialBulkAction parameters power lower positive bounded second secondRegular := by
  unfold regularRadialBulkAction
  apply completedBulkKernel_congr
  exact Eventually.of_forall (fun x => same (collarRadius lower positive bounded x))

theorem regularRadialBulkAction_sub
    (second : (r : RadialPoint) → RadialKernel parameters r src tgt)
    (secondRegular : RegularKernelFamily second) :
    regularRadialBulkAction parameters power lower positive bounded
      (fun r => fullKernelSub (kernel r) (second r)) (regular.sub secondRegular) =
      regularRadialBulkAction parameters power lower positive bounded kernel regular -
        regularRadialBulkAction parameters power lower positive bounded second secondRegular := by
  unfold regularRadialBulkAction
  apply completedBulkKernel_sub

theorem regularRadialBulkAction_comp {mid : ℕ}
    (outer : (r : RadialPoint) → RadialKernel parameters r mid tgt)
    (inner : (r : RadialPoint) → RadialKernel parameters r src mid)
    (outerRegular : RegularKernelFamily outer) (innerRegular : RegularKernelFamily inner) :
    regularRadialBulkAction parameters power lower positive bounded
      (fun r => fullKernelComposition (outer r) (inner r)) (outerRegular.comp innerRegular) =
      (regularRadialBulkAction parameters power lower positive bounded outer outerRegular).comp
        (regularRadialBulkAction parameters power lower positive bounded inner innerRegular) := by
  unfold regularRadialBulkAction
  apply completedBulkKernel_comp

end Grad.AnnularKernelL2
