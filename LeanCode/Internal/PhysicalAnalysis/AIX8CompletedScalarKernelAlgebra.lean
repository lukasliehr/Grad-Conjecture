import AIX7KernelOrbitalTaylorRemainder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKernelOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularKernelContinuity

variable {src tgt : ℕ} (parameters : PhaseParameters)
    (kernel : (r : RadialPoint) → RadialKernel parameters r src tgt) (regular : RegularKernelFamily kernel)

include regular in
theorem constantSmulKernel_regular (scalar : ℂ) :
    RegularKernelFamily (fun r => fullKernelSmul scalar (kernel r)) :=
  Grad.AnnularReconstruction.RegularKernelFamily.radial_smul regular (fun _ => scalar) continuous_const ‖scalar‖ (norm_nonneg _) (fun _ => le_rfl)

/-- Scalar multiplication passes to the SAME original completed action. -/
theorem regularAction_smul (power : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (scalar : ℂ) :
    regularRadialBulkAction parameters power lower positive bounded
      (fun r => fullKernelSmul scalar (kernel r)) (constantSmulKernel_regular parameters kernel regular scalar) =
    scalar • regularRadialBulkAction parameters power lower positive bounded kernel regular := by
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext mode
  apply Lp.ext
  let output := regularRadialBulkAction parameters power lower positive bounded kernel regular field
  have original := completedBulkKernel_ae parameters power lower
    (collarRadius lower positive bounded) (collarRadius_continuous lower positive bounded)
    (fun x => kernel (collarRadius lower positive bounded x))
    (regularRadialBulk_measurable parameters lower positive bounded kernel regular)
    (regularRadialBulkBound parameters power kernel regular)
    (regularRadialBulk_moment parameters power lower positive bounded kernel regular) field
  have translated := completedBulkKernel_ae parameters power lower
    (collarRadius lower positive bounded) (collarRadius_continuous lower positive bounded)
    (fun x => fullKernelSmul scalar (kernel (collarRadius lower positive bounded x)))
    (regularRadialBulk_measurable parameters lower positive bounded (fun r => fullKernelSmul scalar (kernel r))
      (constantSmulKernel_regular parameters kernel regular scalar))
    (regularRadialBulkBound parameters power (fun r => fullKernelSmul scalar (kernel r))
      (constantSmulKernel_regular parameters kernel regular scalar))
    (regularRadialBulk_moment parameters power lower positive bounded (fun r => fullKernelSmul scalar (kernel r))
      (constantSmulKernel_regular parameters kernel regular scalar)) field
  filter_upwards [original, translated, Lp.coeFn_smul scalar (output mode)] with radius base orbit outputLaw
  change _ = (scalar • output mode) radius
  rw [outputLaw, Pi.smul_apply]
  apply (orbit mode).unique
  convert (base mode).const_smul scalar using 1
  · funext shift
    exact smul_comm (bulkWeightRatio parameters power (collarRadius lower positive bounded radius).val shift mode : ℂ)
      scalar ((kernel (collarRadius lower positive bounded radius)).entry shift
        (twoFrequencyTranslation shift mode) (field (twoFrequencyTranslation shift mode) radius))
  · rfl

end Grad.AnnularKernelOrbit
