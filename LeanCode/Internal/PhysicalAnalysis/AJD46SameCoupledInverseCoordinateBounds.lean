import AJD44SameCoupledResidualCoordinateBounds
import AJD45UniformSameInverseCoordinateBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.AnnularKernelOrbit Grad.AnnularCoupledInverse Grad.AnnularCoupledOrbit
open Grad.GaugeCoefficients.Physical.Allocation

attribute [local instance] coupledNormed coupledSeminormed coupledComplexNormed coupledComplexModule
  coupledRealNormed coupledRealModule coupledOperatorRealNormed coupledOperatorRealModule
  coupledCoordinateOperatorNormed

local instance coupledCoordinateComplete (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    CompleteSpace (CoupledSpace lower L positive lengthPositive) := inferInstance

variable (parameters : PhaseParameters) (L compact : ℝ) (lengthPositive : 0 < L)
include lengthPositive

/-- Genuine pure angular and cell derivatives of the SAME accepted AIZ
inverse have one high B_(8+n) factor on its unchanged original B8 ball.
The constants precede the lower radius, state, and all translations. -/
theorem coupledOrbitInverse_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        coupledOrbitInverse parameters context.lower L compact context.lengthPositive context.positive context.lowerHalf
          context.widthHalf context.widthLength context.state context.small) := by
  have inverseBound := UniformCoordinateBound.sameInverse (𝕜 := ℂ)
    (E := fun context : CoupledCoordinateContext parameters L compact => CoupledSpace context.lower L context.positive context.lengthPositive)
    (F := fun context : CoupledCoordinateContext parameters L compact => CoupledSpace context.lower L context.positive context.lengthPositive)
    (fun context => coupledResidualOrbit parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf
      context.widthHalf context.widthLength context.state context.small)
    (fun context => coupledOrbitInverse parameters context.lower L compact context.lengthPositive context.positive context.lowerHalf
      context.widthHalf context.widthLength context.state context.small)
    (by
      intro axis order
      let constant : ℝ := (coupledResidualOrbit_uniformCoordinateBound parameters L compact lengthPositive axis order).choose
      refine ⟨constant, (coupledResidualOrbit_uniformCoordinateBound parameters L compact lengthPositive axis order).choose_spec.1, ?_⟩
      intro context base time
      with_unfolding_all
        exact (coupledResidualOrbit_uniformCoordinateBound parameters L compact lengthPositive axis order).choose_spec.2 context base time)
    (fun context => coupledResidualOrbit_contDiff parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf
      context.widthHalf context.widthLength context.state context.small)
    (fun context => coupledResidualOrbit_inverse_right parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf
      context.widthHalf context.widthLength context.state context.small)
    (fun context => coupledResidualOrbit_inverse_left parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf
      context.widthHalf context.widthLength context.state context.small)
    2 (by norm_num)
    (fun context => coupledOrbitInverse_bound parameters context.lower L compact context.lengthPositive context.positive context.lowerHalf
      context.widthHalf context.widthLength context.state context.small)
    (fun context => context.budget_nonnegative) (fun context => context.budget_monotone)
    (fun order => pairBudgetConstant 8 order 1)
    (fun order => pairBudgetConstant_nonnegative 8 order (by norm_num)) (fun context => context.budget_pair)
  intro axis order
  obtain ⟨constant, nonnegative, estimate⟩ := inverseBound axis order
  refine ⟨constant, nonnegative, ?_⟩
  intro context base time
  with_unfolding_all exact estimate context base time
end Grad.AnnularCrossOrbit
