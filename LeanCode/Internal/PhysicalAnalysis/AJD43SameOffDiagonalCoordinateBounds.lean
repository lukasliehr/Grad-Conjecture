import AJD35SameCompleteCrossResponseBounds
import AJD42CompleteCrossDataCoordinateBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.AnnularKernelOrbit Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularCrossMaps
open Grad.AnnularCoupledInverse Grad.AnnularLowOrbit Grad.GaugeCoefficients.Physical.Allocation

attribute [local instance] crossDataNormed crossDataSeminormed crossDataRealInner crossDataRealNormed crossDataRealModule
  crossHighNormed crossHighSeminormed crossHighComplexNormed crossHighComplexModule crossHighRealNormed crossHighRealModule
  crossResponseRealNormed crossResponseRealModule lowToHighOperatorRealNormed highToLowOperatorRealNormed
  highOffDiagonalRealNormed lowOffDiagonalRealNormed

local instance highOffDiagonalOperatorNormed (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    NormedAddCommGroup (lowEnergyGraph lower L positive →L[ℂ] CrossHighSpace lower L positive lengthPositive) := inferInstance
local instance lowOffDiagonalOperatorNormed (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    NormedAddCommGroup (CrossHighSpace lower L positive lengthPositive →L[ℂ] lowEnergyGraph lower L positive) := inferInstance

variable (parameters : PhaseParameters) (L compact : ℝ)

theorem actualHighOffDiagonalOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        actualHighOffDiagonalOrbit parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf
          context.widthHalf context.widthLength context.state context.small) := by
  have assembled := UniformCoordinateBound.composeComplex
    (budget := CoupledCoordinateContext.budget)
    (X := fun context : CoupledCoordinateContext parameters L compact => lowEnergyGraph context.lower L context.positive)
    (E := fun context : CoupledCoordinateContext parameters L compact => CrossHighData parameters context.lower)
    (F := fun context : CoupledCoordinateContext parameters L compact => CrossHighSpace context.lower L context.positive context.lengthPositive)
    (outer := fun context => actualHighCrossResponseOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (inner := fun context => lowToHighCrossOrbit parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf context.state)
    (by
      intro axis order
      let constant : ℝ := (actualHighCrossResponseOrbit_uniformCoordinateBound parameters L compact axis order).choose
      refine ⟨constant, (actualHighCrossResponseOrbit_uniformCoordinateBound parameters L compact axis order).choose_spec.1, ?_⟩
      intro context base time
      with_unfolding_all
        exact (actualHighCrossResponseOrbit_uniformCoordinateBound parameters L compact axis order).choose_spec.2 context base time)
    (by
      intro axis order
      let constant : ℝ := (lowToHighCrossOrbit_uniformCoordinateBound parameters L compact axis order).choose
      refine ⟨constant, (lowToHighCrossOrbit_uniformCoordinateBound parameters L compact axis order).choose_spec.1, ?_⟩
      intro context base time
      with_unfolding_all
        exact (lowToHighCrossOrbit_uniformCoordinateBound parameters L compact axis order).choose_spec.2 context base time)
    (fun context => actualHighCrossResponseOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (fun context => lowToHighCrossOrbit_contDiff parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf context.state)
    (fun context => context.budget_nonnegative) (fun order => pairBudgetConstant 8 order 1)
    (fun order => pairBudgetConstant_nonnegative 8 order (by norm_num)) (fun context => context.budget_pair)
  intro axis order
  obtain ⟨constant, nonnegative, estimate⟩ := assembled axis order
  refine ⟨constant, nonnegative, ?_⟩
  intro context base time
  with_unfolding_all exact estimate context base time

theorem actualLowOffDiagonalOrbit_uniformCoordinateBound (lengthPositive : 0 < L) :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        actualLowOffDiagonalOrbit parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf context.state) := by
  have assembled := UniformCoordinateBound.composeComplex
    (budget := CoupledCoordinateContext.budget)
    (X := fun context : CoupledCoordinateContext parameters L compact => CrossHighSpace context.lower L context.positive context.lengthPositive)
    (E := fun context : CoupledCoordinateContext parameters L compact => LowEnergyData context.lower)
    (F := fun context : CoupledCoordinateContext parameters L compact => lowEnergyGraph context.lower L context.positive)
    (outer := fun context => actualLowInverseOrbit parameters L compact context.lower context.lengthPositive context.positive
      (context.lowerHalf.trans_lt (by norm_num)) context.state)
    (inner := fun context => highToLowCrossOrbit parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf context.state)
    (by
      intro axis order
      let constant : ℝ := (actualLowInverseOrbit_uniformCoordinateBound parameters L compact lengthPositive axis order).choose
      refine ⟨constant, (actualLowInverseOrbit_uniformCoordinateBound parameters L compact lengthPositive axis order).choose_spec.1, ?_⟩
      intro context base time
      with_unfolding_all
        exact (actualLowInverseOrbit_uniformCoordinateBound parameters L compact lengthPositive axis order).choose_spec.2 context base time)
    (by
      intro axis order
      let constant : ℝ := (highToLowCrossOrbit_uniformCoordinateBound parameters L compact axis order).choose
      refine ⟨constant, (highToLowCrossOrbit_uniformCoordinateBound parameters L compact axis order).choose_spec.1, ?_⟩
      intro context base time
      with_unfolding_all
        exact (highToLowCrossOrbit_uniformCoordinateBound parameters L compact axis order).choose_spec.2 context base time)
    (fun context => actualLowInverseOrbit_contDiff parameters L compact context.lower context.lengthPositive context.positive
      (context.lowerHalf.trans_lt (by norm_num)) context.state (coupledPrimitive_lowSmall parameters L compact context.state context.small))
    (fun context => highToLowCrossOrbit_contDiff parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf context.state)
    (fun context => context.budget_nonnegative) (fun order => pairBudgetConstant 8 order 1)
    (fun order => pairBudgetConstant_nonnegative 8 order (by norm_num)) (fun context => context.budget_pair)
  intro axis order
  obtain ⟨constant, nonnegative, estimate⟩ := assembled axis order
  refine ⟨constant, nonnegative, ?_⟩
  intro context base time
  with_unfolding_all exact estimate context base time
end Grad.AnnularCrossOrbit
