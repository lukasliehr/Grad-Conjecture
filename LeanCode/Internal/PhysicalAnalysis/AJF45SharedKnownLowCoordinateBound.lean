import AJF34FullKnownLowCoordinateBounds
import AJF28SameSharedKnownLowResponse
import AJD29SameDiagonalCoordinateBounds
import AJE25SharedLowForcingTower

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.CartesianState Grad.AnnularKernelOrbit Grad.AnnularCrossOrbit Grad.AnnularStrongOrbit
open Grad.AnnularLowEnergy Grad.AnnularLowOrbit Grad.AnnularStrongData Grad.AnnularKnownLow
open Grad.AnnularReconstruction Grad.AnnularOrbitGenerators Grad.AnnularVariational Grad.AnnularCoupledInverse

section GenericComplexReal
variable {Context : Type*} {X E F : Context → Type*}
  [∀ context, NormedAddCommGroup (X context)] [∀ context, NormedSpace ℝ (X context)]
  [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace ℂ (E context)]
  [∀ context, NormedAddCommGroup (F context)] [∀ context, NormedSpace ℂ (F context)]

theorem uniformCoordinateBound_complexRealComposition
    (budget : Context → ℕ → ℝ)
    (outer : (context : Context) → OrbitParameter → E context →L[ℂ] F context)
    (inner : (context : Context) → OrbitParameter → X context →L[ℝ] E context)
    (outerBound : UniformCoordinateBound budget outer) (innerBound : UniformCoordinateBound budget inner)
    (outerSmooth : ∀ context, ContDiff ℝ ∞ (outer context))
    (innerSmooth : ∀ context, ContDiff ℝ ∞ (inner context))
    (nonnegative : ∀ context order, 0 ≤ budget context order)
    (pair : ℕ → ℝ) (pairNonnegative : ∀ order, 0 ≤ pair order)
    (paired : ∀ context a b, budget context a * budget context b ≤ pair (a+b) * budget context (a+b)) :
    UniformCoordinateBound budget (fun context tau => ((outer context tau).restrictScalars ℝ).comp (inner context tau)) :=
  (uniformCoordinateBound_restrictScalars outerBound outerSmooth).composeReal innerBound
    (fun context => operator_restrictScalars_contDiff (outer context) (outerSmooth context))
    innerSmooth nonnegative pair pairNonnegative paired

end GenericComplexReal

attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule

local instance lowResponseOperatorNormed (parameters : PhaseParameters) (L compact : ℝ)
    (context : CoupledCoordinateContext parameters L compact) :
    NormedAddCommGroup (StrongDataCarrier parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) 0 0 →L[ℝ] lowEnergyGraph context.lower L context.positive) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance lowResponseOperatorSeminormed (parameters : PhaseParameters) (L compact : ℝ)
    (context : CoupledCoordinateContext parameters L compact) :
    SeminormedAddCommGroup (StrongDataCarrier parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) 0 0 →L[ℝ] lowEnergyGraph context.lower L context.positive) :=
  (lowResponseOperatorNormed parameters L compact context).toSeminormedAddCommGroup
local instance lowResponseOperatorReal (parameters : PhaseParameters) (L compact : ℝ)
    (context : CoupledCoordinateContext parameters L compact) :
    NormedSpace ℝ (StrongDataCarrier parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) 0 0 →L[ℝ] lowEnergyGraph context.lower L context.positive) :=
  ContinuousLinearMap.toNormedSpace
local instance lowResponseOperatorModule (parameters : PhaseParameters) (L compact : ℝ)
    (context : CoupledCoordinateContext parameters L compact) :
    Module ℝ (StrongDataCarrier parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) 0 0 →L[ℝ] lowEnergyGraph context.lower L context.positive) :=
  (lowResponseOperatorReal parameters L compact context).toModule

theorem actualLowInverseReal_uniformCoordinateBound (parameters : PhaseParameters) (L compact : ℝ) (lengthPositive : 0 < L) :
    UniformCoordinateBound (augmentedBudget CoupledCoordinateContext.budget)
      (fun (context : CoupledCoordinateContext parameters L compact) tau =>
        (actualLowInverseOrbit parameters L compact context.lower context.lengthPositive context.positive (context.lowerHalf.trans_lt (by norm_num)) context.state tau).restrictScalars ℝ) := by
  have inverse := uniformCoordinateBound_augment CoupledCoordinateContext.budget
    (fun context : CoupledCoordinateContext parameters L compact => actualLowInverseOrbit parameters L compact context.lower context.lengthPositive context.positive (context.lowerHalf.trans_lt (by norm_num)) context.state)
    (actualLowInverseOrbit_uniformCoordinateBound parameters L compact lengthPositive)
  exact uniformCoordinateBound_restrictScalars
    (E := fun context : CoupledCoordinateContext parameters L compact => LowEnergyData context.lower)
    (F := fun context : CoupledCoordinateContext parameters L compact => lowEnergyGraph context.lower L context.positive)
    inverse (fun context => actualLowInverseOrbit_contDiff parameters L compact context.lower context.lengthPositive context.positive (context.lowerHalf.trans_lt (by norm_num)) context.state (coupledPrimitive_lowSmall parameters L compact context.state context.small))

theorem sharedKnownLowResponseOrbit_uniformCoordinateBound (parameters : PhaseParameters) (L compact : ℝ) (lengthPositive : 0 < L) :
    UniformCoordinateBound (augmentedBudget CoupledCoordinateContext.budget)
      (fun context : CoupledCoordinateContext parameters L compact =>
        sharedKnownLowResponseOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.state) := by
  have result := uniformCoordinateBound_complexRealComposition
    (X := fun context : CoupledCoordinateContext parameters L compact => StrongDataCarrier parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) 0 0)
    (E := fun context : CoupledCoordinateContext parameters L compact => LowEnergyData context.lower)
    (F := fun context : CoupledCoordinateContext parameters L compact => lowEnergyGraph context.lower L context.positive)
    (augmentedBudget CoupledCoordinateContext.budget)
    (fun context => actualLowInverseOrbit parameters L compact context.lower context.lengthPositive context.positive (context.lowerHalf.trans_lt (by norm_num)) context.state)
    (fun context => sharedLowDataOrbitJet parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.state 0 0)
    (uniformCoordinateBound_augment CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact => actualLowInverseOrbit parameters L compact context.lower context.lengthPositive context.positive (context.lowerHalf.trans_lt (by norm_num)) context.state)
      (actualLowInverseOrbit_uniformCoordinateBound parameters L compact lengthPositive))
    (sharedLowDataOrbit_uniformCoordinateBound parameters L compact)
    (fun context => actualLowInverseOrbit_contDiff parameters L compact context.lower context.lengthPositive context.positive (context.lowerHalf.trans_lt (by norm_num)) context.state (coupledPrimitive_lowSmall parameters L compact context.state context.small))
    (fun context => sharedLowDataOrbitJet_contDiff parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.state 0 0)
    (coupledAugmentedBudget_nonnegative parameters L compact)
    (fun order => 2 + Grad.GaugeCoefficients.Physical.Allocation.pairBudgetConstant 8 order 1)
    (fun order => add_nonneg (by norm_num) (Grad.GaugeCoefficients.Physical.Allocation.pairBudgetConstant_nonnegative 8 order (by norm_num)))
    (coupledAugmentedBudget_pair parameters L compact)

  intro axis order
  let constant := (result axis order).choose
  refine ⟨constant, (result axis order).choose_spec.1, ?_⟩
  intro context base time
  have estimate := (result axis order).choose_spec.2 context base time
  with_unfolding_all exact estimate

end Grad.AnnularHighGenerators
