import AJD27OriginalCoupledBudgetContexts
import AJD30UniformOperatorOperations
import AJA22SharpHighInverseOneHigh
import AJB21OriginalLowOrderedOneHigh

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2000
set_option synthInstance.maxHeartbeats 200000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.AnnularKernelOrbit Grad.AnnularInverseCalculus Grad.AnnularOrbitGenerators
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularHighInverseOrbit Grad.AnnularLowOrbit
open Grad.AnnularVariational
open Grad.AnnularCoupledInverse Grad.AnnularLowVolterra Grad.AnnularCurrentLow Grad.AnnularLowEnergy

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

local instance highInverseFamilyRealNormed (parameters : PhaseParameters) (L compact : ℝ)
    (context : CoupledCoordinateContext parameters L compact) :
    NormedSpace ℝ ((annularInnerZero context.lower L context.positive
      (context.lowerHalf.trans_lt (by norm_num)) context.lengthPositive →L[ℝ] ℝ) →L[ℝ]
      annularInnerZero context.lower L context.positive (context.lowerHalf.trans_lt (by norm_num)) context.lengthPositive) :=
  ContinuousLinearMap.toNormedSpace

local instance lowInverseOperatorNormed (lower L : ℝ) (positive : 0 < lower) :
    NormedAddCommGroup (LowEnergyData lower →L[ℂ] lowEnergyGraph lower L positive) := inferInstance

local instance lowInverseFamilyRealNormed (parameters : PhaseParameters) (L compact : ℝ)
    (context : CoupledCoordinateContext parameters L compact) :
    NormedSpace ℝ (LowEnergyData context.lower →L[ℂ] lowEnergyGraph context.lower L context.positive) :=
  ContinuousLinearMap.toNormedSpace

variable (parameters : PhaseParameters) (L compact : ℝ)

/-- Pure-coordinate specialization of the accepted sharp SAME high inverse
bound, with one uniform constant before the original context and translation. -/
theorem currentHighInverseOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        currentHighInverseOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
          context.widthHalf context.widthLength context.state
          (coupledPrimitive_highSmall parameters L compact context.state context.small)) := by
  apply UniformCoordinateBound.of_ordered
  · intro context
    exact currentHighInverseOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state
      (coupledPrimitive_highSmall parameters L compact context.state context.small)
  intro axis order
  by_cases zero : order = 0
  · subst order
    refine ⟨32, by norm_num, ?_⟩
    intro context point
    simp only [List.replicate_zero, orderedOrbitDerivative, coordinateJetWeight, ↓reduceIte, mul_one]
    exact currentHighInverseOrbit_norm parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state
      (coupledPrimitive_highSmall parameters L compact context.state context.small) _
  · have nonempty : List.replicate order axis ≠ [] := by simpa using zero
    let constant : ℝ := (currentHighInverseOrbit_positive_ordered_oneHigh parameters L compact (List.replicate order axis) nonempty).choose
    have nonnegative : 0 ≤ constant := (currentHighInverseOrbit_positive_ordered_oneHigh parameters L compact (List.replicate order axis) nonempty).choose_spec.1
    refine ⟨constant, nonnegative, ?_⟩
    intro context point
    simpa only [constant, List.length_replicate, CoupledCoordinateContext.budget, coordinateJetWeight, if_neg zero] using (currentHighInverseOrbit_positive_ordered_oneHigh parameters L compact (List.replicate order axis) nonempty).choose_spec.2 context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state
      (coupledPrimitive_highSmall parameters L compact context.state context.small) point

/-- Pure-coordinate specialization of the accepted SAME original low graph
inverse, with its original state-independent norm at order zero. -/
theorem actualLowInverseOrbit_uniformCoordinateBound (lengthPositive : 0 < L) :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        actualLowInverseOrbit parameters L compact context.lower context.lengthPositive context.positive
          (context.lowerHalf.trans_lt (by norm_num)) context.state) := by
  apply UniformCoordinateBound.of_ordered
  · intro context
    exact actualLowInverseOrbit_contDiff parameters L compact context.lower context.lengthPositive context.positive
      (context.lowerHalf.trans_lt (by norm_num)) context.state
      (coupledPrimitive_lowSmall parameters L compact context.state context.small)
  intro axis order
  by_cases zero : order = 0
  · subst order
    refine ⟨2 * Real.sqrt (lowReferenceGraphConstant parameters L), by positivity, ?_⟩
    intro context point
    simp only [List.replicate_zero, orderedOrbitDerivative, coordinateJetWeight, ↓reduceIte, mul_one]
    exact actualLowInverseOrbit_bound parameters L compact context.lower context.lengthPositive context.positive
      (context.lowerHalf.trans_lt (by norm_num)) context.state
      (coupledPrimitive_lowSmall parameters L compact context.state context.small) _
  · have nonempty : List.replicate order axis ≠ [] := by simpa using zero
    let constant : ℝ := (actualLowInverseOrbit_ordered_oneHigh parameters L compact lengthPositive (List.replicate order axis) nonempty).choose
    have nonnegative : 0 ≤ constant := (actualLowInverseOrbit_ordered_oneHigh parameters L compact lengthPositive (List.replicate order axis) nonempty).choose_spec.1
    refine ⟨constant, nonnegative, ?_⟩
    intro context point
    simpa only [constant, List.length_replicate, CoupledCoordinateContext.budget, coordinateJetWeight, if_neg zero] using (actualLowInverseOrbit_ordered_oneHigh parameters L compact lengthPositive (List.replicate order axis) nonempty).choose_spec.2 context.state
      (coupledPrimitive_lowSmall parameters L compact context.state context.small) context.lower context.positive
      (context.lowerHalf.trans_lt (by norm_num)) point

end Grad.AnnularCrossOrbit
