import AJD29SameDiagonalCoordinateBounds
import AJD32ActualKnownFunctionalCoordinateBounds
import AJD33UniformOperatorComposition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2000
set_option synthInstance.maxHeartbeats 200000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentBoundary Grad.AnnularReconstruction Grad.AnnularKernelL2 Grad.AnnularHighInverseOrbit
open Grad.AnnularCurrentInverse Grad.AnnularCoupledInverse Grad.GaugeCoefficients.Physical.Allocation

attribute [local instance] crossDataNormed crossDataSeminormed crossDataRealInner crossDataRealNormed crossDataRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace highInverseFamilyRealNormed

local instance crossZeroOperatorNormed (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (upper : lower < 1) (lengthPositive : 0 < L) :
    NormedAddCommGroup (CrossHighData parameters lower →L[ℂ] annularInnerZero lower L positive upper lengthPositive) := inferInstance
local instance crossEnergyOperatorNormed (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower) :
    NormedAddCommGroup (CrossHighData parameters lower →L[ℂ] annularEnergySpace lower L positive) := inferInstance
local instance crossZeroOperatorRealNormed (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (upper : lower < 1) (lengthPositive : 0 < L) :
    NormedSpace ℝ (CrossHighData parameters lower →L[ℂ] annularInnerZero lower L positive upper lengthPositive) :=
  NormedSpace.restrictScalars ℝ ℂ (CrossHighData parameters lower →L[ℂ] annularInnerZero lower L positive upper lengthPositive)
local instance crossEnergyOperatorRealNormed (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower) :
    NormedSpace ℝ (CrossHighData parameters lower →L[ℂ] annularEnergySpace lower L positive) :=
  NormedSpace.restrictScalars ℝ ℂ (CrossHighData parameters lower →L[ℂ] annularEnergySpace lower L positive)

section OperatorRetraction
variable {Context : Type*} {X E F : Context → Type*}
  [∀ context, NormedAddCommGroup (X context)] [∀ context, NormedSpace ℂ (X context)]
  [∀ context, NormedSpace ℝ (X context)] [∀ context, IsScalarTower ℝ ℂ (X context)]
  [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace ℂ (E context)]
  [∀ context, NormedSpace ℝ (E context)] [∀ context, IsScalarTower ℝ ℂ (E context)]
  [∀ context, NormedAddCommGroup (F context)] [∀ context, NormedSpace ℂ (F context)]
  {budget : Context → ℕ → ℝ}

private theorem uniformComplexPart
    (family : (context : Context) → OrbitParameter → X context →L[ℝ] E context)
    (bound : UniformCoordinateBound budget family) (smooth : ∀ context, ContDiff ℝ ∞ (family context)) :
    UniformCoordinateBound budget (fun context tau => complexPartCLM (family context tau)) := by
  apply bound.map_bound (F := fun context => X context →L[ℂ] E context) smooth
    (fun context => complexPartCLM (E := X context) (F := E context)) 1 (by norm_num)
  intro context mapping
  exact (ContinuousLinearMap.opNorm_le_bound (complexPart mapping) (norm_nonneg mapping)
    (complexPart_apply_bound mapping)).trans_eq (one_mul _).symm

end OperatorRetraction



variable (parameters : PhaseParameters) (L compact : ℝ)

/-- The SAME actual zero-inner cross-energy response has genuine one-high
coordinate bounds, obtained from the SAME high inverse and actual known dual. -/
theorem crossZeroEnergyOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        crossZeroEnergyOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
          context.widthHalf context.widthLength context.state
          (coupledPrimitive_highSmall parameters L compact context.state context.small)) := by
  let inverse := fun context : CoupledCoordinateContext parameters L compact =>
    currentHighInverseOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state
      (coupledPrimitive_highSmall parameters L compact context.state context.small)
  let known := fun context : CoupledCoordinateContext parameters L compact =>
    crossKnownZeroFunctionalOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state
  have inverseSmooth (context : CoupledCoordinateContext parameters L compact) : ContDiff ℝ ∞ (inverse context) :=
    currentHighInverseOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state
      (coupledPrimitive_highSmall parameters L compact context.state context.small)
  have knownSmooth (context : CoupledCoordinateContext parameters L compact) : ContDiff ℝ ∞ (known context) :=
    crossKnownZeroFunctionalOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state
  have realBound := (currentHighInverseOrbit_uniformCoordinateBound parameters L compact).composeReal
    (X := fun context : CoupledCoordinateContext parameters L compact => CrossHighData parameters context.lower)
    (E := fun context : CoupledCoordinateContext parameters L compact => annularInnerZero context.lower L context.positive
      (context.lowerHalf.trans_lt (by norm_num)) context.lengthPositive →L[ℝ] ℝ)
    (F := fun context : CoupledCoordinateContext parameters L compact => annularInnerZero context.lower L context.positive
      (context.lowerHalf.trans_lt (by norm_num)) context.lengthPositive)
    (crossKnownZeroFunctionalOrbit_uniformCoordinateBound parameters L compact) inverseSmooth knownSmooth
    (fun context => context.budget_nonnegative) (fun order => pairBudgetConstant 8 order 1)
    (fun order => pairBudgetConstant_nonnegative 8 order (by norm_num)) (fun context => context.budget_pair)
  have realSmooth (context : CoupledCoordinateContext parameters L compact) :
      ContDiff ℝ ∞ (fun tau => (inverse context tau).comp (known context tau)) :=
    (ContinuousLinearMap.compL ℝ (CrossHighData parameters context.lower)
      (annularInnerZero context.lower L context.positive (context.lowerHalf.trans_lt (by norm_num)) context.lengthPositive →L[ℝ] ℝ)
      (annularInnerZero context.lower L context.positive (context.lowerHalf.trans_lt (by norm_num)) context.lengthPositive)).isBoundedBilinearMap.contDiff.comp₂
        (inverseSmooth context) (knownSmooth context)
  have complexBound := uniformComplexPart
    (X := fun context : CoupledCoordinateContext parameters L compact => CrossHighData parameters context.lower)
    (E := fun context : CoupledCoordinateContext parameters L compact => annularInnerZero context.lower L context.positive
      (context.lowerHalf.trans_lt (by norm_num)) context.lengthPositive)
    (fun context tau => (inverse context tau).comp (known context tau)) realBound realSmooth
  have same (context : CoupledCoordinateContext parameters L compact) (tau : OrbitParameter) :
      complexPartCLM ((inverse context tau).comp (known context tau)) =
        crossZeroEnergyOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
          context.widthHalf context.widthLength context.state
          (coupledPrimitive_highSmall parameters L compact context.state context.small) tau := by
    exact (congrArg
      (fun mapping : CrossHighData parameters context.lower →L[ℝ]
        annularInnerZero context.lower L context.positive (context.lowerHalf.trans_lt (by norm_num)) context.lengthPositive => complexPartCLM mapping)
      (crossZeroEnergyOrbit_sameInverse parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
        context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small) tau).symm).trans
      (complexPartCLM_restrict _)
  intro axis order
  obtain ⟨constant, nonnegative, estimate⟩ := complexBound axis order
  refine ⟨constant, nonnegative, ?_⟩
  intro context base time
  have converted := estimate context base time
  simp only [same] at converted
  with_unfolding_all exact converted

end Grad.AnnularCrossOrbit
