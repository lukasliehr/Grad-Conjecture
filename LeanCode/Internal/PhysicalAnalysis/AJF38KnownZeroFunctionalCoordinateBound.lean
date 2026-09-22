import AJF31FullKnownFunctionalCoordinateBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularCurrentSource
open Grad.CartesianState Grad.AnnularKernelOrbit Grad.AnnularCrossOrbit Grad.AnnularStrongOrbit
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularStrongData
open Grad.AnnularReconstruction Grad.AnnularOrbitGenerators Grad.AnnularHighInverseOrbit

attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

section Restriction
variable {X W V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem operatorTestRestriction_norm (inclusion : V →L[ℝ] W) (isometry : ∀ test, ‖inclusion test‖ = ‖test‖)
    (functional : X →L[ℝ] W →L[ℝ] ℝ) :
    ‖operatorTestRestriction inclusion functional‖ ≤ ‖functional‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg functional)
  intro source
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg functional) (norm_nonneg source))
  intro test
  change ‖functional source (inclusion test)‖ ≤ (‖functional‖ * ‖source‖) * ‖test‖
  exact ((functional source).le_opNorm (inclusion test)).trans
    ((mul_le_mul_of_nonneg_right (functional.le_opNorm source) (norm_nonneg _)).trans_eq
      (congrArg (fun size : ℝ => (‖functional‖ * ‖source‖) * size) (isometry test)))
end Restriction

section UniformRestriction
variable {Context : Type*} {X W V : Context → Type*}
  [∀ context, NormedAddCommGroup (X context)] [∀ context, NormedSpace ℝ (X context)]
  [∀ context, NormedAddCommGroup (W context)] [∀ context, NormedSpace ℝ (W context)]
  [∀ context, NormedAddCommGroup (V context)] [∀ context, NormedSpace ℝ (V context)]
  {budget : Context → ℕ → ℝ}

theorem uniformCoordinateBound_testRestriction
    (family : (context : Context) → Grad.AnnularKernelOrbit.OrbitParameter → X context →L[ℝ] W context →L[ℝ] ℝ)
    (bound : UniformCoordinateBound budget family) (smooth : ∀ context, ContDiff ℝ ∞ (family context))
    (inclusion : (context : Context) → V context →L[ℝ] W context)
    (isometry : ∀ context value, ‖inclusion context value‖ = ‖value‖) :
    UniformCoordinateBound budget (fun context tau => operatorTestRestriction (inclusion context) (family context tau)) := by
  apply bound.map_bound (F := fun context => X context →L[ℝ] V context →L[ℝ] ℝ) smooth
    (fun context => operatorTestRestriction (X := X context) (W := W context) (V := V context) (inclusion context)) 1 (by norm_num)
  intro context functional
  exact (operatorTestRestriction_norm (inclusion context) (isometry context) functional).trans_eq (one_mul _).symm
end UniformRestriction

variable (parameters : PhaseParameters) (L compact : ℝ)

theorem knownZeroFunctionalOrbit_uniformCoordinateBound :
    UniformCoordinateBound (augmentedBudget CoupledCoordinateContext.budget)
      (fun context : CoupledCoordinateContext parameters L compact =>
        knownZeroFunctionalOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
          context.widthHalf context.widthLength context.state) :=
  uniformCoordinateBound_testRestriction
    (X := fun context : CoupledCoordinateContext parameters L compact => ActualHighKnownAmbient parameters context.lower 0 0)
    (W := fun context : CoupledCoordinateContext parameters L compact => annularEnergySpace context.lower L context.positive)
    (V := fun context : CoupledCoordinateContext parameters L compact =>
      annularInnerZero context.lower L context.positive (context.lowerHalf.trans_lt (by norm_num)) context.lengthPositive)
    (fun context => knownFunctionalOrbitJet parameters L compact context.lower context.positive context.lowerHalf
      context.lengthPositive context.widthHalf context.widthLength context.state 0 0)
    (knownFunctionalOrbit_uniformCoordinateBound parameters L compact)
    (fun context => knownFunctionalOrbitJet_contDiff parameters L compact context.lower context.positive context.lowerHalf
      context.lengthPositive context.widthHalf context.widthLength context.state 0 0)
    (fun context => annularZeroRealInclusion context.lower L context.positive
      (context.lowerHalf.trans_lt (by norm_num)) context.lengthPositive)
    (fun _ _ => rfl)

end Grad.AnnularHighGenerators
