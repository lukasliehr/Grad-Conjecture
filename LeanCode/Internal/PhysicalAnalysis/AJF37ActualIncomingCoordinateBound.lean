import AJF32ActualLiftedFunctionalCoordinateBounds
import AJF33UniformRealOperatorOperations
import AJF22ActualIncomingSolverOneHigh
import AJD29SameDiagonalCoordinateBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational
open Grad.CartesianState Grad.AnnularKernelOrbit Grad.AnnularCrossOrbit Grad.AnnularHighInverseOrbit
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularReconstruction Grad.AnnularOrbitGenerators
open Grad.AnnularCoupledInverse Grad.AnnularCurrentSolution

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

section GenericLift
variable {Context : Type*} {D E V : Context → Type*}
  [∀ context, NormedAddCommGroup (D context)] [∀ context, NormedSpace ℝ (D context)]
  [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace ℝ (E context)]
  [∀ context, NormedAddCommGroup (V context)] [∀ context, NormedSpace ℝ (V context)]

theorem uniformCoordinateBound_liftCorrection
    (budget : Context → ℕ → ℝ)
    (outer : (context : Context) → OrbitParameter → V context →L[ℝ] E context)
    (form : (context : Context) → OrbitParameter → E context →L[ℝ] V context)
    (outerBound : UniformCoordinateBound budget outer) (formBound : UniformCoordinateBound budget form)
    (outerSmooth : ∀ context, ContDiff ℝ ∞ (outer context))
    (formSmooth : ∀ context, ContDiff ℝ ∞ (form context))
    (lift : (context : Context) → D context →L[ℝ] E context)
    (constant : ℝ) (nonnegative : 0 ≤ constant) (liftBound : ∀ context, ‖lift context‖ ≤ constant)
    (budgetNonnegative : ∀ context order, 0 ≤ budget context order)
    (pair : ℕ → ℝ) (pairNonnegative : ∀ order, 0 ≤ pair order)
    (paired : ∀ context a b, budget context a * budget context b ≤ pair (a + b) * budget context (a + b)) :
    UniformCoordinateBound budget (fun context tau => lift context - (outer context tau).comp ((form context tau).comp (lift context))) := by
  have correction := outerBound.composeReal formBound outerSmooth formSmooth budgetNonnegative pair pairNonnegative paired
  have correctionSmooth (context : Context) := realOperatorComposition_contDiff _ _ (outerSmooth context) (formSmooth context)
  have lifted := uniformCoordinateBound_precomposeReal correction correctionSmooth lift constant nonnegative liftBound
  have liftedSmooth (context : Context) := realOperatorComposition_contDiff
    (fun tau => (outer context tau).comp (form context tau)) (fun _ : OrbitParameter => lift context)
    (correctionSmooth context) contDiff_const
  have fixed := UniformCoordinateBound.const budgetNonnegative lift constant nonnegative liftBound
  have result := fixed.add (lifted.neg liftedSmooth) (fun _ => contDiff_const) (fun context => (liftedSmooth context).neg)
  simpa only [sub_eq_add_neg, ContinuousLinearMap.comp_assoc] using result


end GenericLift

variable (parameters : PhaseParameters) (L compact : ℝ)

local instance incomingFamilyNormed (context : CoupledCoordinateContext parameters L compact) :
    NormedAddCommGroup (AnnularBoundary →L[ℝ] annularEnergySpace context.lower L context.positive) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance incomingFamilySeminormed (context : CoupledCoordinateContext parameters L compact) :
    SeminormedAddCommGroup (AnnularBoundary →L[ℝ] annularEnergySpace context.lower L context.positive) :=
  (incomingFamilyNormed parameters L compact context).toSeminormedAddCommGroup
local instance incomingFamilyRealNormed (context : CoupledCoordinateContext parameters L compact) :
    NormedSpace ℝ (AnnularBoundary →L[ℝ] annularEnergySpace context.lower L context.positive) :=
  ContinuousLinearMap.toNormedSpace
local instance incomingFamilyRealModule (context : CoupledCoordinateContext parameters L compact) :
    Module ℝ (AnnularBoundary →L[ℝ] annularEnergySpace context.lower L context.positive) :=
  (incomingFamilyRealNormed parameters L compact context).toModule

def incomingUniformProposition : Prop :=
  UniformCoordinateBound CoupledCoordinateContext.budget
    (fun context : CoupledCoordinateContext parameters L compact =>
      highIncomingSolverOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
        context.widthHalf context.widthLength context.state
        (coupledPrimitive_highSmall parameters L compact context.state context.small))

theorem highSourceSolverOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        highSourceSolverOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
          context.widthHalf context.widthLength context.state
          (coupledPrimitive_highSmall parameters L compact context.state context.small)) := by
  apply uniformCoordinateBound_postcomposeReal (currentHighInverseOrbit_uniformCoordinateBound parameters L compact)
    (fun context => currentHighInverseOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
          context.widthHalf context.widthLength context.state
          (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (fun context => annularZeroRealInclusion context.lower L context.positive
      (context.lowerHalf.trans_lt (by norm_num)) context.lengthPositive) 1 (by norm_num)
  intro context
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro value
  change ‖value.val‖ ≤ 1 * ‖value‖
  exact (one_mul ‖value‖).symm.le

theorem incomingCorrectionUniform :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun (context : CoupledCoordinateContext parameters L compact) tau => (highSourceSolverOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small) tau).comp (liftedTestFunctionalOrbitJet parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state 0 0 tau)) := by
  apply (highSourceSolverOrbit_uniformCoordinateBound parameters L compact).composeReal
    (X := fun context : CoupledCoordinateContext parameters L compact => annularEnergySpace context.lower L context.positive)
    (E := fun context : CoupledCoordinateContext parameters L compact =>
      annularInnerZero context.lower L context.positive (context.lowerHalf.trans_lt (by norm_num)) context.lengthPositive →L[ℝ] ℝ)
    (F := fun context : CoupledCoordinateContext parameters L compact => annularEnergySpace context.lower L context.positive)
    (liftedTestFunctionalOrbit_uniformCoordinateBound parameters L compact)
    (fun context => highSourceSolverOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (fun context => liftedTestFunctionalOrbitJet_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state 0 0)
    CoupledCoordinateContext.budget_nonnegative (fun order => Grad.GaugeCoefficients.Physical.Allocation.pairBudgetConstant 8 order 1)
    (fun order => Grad.GaugeCoefficients.Physical.Allocation.pairBudgetConstant_nonnegative 8 order (by norm_num))
    CoupledCoordinateContext.budget_pair

/-- Uniform coordinate estimates for the actual nonzero-incoming high
solver, using the original physical lift and the SAME high inverse. -/
theorem highIncomingSolverOrbit_uniformCoordinateBound : incomingUniformProposition parameters L compact := by
  exact uniformCoordinateBound_liftCorrection
    (D := fun _ : CoupledCoordinateContext parameters L compact => AnnularBoundary)
    (E := fun context : CoupledCoordinateContext parameters L compact => annularEnergySpace context.lower L context.positive)
    (V := fun context : CoupledCoordinateContext parameters L compact =>
      annularInnerZero context.lower L context.positive (context.lowerHalf.trans_lt (by norm_num)) context.lengthPositive →L[ℝ] ℝ)
    CoupledCoordinateContext.budget
    (fun context => highSourceSolverOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (fun context => liftedTestFunctionalOrbitJet parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state 0 0)
    (highSourceSolverOrbit_uniformCoordinateBound parameters L compact)
    (liftedTestFunctionalOrbit_uniformCoordinateBound parameters L compact)
    (fun context => highSourceSolverOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (fun context => liftedTestFunctionalOrbitJet_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state 0 0)
    (fun context => (physicalIncomingLift context.lower L context.positive context.lowerHalf context.lengthPositive).restrictScalars ℝ)
    (2 * Grad.AnnularUniformBoundary.uniformInnerLiftConstant L)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    (fun context => physicalIncomingLift_real_norm L context.lower context.positive context.lowerHalf context.lengthPositive)
    CoupledCoordinateContext.budget_nonnegative
    (fun order => Grad.GaugeCoefficients.Physical.Allocation.pairBudgetConstant 8 order 1)
    (fun order => Grad.GaugeCoefficients.Physical.Allocation.pairBudgetConstant_nonnegative 8 order (by norm_num))
    CoupledCoordinateContext.budget_pair

end Grad.AnnularHighGenerators
