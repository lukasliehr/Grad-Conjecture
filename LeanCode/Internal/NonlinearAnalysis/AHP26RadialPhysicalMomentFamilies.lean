import AHP25UniformRadialMomentAllocation

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.SourceCollarCoefficients Grad.ActualCurrentPrimitives
open Grad.GaugeCoefficients.Physical.Allocation

/-- The actual physical data on one original low ball, fixed before every
radius and every moment grade. -/
abbrev AnnularReconstructionState (parameters : PhaseParameters) (L compact : ℝ) :=
  {state : RadialCoefficientState parameters L compact //
    physicalBudget parameters state.field state.rho state.epsilon 7 ≤
      radialMassLowRadius parameters L compact}

namespace AnnularReconstructionState
variable {parameters : PhaseParameters} {L compact : ℝ}
abbrev size (state : AnnularReconstructionState parameters L compact) := state.val.size
 theorem firstSmall (state : AnnularReconstructionState parameters L compact) :
    physicalBudget parameters state.val.field state.val.rho state.val.epsilon 7 ≤
      radialFirstLowRadius parameters L compact := state.property.trans (min_le_left _ _)
 theorem gaugeSmall (state : AnnularReconstructionState parameters L compact) :
    physicalBudget parameters state.val.field state.val.rho state.val.epsilon 7 ≤
      radialGaugeLowRadius parameters L compact := state.firstSmall.trans (min_le_left _ _)
end AnnularReconstructionState

abbrev RadialPhysicalMoments (parameters : PhaseParameters) (L compact : ℝ)
    {input output : ℕ}
    (family : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output) : Prop :=
  UniformRadialKernelMoments parameters AnnularReconstructionState.size family

theorem RadialPhysicalMoments.fixed (parameters : PhaseParameters) (L compact : ℝ)
    {input output : ℕ}
    (family : (p : PhaseParameters) → FullTwoFrequencyKernel p input output)
    (same : ∀ first second, SameKernelEntries (family first) (family second)) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => family (radialKernelParameters parameters r)) :=
  UniformRadialKernelMoments.fixed (fun state => state.val.one_le_size) family same

theorem RadialPhysicalMoments.comp {parameters : PhaseParameters} {L compact : ℝ}
    {input middle output : ℕ}
    {outer : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r middle output}
    {inner : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input middle}
    (houter : RadialPhysicalMoments parameters L compact outer)
    (hinner : RadialPhysicalMoments parameters L compact inner) :
    RadialPhysicalMoments parameters L compact
      (fun state r => fullKernelComposition (outer state r) (inner state r)) :=
  UniformRadialKernelMoments.comp (fun state => state.val.size_nonnegative)
    (1 + actualMassInverseLowRadius parameters L compact)
    (by linarith [actualMassInverseLowRadius_positive parameters L compact])
    (fun state => state.val.size_zero_le) houter hinner

theorem radialForceKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ)
    (kind : Fin 2) : RadialPhysicalMoments parameters L compact
      (fun state r => radialForceKernel parameters L compact state.val r kind 0) := by
  intro moment
  let constant := 3 * Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
    forceFourierConstant parameters L kind moment 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state r
  apply (radialForceKernel_moment_le parameters L compact state.val r kind 0 moment).trans
  exact mul_le_mul (le_abs_self constant) (state.val.budget_le_size moment (moment + 0 + 6) (by omega))
    (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon _)
    (abs_nonneg constant)

theorem radialRotatedForceKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ)
    (kind : Fin 2) : RadialPhysicalMoments parameters L compact
      (fun state r => radialRotatedForceKernel parameters L compact state.val r kind 0) := by
  intro moment
  let constant := 3 * Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
    forceFourierConstant parameters L kind (moment + 1) 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state r
  apply (radialRotatedForceKernel_moment_le parameters L compact state.val r kind 0 moment).trans
  exact mul_le_mul (le_abs_self constant) (state.val.budget_le_size moment (moment + 1 + 0 + 6) (by omega))
    (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon _)
    (abs_nonneg constant)

end Grad.AnnularReconstruction
