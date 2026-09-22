import AHS16OriginalRadiusForceGaugeConsumer

noncomputable section
set_option maxHeartbeats 1000000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation

namespace AnnularReconstructionState
variable {parameters : PhaseParameters} {L compact : ℝ}
abbrev errorBudget (state : AnnularReconstructionState parameters L compact) (moment : ℕ) : ℝ :=
  physicalBudget parameters state.val.field state.val.rho state.val.epsilon (moment + 7)
end AnnularReconstructionState

/-- Vanishing physical moments on the same original B7 state space. -/
abbrev RadialDeviationMoments (parameters : PhaseParameters) (L compact : ℝ) {input output : ℕ}
    (family : (state : AnnularReconstructionState parameters L compact) → (r : RadialPoint) → RadialKernel parameters r input output) : Prop :=
  UniformRadialKernelMoments parameters (fun state => state.errorBudget) family

private theorem budget_mul_base (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (moment : ℕ) :
    state.errorBudget moment * state.val.size 0 ≤
      (1 + actualMassInverseLowRadius parameters L compact) * state.errorBudget moment := by
  have bound := mul_le_mul_of_nonneg_left state.val.size_zero_le
    (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon (moment + 7))
  exact bound.trans_eq (mul_comm _ _)

private theorem base_mul_size (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (moment : ℕ) :
    state.errorBudget 0 * state.val.size moment ≤
      (1 + actualMassInverseLowRadius parameters L compact) * state.errorBudget moment := by
  have monotone : state.errorBudget 0 ≤ state.errorBudget moment :=
    physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (by omega)
  have low : state.errorBudget 0 ≤ actualMassInverseLowRadius parameters L compact := state.val.small
  have product := mul_le_mul_of_nonneg_right low
    (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon (moment + 7))
  change state.errorBudget 0 * (1 + state.errorBudget moment) ≤ _
  nlinarith

/-- The high factor is allocated before applying either bound. No high
budget is required to be small. -/
theorem RadialDeviationMoments.comp_regular {parameters : PhaseParameters} {L compact : ℝ}
    {input middle output : ℕ}
    {outer : (state : AnnularReconstructionState parameters L compact) → (r : RadialPoint) → RadialKernel parameters r middle output}
    {inner : (state : AnnularReconstructionState parameters L compact) → (r : RadialPoint) → RadialKernel parameters r input middle}
    (houter : RadialDeviationMoments parameters L compact outer)
    (hinner : RadialPhysicalMoments parameters L compact inner) :
    RadialDeviationMoments parameters L compact (fun state r => fullKernelComposition (outer state r) (inner state r)) := by
  intro moment
  obtain ⟨outerHigh, outerHighNonnegative, outerHighBound⟩ := houter moment
  obtain ⟨outerLow, outerLowNonnegative, outerLowBound⟩ := houter 0
  obtain ⟨innerHigh, innerHighNonnegative, innerHighBound⟩ := hinner moment
  obtain ⟨innerLow, innerLowNonnegative, innerLowBound⟩ := hinner 0
  let radius := 1 + actualMassInverseLowRadius parameters L compact
  have radiusNonnegative : 0 ≤ radius := by dsimp [radius]; linarith [actualMassInverseLowRadius_positive parameters L compact]
  refine ⟨2 ^ moment * (outerHigh * innerLow + outerLow * innerHigh) * radius,
    mul_nonneg (mul_nonneg (by positivity) (add_nonneg (mul_nonneg outerHighNonnegative innerLowNonnegative)
      (mul_nonneg outerLowNonnegative innerHighNonnegative))) radiusNonnegative, ?_⟩
  intro state r
  apply (fullKernelComposition_moment_le moment (outer state r) (inner state r)).trans
  have first := mul_le_mul (outerHighBound state r) (innerLowBound state r)
    (fullKernelMoment_nonnegative (radialKernelParameters parameters r) 0 (inner state r))
    (mul_nonneg outerHighNonnegative (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon (moment + 7)))
  have second := mul_le_mul (outerLowBound state r) (innerHighBound state r)
    (fullKernelMoment_nonnegative (radialKernelParameters parameters r) moment (inner state r))
    (mul_nonneg outerLowNonnegative (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon 7))
  have firstAllocation := mul_le_mul_of_nonneg_left (budget_mul_base parameters L compact state moment)
    (mul_nonneg outerHighNonnegative innerLowNonnegative)
  have secondAllocation := mul_le_mul_of_nonneg_left (base_mul_size parameters L compact state moment)
    (mul_nonneg outerLowNonnegative innerHighNonnegative)
  have added : fullKernelMoment (radialKernelParameters parameters r) moment (outer state r) * fullKernelMoment (radialKernelParameters parameters r) 0 (inner state r) +
      fullKernelMoment (radialKernelParameters parameters r) 0 (outer state r) * fullKernelMoment (radialKernelParameters parameters r) moment (inner state r) ≤
      (outerHigh * innerLow + outerLow * innerHigh) * radius * state.errorBudget moment := by
    dsimp only [radius] at *
    nlinarith
  exact (mul_le_mul_of_nonneg_left added (by positivity : 0 ≤ (2 : ℝ) ^ moment)).trans_eq (by ring)

theorem RadialDeviationMoments.regular_comp {parameters : PhaseParameters} {L compact : ℝ}
    {input middle output : ℕ}
    {outer : (state : AnnularReconstructionState parameters L compact) → (r : RadialPoint) → RadialKernel parameters r middle output}
    {inner : (state : AnnularReconstructionState parameters L compact) → (r : RadialPoint) → RadialKernel parameters r input middle}
    (houter : RadialPhysicalMoments parameters L compact outer)
    (hinner : RadialDeviationMoments parameters L compact inner) :
    RadialDeviationMoments parameters L compact (fun state r => fullKernelComposition (outer state r) (inner state r)) := by
  intro moment
  obtain ⟨outerHigh, outerHighNonnegative, outerHighBound⟩ := houter moment
  obtain ⟨outerLow, outerLowNonnegative, outerLowBound⟩ := houter 0
  obtain ⟨innerHigh, innerHighNonnegative, innerHighBound⟩ := hinner moment
  obtain ⟨innerLow, innerLowNonnegative, innerLowBound⟩ := hinner 0
  let radius := 1 + actualMassInverseLowRadius parameters L compact
  have radiusNonnegative : 0 ≤ radius := by dsimp [radius]; linarith [actualMassInverseLowRadius_positive parameters L compact]
  refine ⟨2 ^ moment * (outerHigh * innerLow + outerLow * innerHigh) * radius,
    mul_nonneg (mul_nonneg (by positivity) (add_nonneg (mul_nonneg outerHighNonnegative innerLowNonnegative)
      (mul_nonneg outerLowNonnegative innerHighNonnegative))) radiusNonnegative, ?_⟩
  intro state r
  apply (fullKernelComposition_moment_le moment (outer state r) (inner state r)).trans
  have first := mul_le_mul (outerHighBound state r) (innerLowBound state r)
    (fullKernelMoment_nonnegative (radialKernelParameters parameters r) 0 (inner state r))
    (mul_nonneg outerHighNonnegative (state.val.size_nonnegative moment))
  have second := mul_le_mul (outerLowBound state r) (innerHighBound state r)
    (fullKernelMoment_nonnegative (radialKernelParameters parameters r) moment (inner state r))
    (mul_nonneg outerLowNonnegative (state.val.size_nonnegative 0))
  have firstAllocation := mul_le_mul_of_nonneg_left (base_mul_size parameters L compact state moment)
    (mul_nonneg outerHighNonnegative innerLowNonnegative)
  have secondAllocation := mul_le_mul_of_nonneg_left (budget_mul_base parameters L compact state moment)
    (mul_nonneg outerLowNonnegative innerHighNonnegative)
  have added : fullKernelMoment (radialKernelParameters parameters r) moment (outer state r) * fullKernelMoment (radialKernelParameters parameters r) 0 (inner state r) +
      fullKernelMoment (radialKernelParameters parameters r) 0 (outer state r) * fullKernelMoment (radialKernelParameters parameters r) moment (inner state r) ≤
      (outerHigh * innerLow + outerLow * innerHigh) * radius * state.errorBudget moment := by
    dsimp only [radius] at *
    nlinarith
  exact (mul_le_mul_of_nonneg_left added (by positivity : 0 ≤ (2 : ℝ) ^ moment)).trans_eq (by ring)

end Grad.AnnularReconstruction
