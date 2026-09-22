import BCI10ActualHighBoundaryInverse

noncomputable section
set_option maxHeartbeats 1000000
namespace Grad.ActualBoundaryInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation

/-- Vanishing physical moments on the same original B7 state space. -/
abbrev BoundaryDeviationMoments (parameters : PhaseParameters) (L compact : ℝ) {input output : ℕ}
    (family : PhysicalBoundaryState parameters L compact → FullTwoFrequencyKernel parameters input output) : Prop :=
  UniformKernelMoments parameters (fun state => state.budget) family

private theorem budget_mul_base (parameters : PhaseParameters) (L compact : ℝ)
    (state : PhysicalBoundaryState parameters L compact) (moment : ℕ) :
    state.budget moment * state.val.size 0 ≤
      (1 + actualMassInverseLowRadius parameters L compact) * state.budget moment := by
  have bound := mul_le_mul_of_nonneg_left state.val.size_zero_le
    (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon (moment + 7))
  exact bound.trans_eq (mul_comm _ _)

private theorem base_mul_size (parameters : PhaseParameters) (L compact : ℝ)
    (state : PhysicalBoundaryState parameters L compact) (moment : ℕ) :
    state.budget 0 * state.val.size moment ≤
      (1 + actualMassInverseLowRadius parameters L compact) * state.budget moment := by
  have monotone : state.budget 0 ≤ state.budget moment :=
    physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (by omega)
  have low : state.budget 0 ≤ actualMassInverseLowRadius parameters L compact := state.val.small
  have product := mul_le_mul_of_nonneg_right low
    (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon (moment + 7))
  change state.budget 0 * (1 + state.budget moment) ≤ _
  nlinarith

/-- The high factor is allocated before applying either bound. No high
budget is required to be small. -/
theorem BoundaryDeviationMoments.comp_regular {parameters : PhaseParameters} {L compact : ℝ}
    {input middle output : ℕ}
    {outer : PhysicalBoundaryState parameters L compact → FullTwoFrequencyKernel parameters middle output}
    {inner : PhysicalBoundaryState parameters L compact → FullTwoFrequencyKernel parameters input middle}
    (houter : BoundaryDeviationMoments parameters L compact outer)
    (hinner : BoundaryKernelMoments parameters L compact inner) :
    BoundaryDeviationMoments parameters L compact (fun state => fullKernelComposition (outer state) (inner state)) := by
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
  intro state
  apply (fullKernelComposition_moment_le moment (outer state) (inner state)).trans
  have first := mul_le_mul (outerHighBound state) (innerLowBound state)
    (fullKernelMoment_nonnegative parameters 0 (inner state))
    (mul_nonneg outerHighNonnegative (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon (moment + 7)))
  have second := mul_le_mul (outerLowBound state) (innerHighBound state)
    (fullKernelMoment_nonnegative parameters moment (inner state))
    (mul_nonneg outerLowNonnegative (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon 7))
  have firstAllocation := mul_le_mul_of_nonneg_left (budget_mul_base parameters L compact state moment)
    (mul_nonneg outerHighNonnegative innerLowNonnegative)
  have secondAllocation := mul_le_mul_of_nonneg_left (base_mul_size parameters L compact state moment)
    (mul_nonneg outerLowNonnegative innerHighNonnegative)
  have added : fullKernelMoment parameters moment (outer state) * fullKernelMoment parameters 0 (inner state) +
      fullKernelMoment parameters 0 (outer state) * fullKernelMoment parameters moment (inner state) ≤
      (outerHigh * innerLow + outerLow * innerHigh) * radius * state.budget moment := by
    dsimp only [radius] at *
    nlinarith
  exact (mul_le_mul_of_nonneg_left added (by positivity : 0 ≤ (2 : ℝ) ^ moment)).trans_eq (by ring)

theorem BoundaryDeviationMoments.regular_comp {parameters : PhaseParameters} {L compact : ℝ}
    {input middle output : ℕ}
    {outer : PhysicalBoundaryState parameters L compact → FullTwoFrequencyKernel parameters middle output}
    {inner : PhysicalBoundaryState parameters L compact → FullTwoFrequencyKernel parameters input middle}
    (houter : BoundaryKernelMoments parameters L compact outer)
    (hinner : BoundaryDeviationMoments parameters L compact inner) :
    BoundaryDeviationMoments parameters L compact (fun state => fullKernelComposition (outer state) (inner state)) := by
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
  intro state
  apply (fullKernelComposition_moment_le moment (outer state) (inner state)).trans
  have first := mul_le_mul (outerHighBound state) (innerLowBound state)
    (fullKernelMoment_nonnegative parameters 0 (inner state))
    (mul_nonneg outerHighNonnegative (state.val.size_nonnegative moment))
  have second := mul_le_mul (outerLowBound state) (innerHighBound state)
    (fullKernelMoment_nonnegative parameters moment (inner state))
    (mul_nonneg outerLowNonnegative (state.val.size_nonnegative 0))
  have firstAllocation := mul_le_mul_of_nonneg_left (base_mul_size parameters L compact state moment)
    (mul_nonneg outerHighNonnegative innerLowNonnegative)
  have secondAllocation := mul_le_mul_of_nonneg_left (budget_mul_base parameters L compact state moment)
    (mul_nonneg outerLowNonnegative innerHighNonnegative)
  have added : fullKernelMoment parameters moment (outer state) * fullKernelMoment parameters 0 (inner state) +
      fullKernelMoment parameters 0 (outer state) * fullKernelMoment parameters moment (inner state) ≤
      (outerHigh * innerLow + outerLow * innerHigh) * radius * state.budget moment := by
    dsimp only [radius] at *
    nlinarith
  exact (mul_le_mul_of_nonneg_left added (by positivity : 0 ≤ (2 : ℝ) ^ moment)).trans_eq (by ring)

end Grad.ActualBoundaryInverse
