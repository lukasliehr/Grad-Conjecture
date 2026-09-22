import AEH1HighBoundaryEmbedding

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace Grad.AnnularCurrentBoundary

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Allocation

/-- Vanishing moments for kernels on the completed outer-inverse ball.  This
is the boundary analogue of the retained radial inverse error allocation. -/
abbrev BoundaryLiftDeviationMoments (parameters : PhaseParameters) (L compact : ℝ)
    {input output : ℕ}
    (family : BoundaryInverseState parameters L compact →
      FullTwoFrequencyKernel parameters input output) : Prop :=
  UniformKernelMoments parameters (fun state => state.val.budget) family

private theorem boundaryLift_budget_mul_base
    (parameters : PhaseParameters) (L compact : ℝ)
    (state : BoundaryInverseState parameters L compact) (moment : ℕ) :
    state.val.budget moment * state.val.val.size 0 ≤
      (1 + actualMassInverseLowRadius parameters L compact) *
        state.val.budget moment := by
  have bound := mul_le_mul_of_nonneg_left state.val.val.size_zero_le
    (physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho
      state.val.val.epsilon (moment + 7))
  exact bound.trans_eq (mul_comm _ _)

private theorem boundaryLift_base_mul_size
    (parameters : PhaseParameters) (L compact : ℝ)
    (state : BoundaryInverseState parameters L compact) (moment : ℕ) :
    state.val.budget 0 * state.val.val.size moment ≤
      (1 + actualMassInverseLowRadius parameters L compact) *
        state.val.budget moment := by
  have monotone : state.val.budget 0 ≤ state.val.budget moment :=
    physicalBudget_monotone parameters state.val.val.field state.val.val.rho
      state.val.val.epsilon (by omega)
  have low : state.val.budget 0 ≤ actualMassInverseLowRadius parameters L compact :=
    state.val.val.small
  have product := mul_le_mul_of_nonneg_right low
    (physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho
      state.val.val.epsilon (moment + 7))
  change state.val.budget 0 * (1 + state.val.budget moment) ≤ _
  nlinarith

/-- A uniformly regular inverse followed by a boundary coefficient which
vanishes at the circular state still has one exact physical budget factor. -/
theorem boundaryInverse_regular_comp_vanishing
    {parameters : PhaseParameters} {L compact : ℝ}
    {input middle output : ℕ}
    {outer : BoundaryInverseState parameters L compact →
      FullTwoFrequencyKernel parameters middle output}
    {inner : PhysicalBoundaryState parameters L compact →
      FullTwoFrequencyKernel parameters input middle}
    (houter : BoundaryInverseMoments parameters L compact outer)
    (hinner : BoundaryDeviationMoments parameters L compact inner) :
    BoundaryLiftDeviationMoments parameters L compact
      (fun state => fullKernelComposition (outer state) (inner state.val)) := by
  intro moment
  obtain ⟨outerHigh, outerHighNonnegative, outerHighBound⟩ := houter moment
  obtain ⟨outerLow, outerLowNonnegative, outerLowBound⟩ := houter 0
  obtain ⟨innerHigh, innerHighNonnegative, innerHighBound⟩ := hinner moment
  obtain ⟨innerLow, innerLowNonnegative, innerLowBound⟩ := hinner 0
  let radius := 1 + actualMassInverseLowRadius parameters L compact
  have radiusNonnegative : 0 ≤ radius := by
    dsimp [radius]
    linarith [actualMassInverseLowRadius_positive parameters L compact]
  refine ⟨2 ^ moment * (outerHigh * innerLow + outerLow * innerHigh) * radius,
    mul_nonneg (mul_nonneg (by positivity)
      (add_nonneg (mul_nonneg outerHighNonnegative innerLowNonnegative)
        (mul_nonneg outerLowNonnegative innerHighNonnegative))) radiusNonnegative, ?_⟩
  intro state
  apply (fullKernelComposition_moment_le moment (outer state) (inner state.val)).trans
  have first := mul_le_mul (outerHighBound state) (innerLowBound state.val)
    (fullKernelMoment_nonnegative parameters 0 (inner state.val))
    (mul_nonneg outerHighNonnegative (state.val.val.size_nonnegative moment))
  have second := mul_le_mul (outerLowBound state) (innerHighBound state.val)
    (fullKernelMoment_nonnegative parameters moment (inner state.val))
    (mul_nonneg outerLowNonnegative (state.val.val.size_nonnegative 0))
  have firstAllocation := mul_le_mul_of_nonneg_left
    (boundaryLift_base_mul_size parameters L compact state moment)
    (mul_nonneg outerHighNonnegative innerLowNonnegative)
  have secondAllocation := mul_le_mul_of_nonneg_left
    (boundaryLift_budget_mul_base parameters L compact state moment)
    (mul_nonneg outerLowNonnegative innerHighNonnegative)
  have added :
      fullKernelMoment parameters moment (outer state) *
          fullKernelMoment parameters 0 (inner state.val) +
        fullKernelMoment parameters 0 (outer state) *
          fullKernelMoment parameters moment (inner state.val) ≤
      (outerHigh * innerLow + outerLow * innerHigh) * radius *
        state.val.budget moment := by
    dsimp only [radius] at *
    nlinarith
  exact (mul_le_mul_of_nonneg_left added
    (by positivity : 0 ≤ (2 : ℝ) ^ moment)).trans_eq (by ring)

/-- The literal retained lift kernel `-T⁻¹N` has `C_q B_(q+7)` moments;
the budget factor is not weakened to `1+B`. -/
theorem actualRetainedBoundaryLiftKernel_vanishingMoments
    (parameters : PhaseParameters) (L compact : ℝ) :
    BoundaryLiftDeviationMoments parameters L compact
      actualRetainedBoundaryLiftKernel := by
  exact UniformKernelMoments.neg
    (boundaryInverse_regular_comp_vanishing
      (actualHighBoundaryInverse_physicalMoments parameters L compact)
      (actualBoundaryN_vanishingMoments parameters L compact))

end Grad.AnnularCurrentBoundary
