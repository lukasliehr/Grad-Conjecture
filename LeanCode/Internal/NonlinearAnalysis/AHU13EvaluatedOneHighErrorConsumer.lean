import AHU12ExactAnnularErrorConsumer

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

theorem RadialDeviationMoments.oneHigh_bound
    {parameters : PhaseParameters} {L compact : ℝ} {input output : ℕ}
    {family : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output}
    (bounded : RadialDeviationMoments parameters L compact family) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ state (r : RadialPoint) (high : NegativeTotalTrace (radialKernelParameters parameters r) grade input)
        (low : NegativeTotalTrace (radialKernelParameters parameters r) 0 input),
        ‖fullOneHighKernelAction (radialKernelParameters parameters r) grade (family state r) high low‖ ≤
          constant * (state.errorBudget 1 * ‖high‖ + state.errorBudget (grade + 1) * ‖low‖) := by
  obtain ⟨lowConstant, lowNonnegative, lowBound⟩ := bounded 1
  obtain ⟨highConstant, highNonnegative, highBound⟩ := bounded (grade + 1)
  refine ⟨2 ^ grade * (lowConstant + highConstant), by positivity, ?_⟩
  intro state r high low
  have lowSizeNonnegative := physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon 8
  have highSizeNonnegative := physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon ((grade + 1) + 7)
  apply (fullOneHighKernelAction_bound (radialKernelParameters parameters r) grade (family state r) high low).trans
  calc
    _ ≤ 2 ^ grade *
      ((lowConstant * state.errorBudget 1) * ‖high‖ +
        (highConstant * state.errorBudget (grade + 1)) * ‖low‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul_of_nonneg_right (lowBound state r) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (highBound state r) (norm_nonneg _))
    _ ≤ 2 ^ grade *
      (((lowConstant + highConstant) * state.errorBudget 1) * ‖high‖ +
        ((lowConstant + highConstant) * state.errorBudget (grade + 1)) * ‖low‖) := by
      gcongr <;> linarith
    _ = _ := by ring

/-- Evaluated negative-half trace error: B8 multiplies the high input,
and B_(grade+8) multiplies the low input. The constant precedes the radius. -/
theorem actualRadialNormalizedCovariantError_oneHigh
    (parameters : PhaseParameters) (L compact : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (state : AnnularReconstructionState parameters L compact) (r : RadialPoint)
        (high : NegativeTotalTrace (radialKernelParameters parameters r) grade 7)
        (low : NegativeTotalTrace (radialKernelParameters parameters r) 0 7),
      ‖fullOneHighKernelAction (radialKernelParameters parameters r) grade
        (fullKernelSub
          (radialNormalizedCovariantKernel parameters L compact state.val r state.property)
          (circularNormalizedCovariantKernel (radialKernelParameters parameters r) L)) high low‖ ≤
      constant *
        (physicalBudget parameters state.val.field state.val.rho state.val.epsilon 8 * ‖high‖ +
          physicalBudget parameters state.val.field state.val.rho state.val.epsilon (grade + 8) * ‖low‖) := by
  simpa only [AnnularReconstructionState.errorBudget, Nat.reduceAdd, Nat.add_assoc] using
    RadialDeviationMoments.oneHigh_bound
      (radialNormalizedCovariantKernel_referenceDifference parameters L compact) grade

/-- Evaluated negative-half trace error: B8 multiplies the high input,
and B_(grade+8) multiplies the low input. The constant precedes the radius. -/
theorem actualRadialNormalizedRotatedCovariantError_oneHigh
    (parameters : PhaseParameters) (L compact : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (state : AnnularReconstructionState parameters L compact) (r : RadialPoint)
        (high : NegativeTotalTrace (radialKernelParameters parameters r) grade 7)
        (low : NegativeTotalTrace (radialKernelParameters parameters r) 0 7),
      ‖fullOneHighKernelAction (radialKernelParameters parameters r) grade
        (fullKernelSub
          (radialNormalizedRotatedCovariantKernel parameters L compact state.val r state.property)
          (circularNormalizedRotatedCovariantKernel (radialKernelParameters parameters r) L)) high low‖ ≤
      constant *
        (physicalBudget parameters state.val.field state.val.rho state.val.epsilon 8 * ‖high‖ +
          physicalBudget parameters state.val.field state.val.rho state.val.epsilon (grade + 8) * ‖low‖) := by
  simpa only [AnnularReconstructionState.errorBudget, Nat.reduceAdd, Nat.add_assoc] using
    RadialDeviationMoments.oneHigh_bound
      (radialNormalizedRotatedCovariantKernel_referenceDifference parameters L compact) grade

/-- On compatible representatives this is the actual error Fourier action,
not the sum of two independently interpreted input fields. -/
theorem actualRadialNormalizedCovariantError_oneHigh_physical
    (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (r : RadialPoint) (grade : ℕ)
    (high : NegativeTotalTrace (radialKernelParameters parameters r) grade 7)
    (low : NegativeTotalTrace (radialKernelParameters parameters r) 0 7)
    (compatible : TotalTraceCompatible (radialKernelParameters parameters r) grade high low)
    (mode : ℤ × ℤ) :
    let error := fullKernelSub
      (radialNormalizedCovariantKernel parameters L compact state.val r state.property)
      (circularNormalizedCovariantKernel (radialKernelParameters parameters r) L)
    HasSum (fun shift => error.entry shift (twoFrequencyTranslation shift mode)
      (negativeTotalCoefficient (radialKernelParameters parameters r) grade high
        (twoFrequencyTranslation shift mode)))
      (negativeTotalCoefficient (radialKernelParameters parameters r) grade
        (fullOneHighKernelAction (radialKernelParameters parameters r) grade error high low) mode) :=
  fullOneHighKernelAction_coefficient_hasSum _ _ _ _ _ compatible _

end Grad.AnnularReconstruction
