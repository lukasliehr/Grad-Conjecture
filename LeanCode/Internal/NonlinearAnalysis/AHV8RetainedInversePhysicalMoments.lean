import AHV7ActualRetainedInverseIdentities

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation

/-- Exact ordered tail relative to the negative circular b_m inverse. -/
theorem radialRetainedHighInverse_reference_tail (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) :
    fullKernelAdd (radialRetainedHighInverse parameters L compact state r)
      (retainedBInverseKernel (radialKernelParameters parameters r)) =
      fullKernelNeg (fullKernelComposition
        (fullKernelNeumannTail (radialKernelParameters parameters r)
          (radialRetainedPreconditionKernel parameters L compact state.val r) (1 / 2)
          (radialRetainedPreconditionKernel_small parameters L compact state r) (by norm_num))
        (retainedBInverseKernel (radialKernelParameters parameters r))) := by
  unfold radialRetainedHighInverse radialRetainedAmbientInverse fullKernelNegativeIdentityInverse fullKernelNeumannSum
  rw [fullKernelComposition_neg_outer, fullKernelComposition_add_outer, fullIdentityKernel_comp]
  apply FullTwoFrequencyKernel.ext_entry
  intro shift mode
  simp only [fullKernelAdd_entry, fullKernelNeg_entry]
  abel

/-- The inverse error has one vanishing physical budget at every grade,
uniformly at every radius including the axis. -/
theorem radialRetainedHighInverse_referenceMoments (parameters : PhaseParameters) (L compact : ℝ) :
    UniformRadialKernelMoments parameters (fun state : RetainedInverseState parameters L compact => state.val.errorBudget)
      (fun state r => fullKernelAdd (radialRetainedHighInverse parameters L compact state r)
        (retainedBInverseKernel (radialKernelParameters parameters r))) := by
  intro moment
  obtain ⟨highConstant, highNonnegative, highBound⟩ := radialRetainedPreconditionKernel_vanishingMoments parameters L compact moment
  obtain ⟨baseConstant, baseNonnegative, baseBound⟩ := radialRetainedPreconditionKernel_vanishingMoments parameters L compact 0
  have neumannNonnegative (q : ℕ) : 0 ≤ fullKernelNeumannConstant q (1 / 2) := by
    unfold fullKernelNeumannConstant
    exact tsum_nonneg (fun _ => by positivity)
  let fixed (q : ℕ) := fullKernelMoment (maximalKernelParameters parameters) q
    (retainedBInverseKernel (maximalKernelParameters parameters))
  have fixedNonnegative (q : ℕ) : 0 ≤ fixed q := fullKernelMoment_nonnegative _ _ _
  have fixedBound (r : RadialPoint) (q : ℕ) :
      fullKernelMoment (radialKernelParameters parameters r) q (retainedBInverseKernel (radialKernelParameters parameters r)) ≤ fixed q :=
    (sameScalarModeDiagonalKernel _ _ _ retainedBInverseMultiplier _ retainedBInverseMultiplier_norm_le).radialMoment_le parameters r q
  let constant := 2 ^ moment *
    (fullKernelNeumannConstant moment (1 / 2) * highConstant * fixed 0 +
      fullKernelNeumannConstant 0 (1 / 2) * baseConstant * fixed moment)
  refine ⟨constant, mul_nonneg (by positivity) (add_nonneg
    (mul_nonneg (mul_nonneg (neumannNonnegative moment) highNonnegative) (fixedNonnegative 0))
    (mul_nonneg (mul_nonneg (neumannNonnegative 0) baseNonnegative) (fixedNonnegative moment))), ?_⟩
  intro state r
  let tail := fullKernelNeumannTail (radialKernelParameters parameters r)
    (radialRetainedPreconditionKernel parameters L compact state.val r) (1 / 2)
    (radialRetainedPreconditionKernel_small parameters L compact state r) (by norm_num)
  have tailHigh : fullKernelMoment (radialKernelParameters parameters r) moment tail ≤
      fullKernelNeumannConstant moment (1 / 2) * highConstant * state.val.errorBudget moment := by
    apply (fullKernelNeumannTail_moment_le _ moment _ (1 / 2)
      (radialRetainedPreconditionKernel_small parameters L compact state r) (by norm_num)).trans
    exact (mul_le_mul_of_nonneg_left (highBound state.val r) (neumannNonnegative moment)).trans_eq (mul_assoc _ _ _).symm
  have tailBase : fullKernelMoment (radialKernelParameters parameters r) 0 tail ≤
      fullKernelNeumannConstant 0 (1 / 2) * baseConstant * state.val.errorBudget moment := by
    apply (fullKernelNeumannTail_moment_le _ 0 _ (1 / 2)
      (radialRetainedPreconditionKernel_small parameters L compact state r) (by norm_num)).trans
    have budget : state.val.errorBudget 0 ≤ state.val.errorBudget moment :=
      physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon (by omega)
    have bound := (baseBound state.val r).trans (mul_le_mul_of_nonneg_left budget baseNonnegative)
    exact (mul_le_mul_of_nonneg_left bound (neumannNonnegative 0)).trans_eq (mul_assoc _ _ _).symm
  change fullKernelMoment _ moment (fullKernelAdd (radialRetainedHighInverse parameters L compact state r)
    (retainedBInverseKernel (radialKernelParameters parameters r))) ≤ constant * state.val.errorBudget moment
  rw [radialRetainedHighInverse_reference_tail]
  apply (fullKernelNeg_moment_le _ moment _).trans
  apply (fullKernelComposition_moment_le moment tail (retainedBInverseKernel (radialKernelParameters parameters r))).trans
  have budgetNonnegative := physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon (moment + 7)
  have first := mul_le_mul tailHigh (fixedBound r 0) (fullKernelMoment_nonnegative _ _ _)
    (mul_nonneg (mul_nonneg (neumannNonnegative moment) highNonnegative) budgetNonnegative)
  have second := mul_le_mul tailBase (fixedBound r moment) (fullKernelMoment_nonnegative _ _ _)
    (mul_nonneg (mul_nonneg (neumannNonnegative 0) baseNonnegative) budgetNonnegative)
  exact (mul_le_mul_of_nonneg_left (add_le_add first second) (by positivity : 0 ≤ (2 : ℝ) ^ moment)).trans_eq (by dsimp [constant]; ring)

/-- The actual inverse itself has the corresponding one-high physical moments. -/
theorem radialRetainedHighInverse_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    UniformRadialKernelMoments parameters (fun state : RetainedInverseState parameters L compact => state.val.val.size)
      (radialRetainedHighInverse parameters L compact) := by
  intro moment
  obtain ⟨errorConstant, errorNonnegative, errorBound⟩ := radialRetainedHighInverse_referenceMoments parameters L compact moment
  let fixed := fullKernelMoment (maximalKernelParameters parameters) moment
    (retainedBInverseKernel (maximalKernelParameters parameters))
  have fixedNonnegative : 0 ≤ fixed := fullKernelMoment_nonnegative _ _ _
  refine ⟨errorConstant + fixed, add_nonneg errorNonnegative fixedNonnegative, ?_⟩
  intro state r
  have identity : radialRetainedHighInverse parameters L compact state r =
      fullKernelSub (fullKernelAdd (radialRetainedHighInverse parameters L compact state r)
        (retainedBInverseKernel (radialKernelParameters parameters r)))
        (retainedBInverseKernel (radialKernelParameters parameters r)) := by
    apply FullTwoFrequencyKernel.ext_entry
    intro shift mode
    simp only [fullKernelSub, fullKernelAdd_entry, fullKernelNeg_entry]
    abel
  rw [identity]
  apply (fullKernelAdd_moment_le _ moment _ _).trans
  have fixedBound : fullKernelMoment (radialKernelParameters parameters r) moment
      (retainedBInverseKernel (radialKernelParameters parameters r)) ≤ fixed :=
    (sameScalarModeDiagonalKernel _ _ _ retainedBInverseMultiplier _ retainedBInverseMultiplier_norm_le).radialMoment_le parameters r moment
  have second := (fullKernelNeg_moment_le (radialKernelParameters parameters r) moment _).trans fixedBound
  apply (add_le_add (errorBound state r) second).trans
  have budgetNonnegative := physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon (moment + 7)
  change errorConstant * state.val.errorBudget moment + fixed ≤ (errorConstant + fixed) * (1 + state.val.errorBudget moment)
  nlinarith

end Grad.AnnularReconstruction
