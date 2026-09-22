import AHV6ActualRetainedInverseBall

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.CircularHighWeak
open Grad.ActualReferenceAssembly Grad.Constraints

theorem scalarModeDiagonalKernel_high_left (parameters : PhaseParameters)
    (symbol : (ℤ × ℤ) → ℂ) (bound : ℝ) (bounded : ∀ mode, ‖symbol mode‖ ≤ bound)
    (supported : ∀ mode, highAngularMultiplier mode * symbol mode = symbol mode) :
    fullKernelComposition (highAngularKernel parameters 1)
      (scalarModeDiagonalKernel parameters 1 symbol bound bounded) =
      scalarModeDiagonalKernel parameters 1 symbol bound bounded := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift mode
  rw [highAngularKernel, scalarModeDiagonalKernel_comp_entry]
  by_cases zero : shift = (0, 0)
  · subst shift
    simp only [scalarModeDiagonalKernel, modeDiagonalKernel_entry, if_pos,
      show mode + (0, 0) = mode from add_zero mode, smul_smul, supported]
  · simp only [scalarModeDiagonalKernel, modeDiagonalKernel_entry, if_neg zero]
    apply ContinuousLinearMap.ext
    intro value
    simp only [smul_apply, zero_apply, smul_zero]

theorem scalarModeDiagonalKernel_high_right (parameters : PhaseParameters)
    (symbol : (ℤ × ℤ) → ℂ) (bound : ℝ) (bounded : ∀ mode, ‖symbol mode‖ ≤ bound)
    (supported : ∀ mode, highAngularMultiplier mode * symbol mode = symbol mode) :
    fullKernelComposition (scalarModeDiagonalKernel parameters 1 symbol bound bounded)
      (highAngularKernel parameters 1) =
      scalarModeDiagonalKernel parameters 1 symbol bound bounded := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift mode
  rw [scalarModeDiagonalKernel_comp_entry]
  by_cases zero : shift = (0, 0)
  · subst shift
    simp only [highAngularKernel, scalarModeDiagonalKernel, modeDiagonalKernel_entry, if_pos,
      show mode + (0, 0) = mode from add_zero mode, smul_smul]
    rw [mul_comm, supported]
  · simp only [highAngularKernel, scalarModeDiagonalKernel, modeDiagonalKernel_entry, if_neg zero]
    apply ContinuousLinearMap.ext
    intro value
    simp only [smul_apply, zero_apply, smul_zero]

theorem retainedBMultiplier_high (mode : ℤ × ℤ) :
    highAngularMultiplier mode * retainedBMultiplier mode = retainedBMultiplier mode := by
  by_cases high : 3 ≤ |mode.1|
  · simp [highAngularMultiplier, high]
  · simp [highAngularMultiplier, high, retainedBMultiplier, highMultiplier, not_highMode_low mode.1 high]

theorem retainedBInverseMultiplier_high (mode : ℤ × ℤ) :
    highAngularMultiplier mode * retainedBInverseMultiplier mode = retainedBInverseMultiplier mode := by
  by_cases high : 3 ≤ |mode.1|
  · simp [highAngularMultiplier, high]
  · simp [highAngularMultiplier, high, retainedBInverseMultiplier, retainedBMultiplier,
      highMultiplier, not_highMode_low mode.1 high]

theorem retainedBKernel_high_left (parameters : PhaseParameters) :
    fullKernelComposition (highAngularKernel parameters 1) (retainedBKernel parameters) = retainedBKernel parameters :=
  scalarModeDiagonalKernel_high_left _ _ _ _ retainedBMultiplier_high

theorem retainedBKernel_high_right (parameters : PhaseParameters) :
    fullKernelComposition (retainedBKernel parameters) (highAngularKernel parameters 1) = retainedBKernel parameters :=
  scalarModeDiagonalKernel_high_right _ _ _ _ retainedBMultiplier_high

theorem retainedBInverseKernel_high_left (parameters : PhaseParameters) :
    fullKernelComposition (highAngularKernel parameters 1) (retainedBInverseKernel parameters) = retainedBInverseKernel parameters :=
  scalarModeDiagonalKernel_high_left _ _ _ _ retainedBInverseMultiplier_high

theorem retainedBInverseKernel_high_right (parameters : PhaseParameters) :
    fullKernelComposition (retainedBInverseKernel parameters) (highAngularKernel parameters 1) = retainedBInverseKernel parameters :=
  scalarModeDiagonalKernel_high_right _ _ _ _ retainedBInverseMultiplier_high

theorem radialRetainedHighErrorKernel_high_left (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (r : RadialPoint) :
    fullKernelComposition (highAngularKernel (radialKernelParameters parameters r) 1)
      (radialRetainedHighErrorKernel parameters L compact state r) = radialRetainedHighErrorKernel parameters L compact state r := by
  simp only [radialRetainedHighErrorKernel, circularRetainedAKernel, fullKernelSub,
    fullKernelComposition_add_inner, fullKernelComposition_neg_inner,
    radialRetainedHighAKernel_high_left, retainedBKernel_high_left]

theorem radialRetainedHighErrorKernel_high_right (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (r : RadialPoint) :
    fullKernelComposition (radialRetainedHighErrorKernel parameters L compact state r)
      (highAngularKernel (radialKernelParameters parameters r) 1) = radialRetainedHighErrorKernel parameters L compact state r := by
  simp only [radialRetainedHighErrorKernel, circularRetainedAKernel, fullKernelSub,
    fullKernelComposition_add_outer, fullKernelComposition_neg_outer,
    radialRetainedHighAKernel_high_right, retainedBKernel_high_right]

/-- The preconditioned ambient equation is B^{-1} A = (-I+F) Q. -/
theorem retained_preconditioned_equation (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (r : RadialPoint) :
    fullKernelComposition (retainedBInverseKernel (radialKernelParameters parameters r))
      (radialRetainedHighAKernel parameters L compact state r) =
    fullKernelComposition
      (fullKernelNegativeIdentityPerturbation (radialKernelParameters parameters r)
        (radialRetainedPreconditionKernel parameters L compact state r))
      (highAngularKernel (radialKernelParameters parameters r) 1) := by
  simp only [fullKernelNegativeIdentityPerturbation, fullKernelSub, fullKernelComposition_add_outer,
    fullKernelComposition_neg_outer, fullIdentityKernel_comp, radialRetainedPreconditionKernel,
    fullKernelComposition_assoc, radialRetainedHighErrorKernel_high_right]
  simp only [radialRetainedHighErrorKernel, fullKernelSub, circularRetainedAKernel,
    fullKernelComposition_add_inner, fullKernelComposition_neg_inner, retainedBKernel_inverse_left]
  apply FullTwoFrequencyKernel.ext_entry
  intro shift mode
  simp only [fullKernelAdd_entry, fullKernelNeg_entry]
  abel

/-- The actual retained A factors as B(-I+F), with its original negative reference. -/
theorem retained_factorization (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (r : RadialPoint) :
    radialRetainedHighAKernel parameters L compact state r =
      fullKernelComposition (retainedBKernel (radialKernelParameters parameters r))
        (fullKernelNegativeIdentityPerturbation (radialKernelParameters parameters r)
          (radialRetainedPreconditionKernel parameters L compact state r)) := by
  simp only [fullKernelNegativeIdentityPerturbation, fullKernelSub, fullKernelComposition_add_inner,
    fullKernelComposition_neg_inner, fullKernel_comp_identity, radialRetainedPreconditionKernel]
  rw [← fullKernelComposition_assoc, retainedBKernel_inverse_right, radialRetainedHighErrorKernel_high_left]
  apply FullTwoFrequencyKernel.ext_entry
  intro shift mode
  simp only [radialRetainedHighErrorKernel, fullKernelSub, circularRetainedAKernel,
    fullKernelAdd_entry, fullKernelNeg_entry]
  abel

/-- Left inverse on exactly the retained high input. -/
theorem radialRetainedHighInverse_left (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) :
    fullKernelComposition (radialRetainedHighInverse parameters L compact state r)
      (radialRetainedHighAKernel parameters L compact state.val r) = highAngularKernel (radialKernelParameters parameters r) 1 := by
  unfold radialRetainedHighInverse
  rw [fullKernelComposition_assoc, retained_preconditioned_equation, ← fullKernelComposition_assoc,
    radialRetainedAmbientInverse_left, fullIdentityKernel_comp]

/-- Right inverse on exactly the retained high output. -/
theorem radialRetainedHighInverse_right (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) :
    fullKernelComposition (radialRetainedHighAKernel parameters L compact state.val r)
      (radialRetainedHighInverse parameters L compact state r) = highAngularKernel (radialKernelParameters parameters r) 1 := by
  rw [retained_factorization]
  unfold radialRetainedHighInverse
  rw [fullKernelComposition_assoc, ← fullKernelComposition_assoc _ (radialRetainedAmbientInverse parameters L compact state r),
    radialRetainedAmbientInverse_right, fullIdentityKernel_comp, retainedBKernel_inverse_right]

theorem radialRetainedHighInverse_high_right (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) :
    fullKernelComposition (radialRetainedHighInverse parameters L compact state r)
      (highAngularKernel (radialKernelParameters parameters r) 1) = radialRetainedHighInverse parameters L compact state r := by
  unfold radialRetainedHighInverse
  rw [fullKernelComposition_assoc, retainedBInverseKernel_high_right]

theorem radialRetainedHighInverse_high_left (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) :
    fullKernelComposition (highAngularKernel (radialKernelParameters parameters r) 1)
      (radialRetainedHighInverse parameters L compact state r) = radialRetainedHighInverse parameters L compact state r := by
  rw [← radialRetainedHighInverse_left parameters L compact state r, fullKernelComposition_assoc,
    radialRetainedHighInverse_right, radialRetainedHighInverse_high_right]

end Grad.AnnularReconstruction
