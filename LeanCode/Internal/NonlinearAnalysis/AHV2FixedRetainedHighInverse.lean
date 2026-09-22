import AHV1ActualRetainedForceError

noncomputable section
set_option maxHeartbeats 1200000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.CircularHighWeak
open Grad.ActualReferenceAssembly Grad.Constraints

/-- The accepted literal b_m, zero on the excluded five angular modes. -/
def retainedBMultiplier (mode : ℤ × ℤ) : ℂ := highMultiplier mode.1

def retainedBInverseMultiplier (mode : ℤ × ℤ) : ℂ := (retainedBMultiplier mode)⁻¹

theorem retainedBMultiplier_norm_le (mode : ℤ × ℤ) : ‖retainedBMultiplier mode‖ ≤ 1 := by
  rw [retainedBMultiplier, Complex.norm_real, Real.norm_of_nonneg (highMultiplier_nonnegative _)]
  exact highMultiplier_one_le _

theorem retainedBInverseMultiplier_norm_le (mode : ℤ × ℤ) : ‖retainedBInverseMultiplier mode‖ ≤ 9 / 5 := by
  by_cases low : mode.1 ∈ lowAngularModes
  · norm_num [retainedBInverseMultiplier, retainedBMultiplier, highMultiplier, low]
  · have bound := (highMultiplier_bounds mode.1 low).1
    have positive : 0 < highMultiplier mode.1 := by linarith
    rw [retainedBInverseMultiplier, norm_inv, retainedBMultiplier, Complex.norm_real,
      Real.norm_of_nonneg positive.le]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ positive).2
    linarith

def retainedBKernel (parameters : PhaseParameters) : FullTwoFrequencyKernel parameters 1 1 :=
  scalarModeDiagonalKernel parameters 1 retainedBMultiplier 1 retainedBMultiplier_norm_le

def retainedBInverseKernel (parameters : PhaseParameters) : FullTwoFrequencyKernel parameters 1 1 :=
  scalarModeDiagonalKernel parameters 1 retainedBInverseMultiplier (9 / 5) retainedBInverseMultiplier_norm_le

/-- A's actual circular sign is minus b_m. -/
def circularRetainedAKernel (parameters : PhaseParameters) : FullTwoFrequencyKernel parameters 1 1 :=
  fullKernelNeg (retainedBKernel parameters)

theorem retainedBMultiplier_mul_inverse (mode : ℤ × ℤ) :
    retainedBMultiplier mode * retainedBInverseMultiplier mode = highAngularMultiplier mode := by
  by_cases high : 3 ≤ |mode.1|
  · have bound := (highMultiplier_bounds mode.1 (highMode_not_low mode.1 high)).1
    have nonzero : retainedBMultiplier mode ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      linarith
    simp [retainedBInverseMultiplier, highAngularMultiplier, high, nonzero]
  · simp [retainedBMultiplier, retainedBInverseMultiplier, highAngularMultiplier, high,
      highMultiplier, not_highMode_low mode.1 high]

theorem retainedBInverseMultiplier_mul (mode : ℤ × ℤ) :
    retainedBInverseMultiplier mode * retainedBMultiplier mode = highAngularMultiplier mode := by
  rw [mul_comm, retainedBMultiplier_mul_inverse]

theorem retainedBKernel_inverse_right (parameters : PhaseParameters) :
    fullKernelComposition (retainedBKernel parameters) (retainedBInverseKernel parameters) =
      highAngularKernel parameters 1 := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift mode
  rw [retainedBKernel, scalarModeDiagonalKernel_comp_entry]
  by_cases zero : shift = (0, 0)
  · subst shift
    simp only [retainedBInverseKernel, highAngularKernel, scalarModeDiagonalKernel, modeDiagonalKernel_entry,
      if_pos, show mode + (0, 0) = mode from add_zero mode, smul_smul, retainedBMultiplier_mul_inverse]
  · simp only [retainedBInverseKernel, highAngularKernel, scalarModeDiagonalKernel, modeDiagonalKernel_entry, if_neg zero]
    apply ContinuousLinearMap.ext
    intro value
    simp only [smul_apply, zero_apply, smul_zero]

theorem retainedBKernel_inverse_left (parameters : PhaseParameters) :
    fullKernelComposition (retainedBInverseKernel parameters) (retainedBKernel parameters) =
      highAngularKernel parameters 1 := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift mode
  rw [retainedBInverseKernel, scalarModeDiagonalKernel_comp_entry]
  by_cases zero : shift = (0, 0)
  · subst shift
    simp only [retainedBKernel, highAngularKernel, scalarModeDiagonalKernel, modeDiagonalKernel_entry,
      if_pos, show mode + (0, 0) = mode from add_zero mode, smul_smul, retainedBInverseMultiplier_mul]
  · simp only [retainedBKernel, highAngularKernel, scalarModeDiagonalKernel, modeDiagonalKernel_entry, if_neg zero]
    apply ContinuousLinearMap.ext
    intro value
    simp only [smul_apply, zero_apply, smul_zero]

theorem retainedBKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => retainedBKernel (radialKernelParameters parameters r)) :=
  RadialPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameScalarModeDiagonalKernel _ _ _ _ _ _)

theorem retainedBInverseKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => retainedBInverseKernel (radialKernelParameters parameters r)) :=
  RadialPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameScalarModeDiagonalKernel _ _ _ _ _ _)

end Grad.AnnularReconstruction
