import BCI6ActualBoundaryBlocks

noncomputable section
set_option maxHeartbeats 1000000
namespace Grad.ActualBoundaryInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation

def boundaryCorrectionBaseConstant (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  boundaryDeviationMultiplierConstant parameters L compact 1 * actualUnknownUBaseConstant parameters L compact +
    boundaryDeviationMultiplierConstant parameters L compact 0 * actualUnknownVBaseConstant parameters L compact

theorem boundaryCorrectionBaseConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) :
    0 ≤ boundaryCorrectionBaseConstant parameters L compact :=
  add_nonneg (mul_nonneg (boundaryDeviationMultiplierConstant_nonnegative parameters L compact 1)
    (actualUnknownUBaseConstant_nonnegative parameters L compact))
    (mul_nonneg (boundaryDeviationMultiplierConstant_nonnegative parameters L compact 0)
      (actualUnknownVBaseConstant_nonnegative parameters L compact))

def boundaryMassInverseBaseConstant (parameters : PhaseParameters) : ℝ :=
  fullKernelMoment parameters 0 (fullIdentityKernel parameters 1) + |fullKernelNeumannConstant 0 (1 / 2)| * (1 / 2)

theorem boundaryMassInverseBaseConstant_nonnegative (parameters : PhaseParameters) :
    0 ≤ boundaryMassInverseBaseConstant parameters :=
  add_nonneg (fullKernelMoment_nonnegative parameters 0 _) (mul_nonneg (abs_nonneg _) (by norm_num))

variable {parameters : PhaseParameters} {L compact : ℝ}

 theorem boundary_delta_base (state : PhysicalBoundaryState parameters L compact) :
    fullKernelMoment parameters 0 state.deltaRow ≤ boundaryDeviationMultiplierConstant parameters L compact 0 * state.budget 0 := by
  apply (boundaryDeviationMultiplier_moment parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall
    state.val.parameterSmall state.coefficientSmall 0).trans
  exact mul_le_mul_of_nonneg_left (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (by omega))
    (boundaryDeviationMultiplierConstant_nonnegative parameters L compact 0)

theorem boundary_rotated_delta_base (state : PhysicalBoundaryState parameters L compact) :
    fullKernelMoment parameters 0 state.rotatedDeltaRow ≤ boundaryDeviationMultiplierConstant parameters L compact 1 * state.budget 0 := by
  apply (boundaryRotatedDeviationMultiplier_moment parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall
    state.val.parameterSmall state.coefficientSmall 0).trans
  exact mul_le_mul_of_nonneg_left (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (by omega))
    (boundaryDeviationMultiplierConstant_nonnegative parameters L compact 1)

theorem boundary_correction_base (state : PhysicalBoundaryState parameters L compact) :
    fullKernelMoment parameters 0 state.rowCorrection ≤ boundaryCorrectionBaseConstant parameters L compact * state.budget 0 := by
  have uv := actualUnknownUVKernel_moment_zero_le parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.firstSmall state.val.compactNonnegative state.val.alphaSmall
    state.val.deltaSmall state.val.parameterSmall
  have first := fullKernelComposition_zero_moment_le_of state.rotatedDeltaRow state.unknownU _ _
    (boundary_rotated_delta_base state) uv.1
    (mul_nonneg (boundaryDeviationMultiplierConstant_nonnegative parameters L compact 1)
      (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon 7))
    (actualUnknownUBaseConstant_nonnegative parameters L compact)
  have second := fullKernelComposition_zero_moment_le_of state.deltaRow state.unknownV _ _
    (boundary_delta_base state) uv.2
    (mul_nonneg (boundaryDeviationMultiplierConstant_nonnegative parameters L compact 0)
      (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon 7))
    (actualUnknownVBaseConstant_nonnegative parameters L compact)
  exact (fullKernelAdd_zero_moment_le_of _ _ _ _ first second).trans_eq (by
    unfold boundaryCorrectionBaseConstant; ring)

theorem boundary_mass_inverse_base (state : PhysicalBoundaryState parameters L compact) :
    fullKernelMoment parameters 0 state.massInverse ≤ boundaryMassInverseBaseConstant parameters := by
  have small := actualMassPerturbationKernel_moment_zero_le_half parameters L state.val.rho state.val.alpha state.val.delta
    state.val.parameter state.val.epsilon compact state.val.field state.val.small state.val.compactNonnegative
    state.val.alphaSmall state.val.deltaSmall state.val.parameterSmall
  have raw := fullKernelNegativeIdentityInverse_moment_le parameters 0 state.massPerturbation (1 / 2) small (by norm_num)
  apply raw.trans
  unfold boundaryMassInverseBaseConstant
  apply add_le_add le_rfl
  apply (mul_le_mul_of_nonneg_right (le_abs_self _) (fullKernelMoment_nonnegative parameters 0 state.massPerturbation)).trans
  exact mul_le_mul_of_nonneg_left small (abs_nonneg _)

def boundaryInverseBaseConstant (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  fullKernelMoment parameters 0 (highAngularKernel parameters 1) *
    ((actualMassBaseConstant parameters L compact + boundaryCorrectionBaseConstant parameters L compact) *
      boundaryMassInverseBaseConstant parameters) * fullKernelMoment parameters 0 (highAngularKernel parameters 1)

theorem boundaryInverseBaseConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) :
    0 ≤ boundaryInverseBaseConstant parameters L compact :=
  mul_nonneg (mul_nonneg (fullKernelMoment_nonnegative parameters 0 _)
    (mul_nonneg (add_nonneg (actualMassBaseConstant_nonnegative parameters L compact)
      (boundaryCorrectionBaseConstant_nonnegative parameters L compact))
      (boundaryMassInverseBaseConstant_nonnegative parameters))) (fullKernelMoment_nonnegative parameters 0 _)

theorem boundary_E_base (state : PhysicalBoundaryState parameters L compact) :
    fullKernelMoment parameters 0 state.boundaryE ≤ boundaryInverseBaseConstant parameters L compact * state.budget 0 := by
  have mass := actualMassPerturbationKernel_moment_zero_le parameters L state.val.rho state.val.alpha state.val.delta
    state.val.parameter state.val.epsilon compact state.val.field state.val.small state.val.compactNonnegative
    state.val.alphaSmall state.val.deltaSmall state.val.parameterSmall
  have added := fullKernelAdd_zero_moment_le_of state.massPerturbation state.rowCorrection _ _ mass (boundary_correction_base state)
  have inner := fullKernelComposition_zero_moment_le_of _ state.massInverse _ _ added (boundary_mass_inverse_base state)
    (add_nonneg (mul_nonneg (actualMassBaseConstant_nonnegative parameters L compact)
      (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon 7))
      (mul_nonneg (boundaryCorrectionBaseConstant_nonnegative parameters L compact)
        (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon 7)))
    (boundaryMassInverseBaseConstant_nonnegative parameters)
  have innerBoundNonnegative := (fullKernelMoment_nonnegative parameters 0 _).trans inner
  have right := fullKernelComposition_zero_moment_le_of _ (highAngularKernel parameters 1) _ _ inner le_rfl
    innerBoundNonnegative (fullKernelMoment_nonnegative parameters 0 _)
  have both := fullKernelComposition_zero_moment_le_of (highAngularKernel parameters 1) _ _ _ le_rfl right
    (fullKernelMoment_nonnegative parameters 0 _) ((fullKernelMoment_nonnegative parameters 0 _).trans right)
  exact both.trans_eq (by unfold boundaryInverseBaseConstant; ring)

/-- One original B7 neighborhood, independent of every running grade. -/
def boundaryInverseLowRadius (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  min (physicalBoundaryLowRadius parameters L compact) (4 * (boundaryInverseBaseConstant parameters L compact + 1))⁻¹

theorem boundaryInverseLowRadius_positive (parameters : PhaseParameters) (L compact : ℝ) :
    0 < boundaryInverseLowRadius parameters L compact :=
  lt_min (physicalBoundaryLowRadius_positive parameters L compact)
    (inv_pos.mpr (by linarith [boundaryInverseBaseConstant_nonnegative parameters L compact]))

theorem boundary_E_le_quarter (state : PhysicalBoundaryState parameters L compact)
    (small : state.budget 0 ≤ boundaryInverseLowRadius parameters L compact) :
    fullKernelMoment parameters 0 state.boundaryE ≤ 1 / 4 := by
  apply (boundary_E_base state).trans
  apply (mul_le_mul_of_nonneg_left (small.trans (min_le_right _ _))
    (boundaryInverseBaseConstant_nonnegative parameters L compact)).trans
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (by linarith [boundaryInverseBaseConstant_nonnegative parameters L compact] :
    0 < 4 * (boundaryInverseBaseConstant parameters L compact + 1))).mpr
  nlinarith [boundaryInverseBaseConstant_nonnegative parameters L compact]

end Grad.ActualBoundaryInverse
