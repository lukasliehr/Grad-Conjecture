import AHV3NormalizedRetainedHighError

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.CircularHighWeak Grad.ActualReferenceAssembly
open Grad.GaugeCoefficients.Physical.Ledger

/-- Internal support property for the exact circular multiplier recipes. -/
def ZeroShiftKernel {parameters : PhaseParameters} {input output : ℕ}
    (kernel : FullTwoFrequencyKernel parameters input output) : Prop :=
  ∀ shift, shift ≠ (0, 0) → ∀ mode, kernel.entry shift mode = 0

@[simp] theorem zeroShift_modeDiagonal (parameters : PhaseParameters) (input output : ℕ)
    (mapping : (ℤ × ℤ) → (ComplexEuclidean input →L[ℂ] ComplexEuclidean output))
    (bound : ℝ) (bounded : ∀ mode, ‖mapping mode‖ ≤ bound) :
    ZeroShiftKernel (modeDiagonalKernel parameters input output mapping bound bounded) := by
  intro shift nonzero mode
  simp [nonzero]

@[simp] theorem ZeroShiftKernel.add {parameters : PhaseParameters} {input output : ℕ}
    {first second : FullTwoFrequencyKernel parameters input output}
    (one : ZeroShiftKernel first) (two : ZeroShiftKernel second) : ZeroShiftKernel (fullKernelAdd first second) := by
  intro shift nonzero mode
  simp [one shift nonzero mode, two shift nonzero mode]

@[simp] theorem ZeroShiftKernel.neg {parameters : PhaseParameters} {input output : ℕ}
    {kernel : FullTwoFrequencyKernel parameters input output}
    (diagonal : ZeroShiftKernel kernel) : ZeroShiftKernel (fullKernelNeg kernel) := by
  intro shift nonzero mode
  simp [diagonal shift nonzero mode]

@[simp] theorem ZeroShiftKernel.smul {parameters : PhaseParameters} {input output : ℕ}
    {kernel : FullTwoFrequencyKernel parameters input output} (scalar : ℂ)
    (diagonal : ZeroShiftKernel kernel) : ZeroShiftKernel (fullKernelSmul scalar kernel) := by
  intro shift nonzero mode
  rw [fullKernelSmul_entry, diagonal shift nonzero mode]
  apply ContinuousLinearMap.ext
  intro value
  simp only [smul_apply, zero_apply, smul_zero]

@[simp] theorem zeroShift_identity (parameters : PhaseParameters) (dimension : ℕ) :
    ZeroShiftKernel (fullIdentityKernel parameters dimension) := by
  intro shift nonzero mode
  exact fullIdentityKernel_entry_ne_zero parameters dimension shift mode nonzero

/-- Exact convolution collapse, retaining the Fourier input of the right factor. -/
theorem kernelComposition_entry_diagonal_inner {parameters : PhaseParameters} {input middle output : ℕ}
    (outer : FullTwoFrequencyKernel parameters middle output)
    (inner : FullTwoFrequencyKernel parameters input middle) (diagonal : ZeroShiftKernel inner)
    (shift mode : ℤ × ℤ) :
    (fullKernelComposition outer inner).entry shift mode =
      (outer.entry shift mode).comp (inner.entry (0, 0) mode) := by
  rw [fullKernelComposition_entry, tsum_eq_single (0, 0) (by
    intro displacement nonzero
    rw [diagonal displacement nonzero mode]
    exact ContinuousLinearMap.comp_zero _)]
  rw [show shift - (0, 0) = shift from sub_zero shift,
    show mode + (0, 0) = mode from add_zero mode]

@[simp] theorem ZeroShiftKernel.comp {parameters : PhaseParameters} {input middle output : ℕ}
    {outer : FullTwoFrequencyKernel parameters middle output}
    {inner : FullTwoFrequencyKernel parameters input middle}
    (one : ZeroShiftKernel outer) (two : ZeroShiftKernel inner) : ZeroShiftKernel (fullKernelComposition outer inner) := by
  intro shift nonzero mode
  rw [kernelComposition_entry_diagonal_inner _ _ two, one shift nonzero mode]
  exact ContinuousLinearMap.zero_comp _

theorem retainedCircleMultiplier_formula (mode : ℤ × ℤ) :
    highAngularMultiplier mode * (-1 - 4 * angularDoubleInverseMultiplier mode) * highAngularMultiplier mode =
      -retainedBMultiplier mode := by
  by_cases high : 3 ≤ |mode.1|
  · have nonzero : mode.1 ≠ 0 := by intro zero; simp [zero] at high
    have square : angularDoubleInverseMultiplier mode = -((mode.1 : ℂ) ^ 2)⁻¹ := by
      rw [angularDoubleInverseMultiplier, angularInverseMultiplier, if_neg nonzero]
      calc
        _ = ((Complex.I * (mode.1 : ℂ)) * (Complex.I * (mode.1 : ℂ)))⁻¹ := by simp only [mul_inv_rev]
        _ = _ := by rw [← pow_two, mul_pow, Complex.I_sq]; simp
    rw [retainedBMultiplier, highMultiplier_complex mode.1 high]
    simp only [highAngularMultiplier, if_pos high, one_mul, mul_one, square, div_eq_mul_inv]
    ring
  · simp [highAngularMultiplier, high, retainedBMultiplier, highMultiplier, not_highMode_low mode.1 high]

/-- The stored circular recipe, including its scalar mass minus sign,
is exactly minus the accepted b_m multiplier on the retained sector. -/
theorem circularRetainedARecipe_eq (parameters : PhaseParameters) (L : ℝ) :
    circularRetainedARecipe parameters L = circularRetainedAKernel parameters := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift mode
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro component
  have unique := Fin.eq_zero component
  subst component
  by_cases zero : shift = (0, 0)
  · subst shift
    simp (config := { maxDischargeDepth := 100 }) only [circularRetainedARecipe, circularRetainedFirstRowKernel, circularRetainedForceKernel,
      circularNormalizedCovariantKernel, circularNormalizedRotatedCovariantKernel,
      circularUnknownUKernel, circularUnknownVKernel, circularRecoveredMassKernel,
      circularKnownAStarKernel, circularKnownRAStarKernel, circularKnownWKernel, circularUnknownWKernel,
      circularKnownEncodedDataKernel, circularUnknownNKernel,
      encodedJKernel, encodedRotationKernel, angularMeanComponentKernel, angularDoubleInverseComponentKernel,
      angularInverseComponentKernel, angularMeanFreeComponentKernel, componentModeKernel,
      actualUnknownQAKernel, angularMeanKernel, angularInverseKernel,
      firstCoordinateInjectionKernel, secondCoordinateInjectionKernel, thirdCoordinateInjectionKernel,
      coordinateProjectionKernel, coordinateInjectionKernel, sevenInputSlotKernel, encodedD0InverseKernel,
      highAngularKernel, circularRetainedAKernel, retainedBKernel, constantMatrixKernel,
      scalarModeDiagonalKernel, kernelComposition_entry_diagonal_inner, fullKernelSub,
      ZeroShiftKernel.comp, ZeroShiftKernel.add, ZeroShiftKernel.neg, ZeroShiftKernel.smul,
      zeroShift_identity, zeroShift_modeDiagonal, fullKernelAdd_entry, fullKernelNeg_entry,
      fullKernelSmul_entry, modeDiagonalKernel_entry, fullIdentityKernel_entry_zero]
    simp only [ContinuousLinearMap.comp_apply, add_apply, neg_apply, smul_apply, ContinuousLinearMap.id_apply,
      PiLp.neg_apply]
    simp [diagonalThreeMap, matrixUnit_apply, operatorBasis]
    have formula := congrArg (fun scalar : ℂ => scalar * value 0) (retainedCircleMultiplier_formula mode)
    linear_combination formula
  · simp (config := { maxDischargeDepth := 100 }) only [circularRetainedARecipe, circularRetainedFirstRowKernel, circularRetainedForceKernel,
      circularNormalizedCovariantKernel, circularNormalizedRotatedCovariantKernel,
      circularUnknownUKernel, circularUnknownVKernel, circularRecoveredMassKernel,
      circularKnownAStarKernel, circularKnownRAStarKernel, circularKnownWKernel, circularUnknownWKernel,
      circularKnownEncodedDataKernel, circularUnknownNKernel,
      encodedJKernel, encodedRotationKernel, angularMeanComponentKernel, angularDoubleInverseComponentKernel,
      angularInverseComponentKernel, angularMeanFreeComponentKernel, componentModeKernel,
      actualUnknownQAKernel, angularMeanKernel, angularInverseKernel,
      firstCoordinateInjectionKernel, secondCoordinateInjectionKernel, thirdCoordinateInjectionKernel,
      coordinateProjectionKernel, coordinateInjectionKernel, sevenInputSlotKernel, encodedD0InverseKernel,
      highAngularKernel, circularRetainedAKernel, retainedBKernel, constantMatrixKernel,
      scalarModeDiagonalKernel, kernelComposition_entry_diagonal_inner, fullKernelSub,
      ZeroShiftKernel.comp, ZeroShiftKernel.add, ZeroShiftKernel.neg, ZeroShiftKernel.smul,
      zeroShift_identity, zeroShift_modeDiagonal, fullKernelAdd_entry, fullKernelNeg_entry,
      fullKernelSmul_entry, modeDiagonalKernel_entry, fullIdentityKernel_entry_zero, if_neg zero]
    simp only [ContinuousLinearMap.comp_apply, add_apply, neg_apply, smul_apply, ContinuousLinearMap.id_apply, zero_apply, neg_zero]

end Grad.AnnularReconstruction
