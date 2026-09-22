import AEM8ActualLowOuterTraceMaps

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.BoundaryKernelAction Grad.PhaseAlgebra Grad.BoundaryTrace

 theorem boundaryPhase_at_outer (parameters : PhaseParameters) (cell : ℤ) :
    boundaryPhase parameters cell = radialPhase parameters 1 cell := by
  unfold boundaryPhase radialPhase
  simp only [one_pow, mul_one]

theorem positiveTraceWeight_base (parameters : PhaseParameters) (mode : ℤ × ℤ) :
    positiveTraceWeight parameters 0 0 mode =
      Real.exp (radialPhase parameters 1 mode.2) * Real.sqrt (Grad.AnnularVariational.annularFrequency mode.1 mode.2) := by
  have exponential : Real.exp (2 * boundaryPhase parameters mode.2) =
      (Real.exp (boundaryPhase parameters mode.2)) ^ 2 := by
    rw [two_mul, Real.exp_add, pow_two]
  unfold positiveTraceWeight positiveTraceWeightSq
  simp only [mul_zero, pow_zero, mul_one]
  rw [Real.sqrt_mul (Real.exp_pos _).le, exponential, Real.sqrt_sq_eq_abs,
    abs_of_pos (Real.exp_pos _), boundaryPhase_at_outer]
  rfl

theorem negativeTraceWeight_base (parameters : PhaseParameters) (mode : ℤ × ℤ) :
    negativeTraceWeight parameters 0 0 mode =
      Real.exp (radialPhase parameters 1 mode.2) / Real.sqrt (Grad.AnnularVariational.annularFrequency mode.1 mode.2) := by
  have exponential : Real.exp (2 * boundaryPhase parameters mode.2) =
      (Real.exp (boundaryPhase parameters mode.2)) ^ 2 := by
    rw [two_mul, Real.exp_add, pow_two]
  unfold negativeTraceWeight negativeTraceWeightSq
  simp only [mul_zero, pow_zero, mul_one]
  rw [Real.sqrt_mul (Real.exp_pos _).le, exponential, Real.sqrt_sq_eq_abs,
    abs_of_pos (Real.exp_pos _), boundaryPhase_at_outer, Real.sqrt_inv]
  rfl

theorem lowOuterXNegative_physical (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (field : lowEnergyGraph lower length positive) (mode : LowAnnularMode) :
    negativeTraceCoefficient parameters 0 0
      (lowOuterXNegative parameters lower length lengthPositive positive lowerHalf field) mode.val =
      lowPhysicalSection parameters lower length positive (lowerHalf.trans_lt (by norm_num)) field (1, mode)
        ⟨1, lowerHalf.trans (by norm_num), le_rfl⟩ := by
  unfold negativeTraceCoefficient
  rw [lowOuterXNegative_retained, ← Complex.ofReal_inv]
  change (negativeTraceWeight parameters 0 0 mode.val)⁻¹ •
    (lowOuterNegativeFactor length mode • ((Real.sqrt (lowMu length (1 / 2) mode.val.2))⁻¹ •
      lowEnergyEndpoint lower length positive (lowerHalf.trans_lt (by norm_num)) 1 field (1, mode))) = _
  rw [smul_smul, smul_smul]
  change _ = lowPhysicalInverseCurve parameters lower length positive (1, mode) 1 •
    lowEnergySection lower length positive (lowerHalf.trans_lt (by norm_num)) field (1, mode)
      ⟨1, lowerHalf.trans (by norm_num), le_rfl⟩
  rw [lowPhysicalInverseCurve_original parameters lower length positive (1, mode) 1
    ⟨lowerHalf.trans (by norm_num), le_rfl⟩]
  congr 1
  rw [negativeTraceWeight_base]
  unfold lowOuterNegativeFactor lowPhysicalFactor
  simp only [show (1 : Fin 2) ≠ 0 from by decide, ↓reduceIte, mul_one]
  have halfNonzero := (Real.sqrt_pos.mpr (lowMu_pos length (1 / 2) mode.val.2 (by norm_num))).ne'
  have frequencyNonzero := (Real.sqrt_pos.mpr (zero_lt_one.trans_le
    (Grad.AnnularVariational.annularFrequency_one_le mode.val.1 mode.val.2))).ne'
  have exponentialNonzero := (Real.exp_pos (radialPhase parameters 1 mode.val.2)).ne'
  field_simp

theorem lowOuterXiPositive_physical (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (field : lowEnergyGraph lower length positive) (mode : LowAnnularMode) :
    positiveTraceCoefficient parameters 0 0
      (lowOuterXiPositive parameters lower length lengthPositive positive lowerHalf field) mode.val =
      lowPhysicalSection parameters lower length positive (lowerHalf.trans_lt (by norm_num)) field (0, mode)
        ⟨1, lowerHalf.trans (by norm_num), le_rfl⟩ := by
  unfold positiveTraceCoefficient
  rw [lowOuterXiPositive_retained, ← Complex.ofReal_inv]
  change (positiveTraceWeight parameters 0 0 mode.val)⁻¹ •
    (lowOuterPositiveFactor parameters length mode • ((Real.sqrt (lowMu length (1 / 2) mode.val.2))⁻¹ •
      lowEnergyEndpoint lower length positive (lowerHalf.trans_lt (by norm_num)) 1 field (0, mode))) = _
  rw [smul_smul, smul_smul]
  change _ = lowPhysicalInverseCurve parameters lower length positive (0, mode) 1 •
    lowEnergySection lower length positive (lowerHalf.trans_lt (by norm_num)) field (0, mode)
      ⟨1, lowerHalf.trans (by norm_num), le_rfl⟩
  rw [lowPhysicalInverseCurve_original parameters lower length positive (0, mode) 1
    ⟨lowerHalf.trans (by norm_num), le_rfl⟩]
  congr 1
  rw [positiveTraceWeight_base]
  unfold lowOuterPositiveFactor lowPhysicalFactor
  simp only [↓reduceIte]
  have halfNonzero := (Real.sqrt_pos.mpr (lowMu_pos length (1 / 2) mode.val.2 (by norm_num))).ne'
  have frequencyNonzero := (Real.sqrt_pos.mpr (zero_lt_one.trans_le
    (Grad.AnnularVariational.annularFrequency_one_le mode.val.1 mode.val.2))).ne'
  have exponentialNonzero := (Real.exp_pos (radialPhase parameters 1 mode.val.2)).ne'
  have amplitudeNonzero := (lowAmplitude_pos length parameters.gamma mode).ne'
  have muNonzero := (lowMu_pos length 1 mode.val.2 zero_lt_one).ne'
  field_simp

end Grad.AnnularCrossMaps
