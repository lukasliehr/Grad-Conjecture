import GC18APInverseHigh

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.AnalyticWeights.Calculus

def apWeightCoefficient (dimension : ℕ) (sigma gamma ell : ℝ) (cell : ℤ) : C(ClosedDisk, OperatorValue dimension dimension) :=
  ⟨fun point => originalWeight sigma gamma ell cell point.val • ContinuousLinearMap.id ℂ (ComplexEuclidean dimension),
    (((smoothGoal sigma gamma ell cell).2.1.continuous.comp continuous_subtype_val).smul continuous_const)⟩

def apInverseWeightCoefficient (dimension : ℕ) (sigma gamma ell : ℝ) (cell : ℤ) : C(ClosedDisk, OperatorValue dimension dimension) :=
  ⟨fun point => (originalWeight sigma gamma ell cell point.val)⁻¹ • ContinuousLinearMap.id ℂ (ComplexEuclidean dimension), by
    have weightContinuous : Continuous (fun point : ClosedDisk => originalWeight sigma gamma ell cell point.val) :=
      (smoothGoal sigma gamma ell cell).2.1.continuous.comp continuous_subtype_val
    apply (weightContinuous.inv₀ (fun point => ?_)).smul continuous_const
    change physicalWeight sigma gamma ell cell point.val ≠ 0
    rw [physicalWeight_exp]
    exact (Real.exp_pos _).ne'⟩

theorem apInverseWeightCoefficient_bound (dimension : ℕ) {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (cell : ℤ) :
    ‖apInverseWeightCoefficient dimension sigma gamma ell cell‖ ≤ Real.exp (-((sigma - gamma) * |(cell : ℝ)|)) := by
  apply (ContinuousMap.norm_le _ (Real.exp_pos _).le).mpr
  intro point
  change ‖(originalWeight sigma gamma ell cell point.val)⁻¹ • ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)‖ ≤ _
  have positive := lt_of_lt_of_le (Real.exp_pos _) (apWeight_lower admissible cell point)
  calc
    _ ≤ ‖(originalWeight sigma gamma ell cell point.val)⁻¹‖ * ‖ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)‖ := norm_smul_le _ _
    _ ≤ ‖(originalWeight sigma gamma ell cell point.val)⁻¹‖ * 1 :=
      mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
    _ = (originalWeight sigma gamma ell cell point.val)⁻¹ := by
      rw [mul_one, Real.norm_of_nonneg (inv_nonneg.mpr positive.le)]
    _ ≤ _ := by rw [Real.exp_neg]; exact inv_anti₀ (Real.exp_pos _) (apWeight_lower admissible cell point)

theorem apBaseCoordinate_bound {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (field : apGrade L sigma gamma ell dimension grade) :
    ‖apUnscaledCoordinate L sigma gamma ell cell (zeroGradeIndex grade) field‖ ≤ ‖field‖ := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := grade) L sigma gamma ell)
    (isClosed_le (apUnscaledCoordinate L sigma gamma ell cell (zeroGradeIndex grade)).continuous.norm continuous_norm) _ field
  intro core
  rw [apUnscaledCoordinate_core]
  exact (apUnscaledDerivative_bound L sigma gamma ell cell (core cell) (0, 0) (by change 0 ≤ grade; omega)).trans (by
    change ‖apRowLinear L sigma gamma ell cell (core cell)‖ ≤ ‖apFiniteEmbed (grade := grade) L sigma gamma ell core‖
    rw [← apFiniteEmbed_apply]
    exact lp.norm_apply_le_norm (by norm_num) _ _)

def apL2Trace {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ) :
    apGrade L sigma gamma ell dimension grade →L[ℂ] DiskL2 dimension :=
  (closedOperatorL2 (apInverseWeightCoefficient dimension sigma gamma ell cell)).comp
    (apUnscaledCoordinate L sigma gamma ell cell (zeroGradeIndex grade))

theorem apL2Trace_bound {dimension grade : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (cell : ℤ) (field : apGrade L sigma gamma ell dimension grade) :
    ‖apL2Trace L sigma gamma ell cell field‖ ≤ Real.exp (-((sigma - gamma) * |(cell : ℝ)|)) * ‖field‖ := by
  exact (closedOperatorL2_apply_norm_le _ _).trans
    (mul_le_mul (apInverseWeightCoefficient_bound dimension admissible cell) (apBaseCoordinate_bound L sigma gamma ell cell field)
      (norm_nonneg _) (Real.exp_pos _).le)

theorem apL2Trace_core {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (core : ℤ →₀ ClosedJet dimension) :
    apL2Trace L sigma gamma ell cell (apFiniteInto (grade := grade) L sigma gamma ell core) = closedContinuousToDiskL2 (core cell).value := by
  change closedOperatorL2 _ (apUnscaledCoordinate L sigma gamma ell cell (zeroGradeIndex grade) (apFiniteInto L sigma gamma ell core)) = _
  rw [apUnscaledCoordinate_core]
  change closedOperatorL2 _ (closedContinuousToDiskL2 (closedMultiDerivative (apWeightedJet sigma gamma ell cell (core cell)) (0, 0))) = _
  rw [closedMultiDerivative_zero, closedOperatorL2_closed]
  apply congrArg closedContinuousToDiskL2
  apply ContinuousMap.ext
  intro point
  change (originalWeight sigma gamma ell cell point.val)⁻¹ • (apWeightedJet sigma gamma ell cell (core cell)).value point = _
  rw [apWeightedJet_value, smul_smul, inv_mul_cancel₀, one_smul]
  change physicalWeight sigma gamma ell cell point.val ≠ 0
  rw [physicalWeight_exp]
  exact (Real.exp_pos _).ne'

theorem apL2Trace_weighted {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (field : apGrade L sigma gamma ell dimension grade) :
    closedOperatorL2 (apWeightCoefficient dimension sigma gamma ell cell) (apL2Trace L sigma gamma ell cell field) =
      apUnscaledCoordinate L sigma gamma ell cell (zeroGradeIndex grade) field := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := grade) L sigma gamma ell)
    (isClosed_eq ((closedOperatorL2 (apWeightCoefficient dimension sigma gamma ell cell)).continuous.comp
      (apL2Trace L sigma gamma ell cell).continuous)
      (apUnscaledCoordinate L sigma gamma ell cell (zeroGradeIndex grade)).continuous) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apL2Trace_core, apUnscaledCoordinate_core, closedOperatorL2_closed]
  change closedContinuousToDiskL2 _ = closedContinuousToDiskL2 (closedMultiDerivative (apWeightedJet sigma gamma ell cell (core cell)) (0, 0))
  rw [closedMultiDerivative_zero]
  rfl

theorem apL2Trace_ext {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (first second : apGrade L sigma gamma ell dimension grade)
    (equality : ∀ cell, apL2Trace L sigma gamma ell cell first = apL2Trace L sigma gamma ell cell second) : first = second := by
  apply apGrade_ext L sigma gamma ell
  intro cell
  rw [← apL2Trace_weighted, ← apL2Trace_weighted, equality]

end Grad.GaugeCoefficients.Physical.RadialLedger
