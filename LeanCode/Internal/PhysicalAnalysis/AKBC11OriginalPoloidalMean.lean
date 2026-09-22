import AKBC10SameMassInverseRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory
open scoped Interval BigOperators
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.SourceCollar
open Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.FlatSourceProjection

def polarTangentialComponentLinear (angle : ℝ) : ComplexEuclidean 2 →L[ℂ] ℂ :=
  -(Real.sin angle : ℂ) • PiLp.proj 2 (fun _ : Fin 2 => ℂ) 0 +
    (Real.cos angle : ℂ) • PiLp.proj 2 (fun _ : Fin 2 => ℂ) 1

@[simp] theorem polarTangentialComponentLinear_apply (angle : ℝ) (value : ComplexEuclidean 2) :
    polarTangentialComponentLinear angle value=polarTangentialComponent angle value := by
  simp [polarTangentialComponentLinear,polarTangentialComponent]

theorem originalTangentialCore_axis_value {parameters : PhaseParameters}
    (field : ACore parameters 2) (cell : ℤ) (radius : ℝ) (bounded : |radius|≤1) :
    ((tangentialCore parameters field).val cell).value (axisClosedPoint radius bounded) 1=
      polarTangentialMean (field.val cell) radius bounded 0 := by
  have axis : polarClosedPoint radius bounded 0=axisClosedPoint radius bounded := by
    apply Subtype.ext
    rw [polarClosedPoint_coordinates]
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [axisClosedPoint]
  rw [← axis,tangentialCore_apply,tangentialJet_polar_formula]
  simp [polarTangentialVector]

theorem polarTangentialComponent_norm_le_two (angle : ℝ) (value : ComplexEuclidean 2) :
    ‖polarTangentialComponent angle value‖≤2*‖value‖ := by
  unfold polarTangentialComponent
  calc
    _ ≤ ‖-(Real.sin angle : ℂ)*value 0‖+‖(Real.cos angle : ℂ)*value 1‖ := norm_add_le _ _
    _ = |Real.sin angle| *‖value 0‖+|Real.cos angle| *‖value 1‖ := by
      simp only [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ 1*‖value‖+1*‖value‖ := add_le_add
      (mul_le_mul (Real.abs_sin_le_one angle) (PiLp.norm_apply_le value 0) (norm_nonneg _) zero_le_one)
      (mul_le_mul (Real.abs_cos_le_one angle) (PiLp.norm_apply_le value 1) (norm_nonneg _) zero_le_one)
    _ = 2*‖value‖ := by ring

theorem sourceAngularAverage_polarTangential
    {parameters : PhaseParameters} (field : ACore parameters 2)
    (radius : ℝ) (bounded : |radius| ≤ 1) (axialAngle : ℝ) :
    sourceAngularAverage (fun polarAngle => polarTangentialComponent polarAngle
      (sourceCoreValue field (polarClosedPoint radius bounded polarAngle) axialAngle)) =
      (coreValue (tangentialCore parameters field)
        (axisClosedPoint radius bounded) axialAngle) 1 := by
  let term : ℤ → ℝ → ℂ := fun cell angle =>
    axialPhase cell axialAngle * polarTangentialComponent angle
      ((field.val cell).value (polarClosedPoint radius bounded angle))
  have termContinuous : ∀ cell, Continuous (term cell) := by
    intro cell
    dsimp only [term]
    unfold polarTangentialComponent
    have pointCurve : Continuous (fun angle : ℝ =>
        polarClosedPoint radius bounded angle) := by
      exact Grad.GaugeCoefficients.Radial.continuous_rotatedPoint_joint.comp
        (continuous_id.prodMk continuous_const)
    have valueCurve : Continuous (fun angle : ℝ =>
        (field.val cell).value (polarClosedPoint radius bounded angle)) :=
      (field.val cell).value.continuous.comp pointCurve
    fun_prop
  have termIntegrable : ∀ cell,
      IntervalIntegrable (term cell) volume 0 (2 * Real.pi) :=
    fun cell => (termContinuous cell).intervalIntegrable _ _
  have dominating : Summable (fun cell : ℤ => 2 * ‖(field.val cell).value‖) :=
    (Grad.Cor18.cell_sup_norm_summable field).mul_left 2
  have law : HasSum (fun cell => ∫ angle in (0 : ℝ)..2 * Real.pi, term cell angle)
      (∫ angle in (0 : ℝ)..2 * Real.pi,
        polarTangentialComponent angle
          (sourceCoreValue field (polarClosedPoint radius bounded angle) axialAngle)) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun cell _ => 2 * ‖(field.val cell).value‖)
    · intro cell
      exact (termContinuous cell).aestronglyMeasurable
    · intro cell
      filter_upwards with angle _
      dsimp only [term]
      rw [norm_mul, norm_axialPhase, one_mul]
      exact (polarTangentialComponent_norm_le_two angle _).trans
        (mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm _ _)
          (by norm_num))
    · filter_upwards with angle _
      exact dominating
    · exact intervalIntegrable_const
    · filter_upwards with angle _
      have vectorSummable := coreValue_summable field
        (polarClosedPoint radius bounded angle) axialAngle
      have mapped := (polarTangentialComponentLinear angle).map_tsum vectorSummable
      have scalarSummable : Summable (fun cell : ℤ => term cell angle) := by
        apply Summable.of_norm_bounded dominating
        intro cell
        dsimp only [term]
        rw [norm_mul, norm_axialPhase, one_mul]
        exact (polarTangentialComponent_norm_le_two angle _).trans
          (mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm _ _)
            (by norm_num))
      rw [← show (∑' cell : ℤ, term cell angle) =
          polarTangentialComponent angle
            (sourceCoreValue field (polarClosedPoint radius bounded angle) axialAngle) by
        change (∑' cell : ℤ, axialPhase cell axialAngle *
          polarTangentialComponent angle ((field.val cell).value
            (polarClosedPoint radius bounded angle))) = _
        simpa only [sourceCoreValue, coreValue, map_smul, smul_eq_mul,
          polarTangentialComponentLinear_apply] using mapped.symm]
      exact scalarSummable.hasSum
  have normalized := law.const_smul ((2 * Real.pi)⁻¹ : ℝ)
  have termLaw (cell : ℤ) :
      (2 * Real.pi)⁻¹ • (∫ angle in (0 : ℝ)..2 * Real.pi, term cell angle) =
        axialPhase cell axialAngle •
          (((tangentialCore parameters field).val cell).value
            (axisClosedPoint radius bounded) 1) := by
    dsimp only [term]
    rw [intervalIntegral.integral_const_mul]
    rw [originalTangentialCore_axis_value]
    unfold polarTangentialMean
    simp only [add_zero]
    simp only [Complex.real_smul, smul_eq_mul]
    ring
  simp only [termLaw] at normalized
  have sumEquality :
      (∑' cell : ℤ, axialPhase cell axialAngle •
        (((tangentialCore parameters field).val cell).value
          (axisClosedPoint radius bounded) 1)) =
        (coreValue (tangentialCore parameters field)
          (axisClosedPoint radius bounded) axialAngle) 1 := by
    have mapped := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) 1).map_tsum
      (coreValue_summable (tangentialCore parameters field)
        (axisClosedPoint radius bounded) axialAngle)
    change ((∑' cell : ℤ, axialPhase cell axialAngle •
      ((tangentialCore parameters field).val cell).value
        (axisClosedPoint radius bounded)) 1) =
      ∑' cell : ℤ, axialPhase cell axialAngle *
        (((tangentialCore parameters field).val cell).value
          (axisClosedPoint radius bounded) 1) at mapped
    simpa only [coreValue, smul_eq_mul] using mapped.symm
  change ((2 * Real.pi)⁻¹ : ℝ) •
      (∫ angle in (0 : ℝ)..2 * Real.pi,
        polarTangentialComponent angle
          (sourceCoreValue field (polarClosedPoint radius bounded angle) axialAngle)) = _
  rw [← normalized.tsum_eq, sumEquality]

end Grad.OriginalKernelCovariantRecovery
