import RadialCompletion

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace Grad.NonlinearRadial

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct

theorem radialIntervalJet_split {dimension : ℕ} (field : ClosedJet dimension)
    {cutoff : ℝ} (nonnegative : 0 ≤ cutoff) (bounded : cutoff ≤ 1) :
    radialIntervalJet 0 cutoff field + radialIntervalJet cutoff 1 field = radialIntervalJet 0 1 field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change radialIntervalValue 0 cutoff field point.val + radialIntervalValue cutoff 1 field point.val =
    radialIntervalValue 0 1 field point.val
  have continuousIntegrand : Continuous (fun scale : ℝ =>
      Real.negMulLog scale • smoothClosedExtension field (scale • point.val)) :=
    Real.continuous_negMulLog.smul ((smoothClosedExtension_smooth field).continuous.comp
      (continuous_id.smul continuous_const))
  unfold radialIntervalValue
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le nonnegative, ← intervalIntegral.integral_of_le bounded,
    ← intervalIntegral.integral_of_le zero_le_one]
  exact intervalIntegral.integral_add_adjacent_intervals
    (continuousIntegrand.intervalIntegrable 0 cutoff) (continuousIntegrand.intervalIntegrable cutoff 1)

theorem radialCore_sub_truncated {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) {cutoff : ℝ}
    (nonnegative : 0 ≤ cutoff) (bounded : cutoff ≤ 1) :
    radialCore parameters field - radialIntervalCore parameters cutoff 1 nonnegative le_rfl field =
      radialIntervalCore parameters 0 cutoff le_rfl bounded field := by
  apply (sub_eq_iff_eq_add).mpr
  symm
  apply Subtype.ext
  funext cell
  exact radialIntervalJet_split (field.val cell) nonnegative bounded

theorem radial_truncation_error {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (grade : ℕ) {cutoff : ℝ}
    (nonnegative : 0 ≤ cutoff) (bounded : cutoff ≤ 1) :
    originalGradeNorm grade
      (radialCore parameters field - radialIntervalCore parameters cutoff 1 nonnegative le_rfl field) ≤
      dilationGradeConstant grade * (cutoff + Real.negMulLog cutoff) * originalGradeNorm grade field := by
  rw [radialCore_sub_truncated parameters field nonnegative bounded]
  have bound := radialIntervalCore_bound parameters 0 cutoff le_rfl bounded field grade
  rw [logarithmicMass_zero nonnegative] at bound
  exact bound

abbrev RadialCutoff := {cutoff : ℝ // 0 ≤ cutoff ∧ cutoff ≤ 1}

def zeroCutoff : RadialCutoff := ⟨0, le_rfl, zero_le_one⟩

/-- Explicit same-grade convergence of the genuine truncated integrals to
the literal full integral in the original completion. -/
theorem radial_truncated_tendsto {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (grade : ℕ) :
    Tendsto (fun cutoff : RadialCutoff => aGradeEta parameters
      (GradeCore.ofCoreLinear (grade := grade)
        (radialIntervalCore parameters cutoff.val 1 cutoff.property.1 le_rfl field)))
      (𝓝 zeroCutoff) (𝓝 (radialCompleted (grade := grade) parameters
        (aGradeEta parameters (GradeCore.ofCoreLinear field)))) := by
  rw [radialCompleted_eta, tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero'
    (g := fun cutoff : RadialCutoff => dilationGradeConstant grade *
      (cutoff.val + Real.negMulLog cutoff.val) * originalGradeNorm grade field)
    (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ ?_
  · apply Eventually.of_forall
    intro cutoff
    rw [← map_sub, aGradeEta_norm, norm_sub_rev, ← map_sub]
    exact radial_truncation_error parameters field grade cutoff.property.1 cutoff.property.2
  · have limit : Tendsto (fun cutoff : RadialCutoff =>
        dilationGradeConstant grade * (cutoff.val + Real.negMulLog cutoff.val) * originalGradeNorm grade field)
        (𝓝 zeroCutoff) (𝓝 (dilationGradeConstant grade *
          (zeroCutoff.val + Real.negMulLog zeroCutoff.val) * originalGradeNorm grade field)) :=
      ((continuous_const.mul (continuous_subtype_val.add
        (Real.continuous_negMulLog.comp continuous_subtype_val))).mul continuous_const).continuousAt.tendsto
    simpa only [zeroCutoff, Real.negMulLog_zero, add_zero, mul_zero, zero_mul] using limit

end Grad.NonlinearRadial
