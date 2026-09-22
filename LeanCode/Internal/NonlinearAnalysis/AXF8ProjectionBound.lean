import AXF7CorrectionBounds

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.QuotientProjection

theorem flatSourceProjection_bound (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ source : SmoothQuotient parameters,
      quotientNorm parameters grade (flatSourceProjection source) ≤
        constant * quotientNorm parameters grade source := by
  obtain ⟨mode, modeNonneg, modeBound⟩ := modeProjection_bound parameters grade
  obtain ⟨value, valueNonneg, valueBound⟩ := valueCorrection_bound parameters grade large
  obtain ⟨affine, affineNonneg, affineBound⟩ := radialAffineInsertion_bound parameters grade large
  obtain ⟨trace, traceNonneg, traceBound⟩ := affineTrace_bound parameters grade large
  obtain ⟨fourth, fourthNonneg, fourthBound⟩ := fourthCorrection_bound parameters grade large
  have angularNonneg := orthogonalGradeConstant_nonnegative grade
  refine ⟨2 * (1 + orthogonalGradeConstant grade) + mode + value * (1 + mode) + affine * trace + fourth,
    by positivity, ?_⟩
  intro source
  have projected : quotientNorm parameters grade (source - modeProjection parameters source) ≤
      (1 + mode) * quotientNorm parameters grade source := by
    calc
      _ ≤ quotientNorm parameters grade source + quotientNorm parameters grade (modeProjection parameters source) :=
        quotientNorm_sub_le parameters grade source (modeProjection parameters source)
      _ ≤ quotientNorm parameters grade source + mode * quotientNorm parameters grade source :=
        add_le_add le_rfl (modeBound source)
      _ = (1 + mode) * quotientNorm parameters grade source := by ring
  have correction := (valueBound (source - modeProjection parameters source)).trans
    (mul_le_mul_of_nonneg_left projected valueNonneg)
  have affineCorrection := (affineBound (affineTrace parameters source)).trans
    (mul_le_mul_of_nonneg_left (traceBound source) affineNonneg)
  have first := (quotientNorm_sub_le parameters grade (meanPair parameters source)
      (modeProjection parameters source)).trans
    (add_le_add (meanPair_bound parameters grade source) (modeBound source))
  have second := (quotientNorm_sub_le parameters grade
      (meanPair parameters source - modeProjection parameters source)
      (valueCorrection (source - modeProjection parameters source))).trans
    (add_le_add first correction)
  have third := (quotientNorm_sub_le parameters grade
      (meanPair parameters source - modeProjection parameters source -
        valueCorrection (source - modeProjection parameters source))
      (radialAffineInsertion (affineTrace parameters source))).trans
    (add_le_add second affineCorrection)
  rw [flatSourceProjection_apply]
  calc
    _ ≤ (((2 * (1 + orthogonalGradeConstant grade) * quotientNorm parameters grade source +
        mode * quotientNorm parameters grade source) +
        value * ((1 + mode) * quotientNorm parameters grade source)) +
        affine * (trace * quotientNorm parameters grade source)) + fourth * quotientNorm parameters grade source :=
      (quotientNorm_sub_le parameters grade _ _).trans (add_le_add third (fourthBound source))
    _ = _ := by ring

end Grad.FlatSourceProjection
