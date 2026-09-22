import GQC45GraphBounds

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger

def removedGraphConstant : ℝ := 1 + ‖planarPartMap‖ + ‖toroidalPartMap‖

theorem removedGraphConstant_nonnegative : 0 ≤ removedGraphConstant := by
  unfold removedGraphConstant
  positivity

theorem apSmoothRotation_valueMap_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {output : ℕ}
    (mapping : ComplexEuclidean 3 →L[ℂ] ComplexEuclidean output)
    (field : APSmooth L sigma gamma ell 3) (grade : ℕ)
    (rotationBound : ‖apSmoothGrade L sigma gamma ell 3 grade (apSmoothRotation admissible 3 field)‖ ≤
      ‖apSmoothGrade L sigma gamma ell 3 grade field‖) :
    ‖apSmoothGrade L sigma gamma ell output grade
      (apSmoothRotation admissible output (apSmoothValueMap L sigma gamma ell mapping field))‖ ≤
        ‖mapping‖ * ‖apSmoothGrade L sigma gamma ell 3 grade field‖ := by
  have equality := congrArg (fun value : APSmooth L sigma gamma ell output =>
    ‖apSmoothGrade L sigma gamma ell output grade value‖)
      (apSmoothRotation_valueMap admissible mapping field)
  exact equality.trans_le ((apSmoothValueMap_bound mapping (apSmoothRotation admissible 3 field) grade).trans
    (mul_le_mul_of_nonneg_left rotationBound (norm_nonneg _)))

/-- Every required extra rotation slot is bounded at the SAME grade
on the actual removed complement. No derivative of the input is taken. -/
theorem compensatedRemovedGraph_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (field : APSmooth L sigma gamma ell 3)
    (member : apSmoothGrade L sigma gamma ell 3 (grade + 1) field ∈
      apComplementRange L sigma gamma ell (grade + 1)) :
    compensatedNorm admissible grade (0, field) ≤
      Real.sqrt 5 * removedGraphConstant * ‖apSmoothGrade L sigma gamma ell 3 (grade + 1) field‖ := by
  have planarBound : ‖planarPartMap‖ ≤ removedGraphConstant := by
    unfold removedGraphConstant
    linarith [norm_nonneg toroidalPartMap]
  have scalarBound : ‖toroidalPartMap‖ ≤ removedGraphConstant := by
    unfold removedGraphConstant
    linarith [norm_nonneg planarPartMap]
  have rotationBound := (apSmoothRotation_removed admissible field (grade + 1) member).2
  have result := compensatedGraph_bound_of_entries admissible grade (0, field)
    (removedGraphConstant * ‖apSmoothGrade L sigma gamma ell 3 (grade + 1) field‖)
    (mul_nonneg removedGraphConstant_nonnegative (norm_nonneg _)) (by
      intro index
      fin_cases index
      · change ‖(0 : apGrade L sigma gamma ell 1 (grade + 2))‖ ≤ _
        rw [norm_zero]
        exact mul_nonneg removedGraphConstant_nonnegative (norm_nonneg _)
      · exact (apSmoothValueMap_bound planarPartMap field (grade + 1)).trans
          (mul_le_mul_of_nonneg_right planarBound (norm_nonneg _))
      · exact (apSmoothRotation_valueMap_bound admissible planarPartMap field (grade + 1) rotationBound).trans
          (mul_le_mul_of_nonneg_right planarBound (norm_nonneg _))
      · exact (apSmoothValueMap_bound toroidalPartMap field (grade + 1)).trans
          (mul_le_mul_of_nonneg_right scalarBound (norm_nonneg _))
      · exact (apSmoothRotation_valueMap_bound admissible toroidalPartMap field (grade + 1) rotationBound).trans
          (mul_le_mul_of_nonneg_right scalarBound (norm_nonneg _)))
  exact result.trans_eq (mul_assoc _ _ _).symm

theorem compensatedNorm_neg {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (data : CompensatedData L sigma gamma ell) :
    compensatedNorm admissible grade (-data) = compensatedNorm admissible grade data := by
  unfold compensatedNorm
  rw [map_neg, norm_neg]

end Grad.GaugeCoefficients.Physical.Compensated
