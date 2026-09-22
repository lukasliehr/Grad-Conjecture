import ANV5CompensatedReconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.ActualNonexceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.ActualAngularInverse
variable {L sigma gamma ell : ℝ}

def loadConstant (L gamma : ℝ) (grade : ℕ) : ℝ := 2 * ‖quarterValueMap‖ * gradientBoundConstant L gamma grade

theorem loadConstant_nonnegative (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    0 ≤ loadConstant L gamma grade :=
  mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (gradientBoundConstant_nonnegative admissible grade)

private theorem double_add_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (first second : E) : ‖(2 : ℂ) • first + second‖ ≤ 2 * ‖first‖ + ‖second‖ := by
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul]; norm_num)

theorem reconstructionLoad_bound (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (force : APSmooth L sigma gamma ell 2) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 2 grade (reconstructionLoad admissible theta force)‖ ≤
      loadConstant L gamma grade * ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) theta‖ +
        ‖apSmoothGrade L sigma gamma ell 2 grade force‖ := by
  let project := apSmoothGrade L sigma gamma ell 2 grade
  have equality := (project.map_add ((2 : ℂ) • apSmoothQuarter L sigma gamma ell (apSmoothGradient admissible theta)) force).trans
    (congrArg (fun first => first + project force)
      (project.map_smul (2 : ℂ) (apSmoothQuarter L sigma gamma ell (apSmoothGradient admissible theta))))
  have gradient := apSmoothGradient_bound admissible theta grade
  have quarter := (apSmoothValueMap_bound quarterValueMap (apSmoothGradient admissible theta) grade).trans
    (mul_le_mul_of_nonneg_left gradient (norm_nonneg _))
  have bound := double_add_bound (project (apSmoothQuarter L sigma gamma ell (apSmoothGradient admissible theta))) (project force)
  have scaled : 2 * ‖project (apSmoothQuarter L sigma gamma ell (apSmoothGradient admissible theta))‖ + ‖project force‖ ≤
      2 * (‖quarterValueMap‖ * (gradientBoundConstant L gamma grade *
        ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) theta‖)) + ‖project force‖ :=
    add_le_add (mul_le_mul_of_nonneg_left quarter (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
  have finalEquality : 2 * (‖quarterValueMap‖ * (gradientBoundConstant L gamma grade *
        ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) theta‖)) + ‖project force‖ =
      loadConstant L gamma grade * ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) theta‖ + ‖project force‖ := by
    unfold loadConstant
    ring
  exact (congrArg norm equality).le.trans (bound.trans (scaled.trans_eq finalEquality))

def vectorGraphConstant (grade : ℕ) : ℝ := 1 + (1 + ‖quarterValueMap‖) * vectorInverseConstant grade

theorem vectorGraphConstant_nonnegative (grade : ℕ) : 0 ≤ vectorGraphConstant grade := by
  have positive := vectorInverseConstant_nonnegative grade
  unfold vectorGraphConstant
  positivity

theorem reconstructedVector_graph_bound (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (force : APSmooth L sigma gamma ell 2)
    (nonresonant : VectorNonresonant admissible (reconstructionLoad admissible theta force)) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 2 grade (reconstructedVector admissible theta force)‖ +
      ‖apSmoothGrade L sigma gamma ell 2 grade (apSmoothRotation admissible 2 (reconstructedVector admissible theta force))‖ ≤
      vectorGraphConstant grade * (loadConstant L gamma grade * ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) theta‖ +
        ‖apSmoothGrade L sigma gamma ell 2 grade force‖) := by
  let inverse := apVectorInverse admissible (reconstructionLoad admissible theta force)
  let project := apSmoothGrade L sigma gamma ell 2 grade
  have first : ‖project (-inverse)‖ = ‖project inverse‖ :=
    (congrArg norm (project.map_neg inverse)).trans (norm_neg _)
  have second : ‖project (apSmoothRotation admissible 2 (-inverse))‖ =
      ‖project (apSmoothRotation admissible 2 inverse)‖ :=
    (congrArg norm ((congrArg project (map_neg (apSmoothRotation admissible 2) inverse)).trans
      (project.map_neg (apSmoothRotation admissible 2 inverse)))).trans (norm_neg _)
  have original := apVectorInverse_graph_bound admissible (reconstructionLoad admissible theta force) nonresonant grade
  exact (congrArg₂ (fun a b : ℝ => a + b) first second).le.trans
    (original.trans (mul_le_mul_of_nonneg_left (reconstructionLoad_bound admissible theta force grade)
      (vectorGraphConstant_nonnegative grade)))

theorem reconstructedScalar_graph_bound (admissible : Admissible L sigma gamma ell)
    (source : APSmooth L sigma gamma ell 1) (nonresonant : APNonresonant admissible 0 source) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 1 grade (reconstructedScalar admissible source)‖ +
      ‖apSmoothGrade L sigma gamma ell 1 grade (apSmoothRotation admissible 1 (reconstructedScalar admissible source))‖ ≤
      (1 + angularInverseConstant grade) * ‖apSmoothGrade L sigma gamma ell 1 grade source‖ := by
  simpa only [reconstructedScalar, Int.cast_zero, mul_zero, norm_zero, add_zero, one_mul] using!
    apShiftInverse_graph_bound admissible 0 source nonresonant grade

end Grad.ActualNonexceptionalInverse
