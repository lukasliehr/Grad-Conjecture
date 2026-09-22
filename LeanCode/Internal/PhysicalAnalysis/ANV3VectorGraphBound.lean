import ANV2ActualVectorInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.ActualNonexceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.ActualAngularInverse
variable {L sigma gamma ell : ℝ}

def vectorInverseConstant (grade : ℕ) : ℝ :=
  angularInverseConstant grade * (‖helicityValue 1‖ + ‖helicityValue (-1)‖)

theorem vectorInverseConstant_nonnegative (grade : ℕ) : 0 ≤ vectorInverseConstant grade :=
  mul_nonneg (angularInverseConstant_nonnegative grade) (add_nonneg (norm_nonneg _) (norm_nonneg _))

theorem apSignedInverse_bound (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (field : APSmooth L sigma gamma ell 2) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 2 grade (apSignedInverse admissible sign field)‖ ≤
      (angularInverseConstant grade * ‖helicityValue sign‖) * ‖apSmoothGrade L sigma gamma ell 2 grade field‖ := by
  have inverse := apShiftInverse_bound admissible sign grade (apHelicity L sigma gamma ell sign field)
  have projected := apSmoothValueMap_bound (helicityValue sign) field grade
  exact inverse.trans ((mul_le_mul_of_nonneg_left projected (angularInverseConstant_nonnegative grade)).trans_eq (by ring))

private theorem two_norms {E : Type*} [NormedAddCommGroup E]
    (first second : E) (a b source : ℝ) (left : ‖first‖ ≤ a * source) (right : ‖second‖ ≤ b * source) :
    ‖first + second‖ ≤ (a + b) * source := by
  have triangle := norm_add_le first second
  nlinarith

theorem apVectorInverse_bound (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 2 grade (apVectorInverse admissible field)‖ ≤
      vectorInverseConstant grade * ‖apSmoothGrade L sigma gamma ell 2 grade field‖ := by
  let project := apSmoothGrade L sigma gamma ell 2 grade
  have law := project.map_add (apSignedInverse admissible 1 field) (apSignedInverse admissible (-1) field)
  have bound := two_norms _ _ _ _ _
    (apSignedInverse_bound admissible 1 field grade) (apSignedInverse_bound admissible (-1) field grade)
  exact (congrArg norm law).le.trans (bound.trans_eq (by unfold vectorInverseConstant; ring))

private theorem graph_norm {E : Type*} [NormedAddCommGroup E]
    (source solution rotated turned : E) (C D : ℝ) (positive : 0 ≤ D)
    (solutionBound : ‖solution‖ ≤ C * ‖source‖) (turnBound : ‖turned‖ ≤ D * ‖solution‖)
    (equation : rotated + turned = source) :
    ‖solution‖ + ‖rotated‖ ≤ (1 + (1 + D) * C) * ‖source‖ := by
  have equality : rotated = source - turned := eq_sub_of_add_eq equation
  have triangle := norm_sub_le source turned
  rw [← equality] at triangle
  have multiplied := mul_le_mul_of_nonneg_left solutionBound positive
  nlinarith

/-- The true R derivative of the vector inverse is controlled at the same grade
by its equation; the source carries no extra angular derivative. -/
theorem apVectorInverse_graph_bound (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) (nonresonant : VectorNonresonant admissible field) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 2 grade (apVectorInverse admissible field)‖ +
      ‖apSmoothGrade L sigma gamma ell 2 grade (apSmoothRotation admissible 2 (apVectorInverse admissible field))‖ ≤
      (1 + (1 + ‖quarterValueMap‖) * vectorInverseConstant grade) *
        ‖apSmoothGrade L sigma gamma ell 2 grade field‖ := by
  let project := apSmoothGrade L sigma gamma ell 2 grade
  have equation := (project.map_add (apSmoothRotation admissible 2 (apVectorInverse admissible field))
    (apSmoothQuarter L sigma gamma ell (apVectorInverse admissible field))).symm.trans
      (congrArg project (apVectorInverse_solves admissible field nonresonant))
  exact graph_norm _ _ _ _ _ _ (norm_nonneg _) (apVectorInverse_bound admissible field grade)
    (apSmoothValueMap_bound quarterValueMap (apVectorInverse admissible field) grade) equation

end Grad.ActualNonexceptionalInverse
