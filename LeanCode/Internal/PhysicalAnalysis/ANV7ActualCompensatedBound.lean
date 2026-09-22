import ANV6NativeReconstructionBounds

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
open Grad.ActualMeanInverse
variable {L sigma gamma ell : ℝ}

private theorem five_norm_bound (x a b c d e : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (square : x ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) : x ≤ a + b + c + d + e := by
  have squares : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 ≤ (a + b + c + d + e) ^ 2 := by
    nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg ha hd, mul_nonneg ha he,
      mul_nonneg hb hc, mul_nonneg hb hd, mul_nonneg hb he, mul_nonneg hc hd,
      mul_nonneg hc he, mul_nonneg hd he]
  nlinarith

private theorem four_squares_congr (a b c d u v w x : ℝ)
    (ha : a = u) (hb : b = v) (hc : c = w) (hd : d = x) :
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = u ^ 2 + v ^ 2 + w ^ 2 + x ^ 2 := by
  rw [ha, hb, hc, hd]

theorem reconstructedState_norm_sum (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell) (grade : ℕ) :
    compensatedNorm admissible grade (reconstructedState admissible theta source) ≤
      ‖apSmoothGrade L sigma gamma ell 1 (grade + 2) theta‖ +
      ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) (reconstructedVector admissible theta source.1)‖ +
      ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) (apSmoothRotation admissible 2 (reconstructedVector admissible theta source.1))‖ +
      ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) (reconstructedScalar admissible source.2.2)‖ +
      ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) (apSmoothRotation admissible 1 (reconstructedScalar admissible source.2.2))‖ := by
  have planar := reconstructedState_planar admissible theta source
  have scalar := reconstructedState_scalar admissible theta source
  let vectorGrade := apSmoothGrade L sigma gamma ell 2 (grade + 1)
  let scalarGrade := apSmoothGrade L sigma gamma ell 1 (grade + 1)
  have v := congrArg norm (congrArg vectorGrade planar)
  have rv := congrArg norm (congrArg vectorGrade (congrArg (apSmoothRotation admissible 2) planar))
  have e := congrArg norm (congrArg scalarGrade scalar)
  have re := congrArg norm (congrArg scalarGrade (congrArg (apSmoothRotation admissible 1) scalar))
  have tail := four_squares_congr _ _ _ _ _ _ _ _ v rv e re
  have square := compensatedNorm_sq admissible grade (reconstructedState admissible theta source)
  have reassociate (a b c d e : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 =
      a ^ 2 + (b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by ring
  have exactSquare := square.trans ((reassociate _ _ _ _ _).trans
    ((congrArg (fun value : ℝ => ‖apSmoothGrade L sigma gamma ell 1 (grade + 2) theta‖ ^ 2 + value) tail).trans
      (reassociate _ _ _ _ _).symm))
  exact five_norm_bound _ _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) exactSquare

def reconstructionConstant (L gamma : ℝ) (grade : ℕ) : ℝ :=
  1 + vectorGraphConstant (grade + 1) * (1 + loadConstant L gamma (grade + 1)) +
    (1 + angularInverseConstant (grade + 1))

theorem reconstructionConstant_nonnegative (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    0 ≤ reconstructionConstant L gamma grade := by
  have first := vectorGraphConstant_nonnegative (grade + 1)
  have second := loadConstant_nonnegative admissible (grade + 1)
  have third := angularInverseConstant_nonnegative (grade + 1)
  unfold reconstructionConstant
  positivity

private theorem collect_bounds (a b c v r e t A V E : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hA : 0 ≤ A) (hV : 0 ≤ V) (hE : 0 ≤ E)
    (vector : v + r ≤ V * (A * a + b)) (scalar : e + t ≤ E * c) :
    a + v + r + e + t ≤ (1 + V * (1 + A) + E) * (a + b + c) := by
  have total : a + v + r + e + t ≤ a + V * (A * a + b) + E * c := by linarith
  apply total.trans
  have oneA : a ≤ a + b + c := by linarith
  have oneB : b ≤ a + b + c := by linarith
  have oneC : c ≤ a + b + c := by linarith
  have inner := add_le_add (mul_le_mul_of_nonneg_left oneA hA) oneB
  have multiplied := mul_le_mul_of_nonneg_left inner hV
  have last := mul_le_mul_of_nonneg_left oneC hE
  nlinarith

/-- AN13 in the literal AN8 graph: Θ costs s+2; force and Hc cost s+1.
The constant retains the original analytic parameters and changes no width. -/
theorem reconstructedState_native_bound (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (compatible : source ∈ smoothCapSourceCore admissible)
    (nonresonant : VectorNonresonant admissible (reconstructionLoad admissible theta source.1)) (grade : ℕ) :
    compensatedNorm admissible grade (reconstructedState admissible theta source) ≤
      reconstructionConstant L gamma grade *
        (‖apSmoothGrade L sigma gamma ell 1 (grade + 2) theta‖ +
          ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) source.1‖ +
          ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) source.2.2‖) := by
  have vector := reconstructedVector_graph_bound admissible theta source.1 nonresonant (grade + 1)
  have scalar := reconstructedScalar_graph_bound admissible source.2.2
    (actualSource_conditions admissible source compatible).2.2.1 (grade + 1)
  exact (reconstructedState_norm_sum admissible theta source grade).trans
    (collect_bounds _ _ _ _ _ _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (loadConstant_nonnegative admissible (grade + 1)) (vectorGraphConstant_nonnegative (grade + 1))
      (add_nonneg zero_le_one (angularInverseConstant_nonnegative (grade + 1))) vector scalar)

end Grad.ActualNonexceptionalInverse
