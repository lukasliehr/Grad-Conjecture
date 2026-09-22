import BT16FiniteTrace

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace Grad.BoundaryTrace

open Grad.ClosedJets Grad.CartesianState Grad.Constraints

local instance traceGradePeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

theorem boundaryCirclePoint_coe (angle : ℝ) :
    boundaryCirclePoint (angle : CellCircle) = collarPlane (0, angle) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [boundaryCirclePoint, collarPlane, AddCircle.toCircle_apply_mk,
      Circle.coe_exp, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

theorem collarField_boundary {dimension : ℕ} (field : ClosedJet dimension) (angle : ℝ) :
    collarField (smoothClosedExtension field) (0, angle) = field.value (boundaryDiskPoint (angle : CellCircle)) := by
  rw [collarField, collarCutoff, collarCutoff1D_zero, one_smul, ← boundaryCirclePoint_coe]
  exact smoothClosedExtension_value field (boundaryDiskPoint _)

theorem collarField_endpoint {dimension : ℕ} (field : ClosedJet dimension) (angle : ℝ) :
    collarField (smoothClosedExtension field) (1 / 4, angle) = 0 := by
  rw [collarField, collarCutoff, collarCutoff1D_vanishes (1 / 4) (by norm_num), zero_smul]

theorem collarField_boundary_coefficient {dimension : ℕ} (field : ClosedJet dimension) (mode : ℤ) :
    angularCoefficient (fun angle => collarField (smoothClosedExtension field) (0, angle)) mode =
      fourierCoeff (fun angle : CellCircle => field.value (boundaryDiskPoint angle)) mode := by
  simp_rw [collarField_boundary]
  exact angularCoefficient_circle (fun angle : CellCircle => field.value (boundaryDiskPoint angle)) mode

theorem collar_angularJet_integral_le {dimension : ℕ} (order : ℕ)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field) :
    collarIntegral (fun point => ‖angularJet order field point‖ ^ 2) ≤
      collarIntegral (fun point => ‖iteratedFDeriv ℝ order field point‖ ^ 2) := by
  apply collarIntegral_mono
  · exact (angularJet_smooth order field smooth).continuous.norm.pow 2
  · exact (smooth.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm.pow 2
  · intro point _
    exact pow_le_pow_left₀ (norm_nonneg _) (angularJet_norm_le order field point) 2

theorem collar_radialAngularJet_integral_le {dimension : ℕ} (order : ℕ)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field) :
    collarIntegral (fun point => ‖angularJet order (radialField field) point‖ ^ 2) ≤
      collarIntegral (fun point => ‖iteratedFDeriv ℝ (order + 1) field point‖ ^ 2) := by
  apply collarIntegral_mono
  · exact (angularJet_smooth order (radialField field) (radialField_smooth field smooth)).continuous.norm.pow 2
  · exact (smooth.continuous_iteratedFDeriv (by exact_mod_cast (le_top : ((order + 1) : ℕ∞) ≤ ⊤))).norm.pow 2
  · intro point _
    exact pow_le_pow_left₀ (norm_nonneg _) (radialAngularJet_norm_le field smooth order point) 2

def traceCellConstant (grade : ℕ) : ℝ :=
  frequencyGradeConstant grade * ((4 / 3 : ℝ) * collarOrderConstant 0 + (4 / 3 : ℝ) * collarOrderConstant grade) +
  frequencyGradeConstant (grade - 1) * ((4 / 3 : ℝ) * collarOrderConstant 1 + (4 / 3 : ℝ) * collarOrderConstant grade)

theorem traceCellConstant_nonnegative (grade : ℕ) : 0 ≤ traceCellConstant grade := by
  unfold traceCellConstant
  exact add_nonneg
    (mul_nonneg (frequencyGradeConstant_nonnegative _) (add_nonneg
      (mul_nonneg (by norm_num) (collarOrderConstant_nonnegative _))
      (mul_nonneg (by norm_num) (collarOrderConstant_nonnegative _))))
    (mul_nonneg (frequencyGradeConstant_nonnegative _) (add_nonneg
      (mul_nonneg (by norm_num) (collarOrderConstant_nonnegative _))
      (mul_nonneg (by norm_num) (collarOrderConstant_nonnegative _))))

theorem finite_trace_original_cell {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (grade : ℕ) (gradePositive : 1 ≤ grade) (field : ClosedJet dimension) (modes : Finset ℤ) :
    (∑ mode ∈ modes, boundaryFrequency (mode, cell) ^ (2 * grade - 1) *
      ‖fourierCoeff (fun angle : CellCircle =>
        (phaseWeightedJet parameters cell field).value (boundaryDiskPoint angle)) mode‖ ^ 2) ≤
      traceCellConstant grade * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2 := by
  let actual := collarField (smoothClosedExtension (phaseWeightedJet parameters cell field))
  have smooth : ContDiff ℝ ∞ actual := collarField_smooth (smoothClosedExtension_smooth _)
  have preliminary := finite_trace_collar_bound cell grade gradePositive actual smooth
    (collarField_periodic _) (collarField_endpoint _) modes
  have zeroBound := weighted_collar_integral_le_original (grade := grade) (order := 0) parameters cell field (Nat.zero_le _)
  simp only [Nat.sub_zero, norm_iteratedFDeriv_zero] at zeroBound
  have highBound := weighted_collar_integral_le_original (grade := grade) (order := grade) parameters cell field le_rfl
  simp only [Nat.sub_self, Nat.mul_zero, pow_zero, one_mul] at highBound
  have firstBound := weighted_collar_integral_le_original (grade := grade) (order := 1) parameters cell field gradePositive
  have angularBound := (collar_angularJet_integral_le grade actual smooth).trans highBound
  have radialLow : cellFrequency cell ^ (2 * (grade - 1)) *
      collarIntegral (fun point => ‖radialField actual point‖ ^ 2) ≤
        ((4 / 3 : ℝ) * collarOrderConstant 1) * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2 := by
    have lowComparison := collar_radialAngularJet_integral_le 0 actual smooth
    simp only [angularJet_zero] at lowComparison
    exact (mul_le_mul_of_nonneg_left lowComparison (pow_nonneg (cellFrequency_pos cell).le _)).trans firstBound
  have radialHigh : collarIntegral (fun point => ‖angularJet (grade - 1) (radialField actual) point‖ ^ 2) ≤
      ((4 / 3 : ℝ) * collarOrderConstant grade) * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2 := by
    have highComparison := collar_radialAngularJet_integral_le (grade - 1) actual smooth
    rw [Nat.sub_add_cancel gradePositive] at highComparison
    exact highComparison.trans highBound
  have aggregate := add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add zeroBound angularBound) (frequencyGradeConstant_nonnegative grade))
    (mul_le_mul_of_nonneg_left (add_le_add radialLow radialHigh) (frequencyGradeConstant_nonnegative (grade - 1)))
  have final := preliminary.trans aggregate
  simp only [actual, collarField_boundary_coefficient] at final
  apply final.trans_eq
  unfold traceCellConstant
  ring

end Grad.BoundaryTrace
