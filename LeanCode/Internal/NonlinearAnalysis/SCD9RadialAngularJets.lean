import SCD8PolarPaidBound
import BT14FrequencyEnergy

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial Grad.BoundaryTrace

def radialIter {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value] :
    ℕ → (ℝ × ℝ → Value) → (ℝ × ℝ → Value) :=
  fun order field => Nat.rec field (fun _ previous => radialField previous) order

theorem radialIter_succ {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (order : ℕ) (field : ℝ × ℝ → Value) :
    radialIter (order + 1) field = radialField (radialIter order field) := rfl

theorem radialIter_smooth {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (order : ℕ) (field : ℝ × ℝ → Value) (smooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (radialIter order field) := by
  induction order with
  | zero => exact smooth
  | succ order inductionHypothesis => exact radialField_smooth _ inductionHypothesis

theorem radialIter_periodic {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (order : ℕ) (field : ℝ × ℝ → Value) (periodic : Function.Periodic field (0, 2 * Real.pi)) :
    Function.Periodic (radialIter order field) (0, 2 * Real.pi) := by
  induction order with
  | zero => exact periodic
  | succ order inductionHypothesis => exact radialField_periodic _ inductionHypothesis

theorem radialIter_tensor_norm_le {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (radial angular : ℕ) (field : ℝ × ℝ → Value) (smooth : ContDiff ℝ ∞ field) (point : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ angular (radialIter radial field) point‖ ≤
      ‖iteratedFDeriv ℝ (angular + radial) field point‖ := by
  induction radial generalizing angular with
  | zero =>
    change ‖iteratedFDeriv ℝ angular field point‖ ≤ ‖iteratedFDeriv ℝ angular field point‖
    exact le_rfl
  | succ radial inductionHypothesis =>
    apply (radialField_iteratedFDeriv_norm_le _ (radialIter_smooth radial field smooth) angular point).trans
    have aligned : angular + 1 + radial = angular + (radial + 1) := by omega
    have next := inductionHypothesis (angular + 1)
    rw [aligned] at next
    exact next

theorem radialAngular_norm_le {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (radial angular : ℕ) (field : ℝ × ℝ → Value) (smooth : ContDiff ℝ ∞ field) (point : ℝ × ℝ) :
    ‖angularJet angular (radialIter radial field) point‖ ≤
      ‖iteratedFDeriv ℝ (angular + radial) field point‖ :=
  (angularJet_norm_le _ _ _).trans (radialIter_tensor_norm_le radial angular field smooth point)

def radialCoefficientJet {dimension : ℕ} (field : ℝ × ℝ → ComplexEuclidean dimension)
    (mode : ℤ) (order : ℕ) (radius : ℝ) : ComplexEuclidean dimension :=
  angularCoefficient (fun angle => radialIter order field (radius, angle)) mode

theorem radialCoefficientJet_hasDerivAt {dimension : ℕ} (field : ℝ × ℝ → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ field) (mode : ℤ) (order : ℕ) (radius : ℝ) :
    HasDerivAt (radialCoefficientJet field mode order)
      (radialCoefficientJet field mode (order + 1) radius) radius :=
  angularCoefficient_hasDerivAt _ (radialIter_smooth order field smooth) mode radius

theorem radialCoefficientJet_smooth {dimension : ℕ} (field : ℝ × ℝ → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ field) (mode : ℤ) (order : ℕ) :
    ContDiff ℝ ∞ (radialCoefficientJet field mode order) :=
  angularCoefficient_smooth _ (radialIter_smooth order field smooth) mode

theorem divided_mixed_paid {dimension grade radial angular power : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (paid : angular + radial + power + 3 ≤ grade) (point : ℝ × ℝ) (inside : point ∈ polarRectangle) :
    cellFrequency cell ^ power *
      ‖angularJet angular (radialIter radial (dividedPolarValue (phaseWeightedJet parameters cell field))) point‖ ≤
      divisionDerivativeConstant (angular + radial) *
        ‖cellGradeRowLinear (grade := grade) parameters cell field‖ :=
  (mul_le_mul_of_nonneg_left (radialAngular_norm_le radial angular _ (dividedPolarValue_smooth _) point)
    (pow_nonneg (cellFrequency_pos cell).le _)).trans
      (dividedPolarValue_derivative_paid parameters cell field paid point inside)

/-- Literal original annular frequency, not the equivalent Euclidean weight. -/
def annularFrequency (mode cell : ℤ) : ℝ := 1 + |(mode : ℝ)| + |(cell : ℝ)|

theorem annularFrequency_nonnegative (mode cell : ℤ) : 0 ≤ annularFrequency mode cell := by
  unfold annularFrequency
  positivity

theorem annularFrequency_even_bound (mode cell : ℤ) (order : ℕ) :
    annularFrequency mode cell ^ (2 * order) ≤ (4 : ℝ) ^ (2 * order) *
      (cellFrequency cell ^ (2 * order) + |(mode : ℝ)| ^ (2 * order)) := by
  have cellBound : |(cell : ℝ)| ≤ cellFrequency cell := by
    rw [cellFrequency_formula]
    exact (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr (by nlinarith [sq_abs (cell : ℝ)])
  have bound : annularFrequency mode cell ≤ 2 * (cellFrequency cell + |(mode : ℝ)|) := by
    unfold annularFrequency
    linarith [cellFrequency_one_le cell, abs_nonneg (mode : ℝ)]
  calc
    _ ≤ (2 * (cellFrequency cell + |(mode : ℝ)|)) ^ (2 * order) :=
      pow_le_pow_left₀ (annularFrequency_nonnegative _ _) bound _
    _ = (2 : ℝ) ^ (2 * order) * (cellFrequency cell + |(mode : ℝ)|) ^ (2 * order) := mul_pow _ _ _
    _ ≤ (2 : ℝ) ^ (2 * order) * ((2 : ℝ) ^ (2 * order) *
        (cellFrequency cell ^ (2 * order) + |(mode : ℝ)| ^ (2 * order))) :=
      mul_le_mul_of_nonneg_left
        (two_term_pow_bound _ _ (cellFrequency_pos cell).le (abs_nonneg _) _) (by positivity)
    _ = _ := by rw [← mul_assoc, ← mul_pow]; norm_num

end Grad.SourceCollarDivision
