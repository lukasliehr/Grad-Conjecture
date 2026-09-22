import GC18APTrace

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.AnalyticWeights.Calculus

theorem apWeight_lower {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (cell : ℤ) (point : ClosedDisk) :
    Real.exp ((sigma - gamma) * |(cell : ℝ)|) ≤ originalWeight sigma gamma ell cell point.val := by
  have membership : point.val ∈ closedDisk := by
    simpa only [closedDisk, Metric.mem_closedBall, dist_zero_right] using
      (show ‖point.val‖ ≤ 1 from point.property)
  have bounds := Grad.AnalyticWeights.weight_absolute_bounds sigma gamma (ell * ‖point.val‖) cell
    (admissible_gamma_nonnegative admissible) (mul_nonneg (admissible_ell_nonnegative admissible) (norm_nonneg _))
    (admissible_rate_nonnegative admissible membership)
  apply (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))).trans bounds.1
  have radius := mul_le_mul_of_nonneg_left (admissible_scaled_radius_le_one admissible membership)
    (admissible_gamma_nonnegative admissible)
  dsimp [Grad.AnalyticWeights.rate]
  linarith

def apUnweightMap {dimension : ℕ} (sigma gamma ell : ℝ) (cell : ℤ) :
    C(ClosedDisk, ComplexEuclidean dimension) →ₗ[ℂ] C(ClosedDisk, ComplexEuclidean dimension) where
  toFun field := ⟨fun point => (originalWeight sigma gamma ell cell point.val)⁻¹ • field point, by
    have weightContinuous : Continuous (fun point : ClosedDisk => originalWeight sigma gamma ell cell point.val) :=
      ((smoothGoal sigma gamma ell cell).2.1.continuous.comp continuous_subtype_val)
    apply (weightContinuous.inv₀ (fun point => ?_)).smul field.continuous
    change physicalWeight sigma gamma ell cell point.val ≠ 0
    rw [physicalWeight_exp]
    exact (Real.exp_pos _).ne'⟩
  map_add' first second := by
    apply ContinuousMap.ext
    intro point
    exact smul_add ((originalWeight sigma gamma ell cell point.val)⁻¹) (first point) (second point)
  map_smul' scalar field := by
    apply ContinuousMap.ext
    intro point
    exact smul_comm ((originalWeight sigma gamma ell cell point.val)⁻¹) scalar (field point)

theorem apUnweightMap_bound {dimension : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (cell : ℤ) (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    ‖apUnweightMap sigma gamma ell cell field‖ ≤ Real.exp (-((sigma - gamma) * |(cell : ℝ)|)) * ‖field‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mpr
  intro point
  change ‖(originalWeight sigma gamma ell cell point.val)⁻¹ • field point‖ ≤ _
  have positive := lt_of_lt_of_le (Real.exp_pos _) (apWeight_lower admissible cell point)
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr positive.le)]
  apply mul_le_mul _ (ContinuousMap.norm_coe_le_norm field point) (norm_nonneg _) (Real.exp_pos _).le
  rw [Real.exp_neg]
  exact inv_anti₀ (Real.exp_pos _) (apWeight_lower admissible cell point)

def apUnweight {dimension : ℕ} {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) (cell : ℤ) :
    C(ClosedDisk, ComplexEuclidean dimension) →L[ℂ] C(ClosedDisk, ComplexEuclidean dimension) :=
  (apUnweightMap sigma gamma ell cell).mkContinuous (Real.exp (-((sigma - gamma) * |(cell : ℝ)|)))
    (apUnweightMap_bound admissible cell)

def apTrace {dimension grade : ℕ} {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (large : 2 ≤ grade) (cell : ℤ) : apGrade L sigma gamma ell dimension grade →L[ℂ] C(ClosedDisk, ComplexEuclidean dimension) :=
  (apUnweight admissible cell).comp (apWeightedTrace L sigma gamma ell large cell)

theorem apTrace_core {dimension grade : ℕ} {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (large : 2 ≤ grade) (cell : ℤ) (core : ℤ →₀ ClosedJet dimension) :
    apTrace admissible large cell (apFiniteInto L sigma gamma ell core) = (core cell).value := by
  change apUnweight admissible cell (apWeightedTrace L sigma gamma ell large cell (apFiniteInto L sigma gamma ell core)) = _
  rw [apWeightedTrace_core]
  apply ContinuousMap.ext
  intro point
  change (originalWeight sigma gamma ell cell point.val)⁻¹ • (apWeightedJet sigma gamma ell cell (core cell)).value point = _
  rw [apWeightedJet_value, smul_smul, inv_mul_cancel₀, one_smul]
  exact (lt_of_lt_of_le (Real.exp_pos _) (apWeight_lower admissible cell point)).ne'

theorem apTrace_bound {dimension grade : ℕ} {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (large : 2 ≤ grade) (cell : ℤ) (field : apGrade L sigma gamma ell dimension grade) :
    ‖apTrace admissible large cell field‖ ≤
      Real.exp (-((sigma - gamma) * |(cell : ℝ)|)) * apSupConstant * ‖field‖ := by
  exact (apUnweightMap_bound admissible cell _).trans
    ((mul_le_mul_of_nonneg_left (apWeightedTrace_bound L sigma gamma ell large cell field) (Real.exp_pos _).le).trans_eq
      (mul_assoc _ _ _).symm)

theorem apTrace_ext {dimension grade : ℕ} {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (large : 2 ≤ grade) (first second : apGrade L sigma gamma ell dimension grade)
    (equality : ∀ cell, apTrace admissible large cell first = apTrace admissible large cell second) : first = second := by
  apply apWeightedTrace_ext L sigma gamma ell large
  intro cell
  apply ContinuousMap.ext
  intro point
  have pointEquality := congrArg (fun value : C(ClosedDisk, ComplexEuclidean dimension) => value point) (equality cell)
  change (originalWeight sigma gamma ell cell point.val)⁻¹ • (apWeightedTrace L sigma gamma ell large cell first) point =
    (originalWeight sigma gamma ell cell point.val)⁻¹ • (apWeightedTrace L sigma gamma ell large cell second) point at pointEquality
  exact (smul_right_injective _ (inv_ne_zero (lt_of_lt_of_le (Real.exp_pos _) (apWeight_lower admissible cell point)).ne')) pointEquality

end Grad.GaugeCoefficients.Physical.RadialLedger
