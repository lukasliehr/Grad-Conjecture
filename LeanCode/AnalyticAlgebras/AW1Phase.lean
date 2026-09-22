import RK1Algebra

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open scoped BigOperators Topology

namespace Grad.AnalyticWeights

def rate (sigma gamma radius : ℝ) : ℝ := sigma - gamma * radius

def phase (sigma gamma radius : ℝ) (cell : ℤ) : ℝ :=
  sigma * Grad.CellWeights.cellWeight cell -
    gamma * (Real.sqrt (1 + radius ^ 2 * Grad.CellWeights.cellWeight cell ^ 2) - 1)

def weight (sigma gamma radius : ℝ) (cell : ℤ) : ℝ :=
  Real.exp (phase sigma gamma radius cell)

def envelope (sigma gamma scale : ℝ) (output input : ℤ) (point : Spatial) : ℝ :=
  Grad.RepresentedKernel.radialEnvelope (fun radius => rate sigma gamma (scale * radius))
    output input point

theorem sqrt_one_add_sq_bounds (value : ℝ) (nonnegative : 0 ≤ value) :
    value ≤ Real.sqrt (1 + value ^ 2) ∧ Real.sqrt (1 + value ^ 2) ≤ value + 1 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by linarith)
  · apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · nlinarith

theorem cellWeight_bounds (cell : ℤ) :
    |(cell : ℝ)| ≤ Grad.CellWeights.cellWeight cell ∧
      Grad.CellWeights.cellWeight cell ≤ |(cell : ℝ)| + 1 := by
  simpa only [Grad.CellWeights.cellWeight, sq_abs] using
    sqrt_one_add_sq_bounds |(cell : ℝ)| (abs_nonneg _)

theorem phase_linear_bounds (sigma gamma radius : ℝ) (cell : ℤ)
    (gammaNonnegative : 0 ≤ gamma) (radiusNonnegative : 0 ≤ radius) :
    rate sigma gamma radius * Grad.CellWeights.cellWeight cell ≤ phase sigma gamma radius cell ∧
      phase sigma gamma radius cell ≤ rate sigma gamma radius * Grad.CellWeights.cellWeight cell + gamma := by
  have rootBounds := sqrt_one_add_sq_bounds (radius * Grad.CellWeights.cellWeight cell)
    (mul_nonneg radiusNonnegative (Grad.CellWeights.cellWeight_pos cell).le)
  rw [mul_pow] at rootBounds
  dsimp [phase, rate]
  constructor <;> nlinarith [mul_nonneg gammaNonnegative
    (sub_nonneg.mpr rootBounds.1), mul_nonneg gammaNonnegative (sub_nonneg.mpr rootBounds.2)]

theorem weight_pos (sigma gamma radius : ℝ) (cell : ℤ) :
    0 < weight sigma gamma radius cell := Real.exp_pos _

theorem weight_linear_bounds (sigma gamma radius : ℝ) (cell : ℤ)
    (gammaNonnegative : 0 ≤ gamma) (radiusNonnegative : 0 ≤ radius) :
    Real.exp (rate sigma gamma radius * Grad.CellWeights.cellWeight cell) ≤ weight sigma gamma radius cell ∧
      weight sigma gamma radius cell ≤ Real.exp gamma *
        Real.exp (rate sigma gamma radius * Grad.CellWeights.cellWeight cell) := by
  have bounds := phase_linear_bounds sigma gamma radius cell gammaNonnegative radiusNonnegative
  refine ⟨Real.exp_le_exp.mpr bounds.1, ?_⟩
  simpa only [Real.exp_add, mul_comm, weight] using Real.exp_le_exp.mpr bounds.2

theorem weight_absolute_bounds (sigma gamma radius : ℝ) (cell : ℤ)
    (gammaNonnegative : 0 ≤ gamma) (radiusNonnegative : 0 ≤ radius)
    (rateNonnegative : 0 ≤ rate sigma gamma radius) :
    Real.exp (rate sigma gamma radius * |(cell : ℝ)|) ≤ weight sigma gamma radius cell ∧
      weight sigma gamma radius cell ≤ Real.exp (sigma + gamma) *
        Real.exp (rate sigma gamma radius * |(cell : ℝ)|) := by
  have phaseBounds := phase_linear_bounds sigma gamma radius cell gammaNonnegative radiusNonnegative
  have cellBounds := cellWeight_bounds cell
  have rateBound : rate sigma gamma radius ≤ sigma := by
    dsimp [rate]
    exact sub_le_self _ (mul_nonneg gammaNonnegative radiusNonnegative)
  constructor
  · exact Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left cellBounds.1 rateNonnegative).trans phaseBounds.1)
  · have exponentBound :
        phase sigma gamma radius cell ≤ sigma + gamma + rate sigma gamma radius * |(cell : ℝ)| := by
      have bound := mul_le_mul_of_nonneg_left cellBounds.2 rateNonnegative
      nlinarith
    simpa only [weight, Real.exp_add] using Real.exp_le_exp.mpr exponentBound

theorem weight_one_le (sigma gamma radius : ℝ) (cell : ℤ)
    (gammaNonnegative : 0 ≤ gamma) (radiusNonnegative : 0 ≤ radius)
    (rateNonnegative : 0 ≤ rate sigma gamma radius) : 1 ≤ weight sigma gamma radius cell :=
  (Real.one_le_exp (mul_nonneg rateNonnegative (abs_nonneg _))).trans
    (weight_absolute_bounds sigma gamma radius cell gammaNonnegative radiusNonnegative rateNonnegative).1

theorem weight_ratio_bound (sigma gamma radius : ℝ) (output input : ℤ)
    (gammaNonnegative : 0 ≤ gamma) (radiusNonnegative : 0 ≤ radius)
    (rateNonnegative : 0 ≤ rate sigma gamma radius) :
    weight sigma gamma radius output / weight sigma gamma radius input ≤
      Real.exp (sigma + gamma) * Real.exp (rate sigma gamma radius * |((output - input : ℤ) : ℝ)|) := by
  apply (div_le_iff₀ (weight_pos sigma gamma radius input)).mpr
  have triangle : |(output : ℝ)| ≤ |((output - input : ℤ) : ℝ)| + |(input : ℝ)| := by
    simpa only [Int.cast_sub, sub_zero] using abs_sub_le (output : ℝ) (input : ℝ) 0
  have exponentBound := mul_le_mul_of_nonneg_left triangle rateNonnegative
  have exponentialBound := Real.exp_le_exp.mpr exponentBound
  rw [mul_add, Real.exp_add] at exponentialBound
  calc
    _ ≤ Real.exp (sigma + gamma) * Real.exp (rate sigma gamma radius * |(output : ℝ)|) :=
      (weight_absolute_bounds sigma gamma radius output gammaNonnegative radiusNonnegative rateNonnegative).2
    _ ≤ Real.exp (sigma + gamma) *
        (Real.exp (rate sigma gamma radius * |((output - input : ℤ) : ℝ)|) *
          Real.exp (rate sigma gamma radius * |(input : ℝ)|)) :=
      mul_le_mul_of_nonneg_left exponentialBound (Real.exp_pos _).le
    _ ≤ Real.exp (sigma + gamma) *
        (Real.exp (rate sigma gamma radius * |((output - input : ℤ) : ℝ)|) *
          weight sigma gamma radius input) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (weight_absolute_bounds sigma gamma radius input gammaNonnegative radiusNonnegative rateNonnegative).1
        (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by ring

theorem phase_axis (sigma gamma : ℝ) (cell : ℤ) :
    phase sigma gamma 0 cell = sigma * Grad.CellWeights.cellWeight cell := by
  simp [phase]

theorem envelope_orthogonal (sigma gamma scale : ℝ) (output input : ℤ)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (point : Spatial) :
    envelope sigma gamma scale output input (orthogonal point) =
      envelope sigma gamma scale output input point :=
  Grad.RepresentedKernel.radialEnvelope_orthogonal _ output input orthogonal point

theorem envelope_composition (sigma gamma scale : ℝ) (output middle input : ℤ)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (point : Spatial)
    (rateNonnegative : 0 ≤ rate sigma gamma (scale * ‖point‖)) :
    envelope sigma gamma scale output input point ≤
      envelope sigma gamma scale output middle point *
        envelope sigma gamma scale middle input (orthogonal point) :=
  Grad.RepresentedKernel.radialEnvelope_composition _ output middle input orthogonal point rateNonnegative

theorem envelope_one_le (sigma gamma scale : ℝ) (output input : ℤ) (point : Spatial)
    (rateNonnegative : 0 ≤ rate sigma gamma (scale * ‖point‖)) :
    1 ≤ envelope sigma gamma scale output input point :=
  Grad.RepresentedKernel.radialEnvelope_one_le _ output input point rateNonnegative

theorem physical_weight_ratio (sigma gamma scale : ℝ) (output input : ℤ) (point : Spatial)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    (rateNonnegative : 0 ≤ rate sigma gamma (scale * ‖point‖)) :
    weight sigma gamma (scale * ‖point‖) output / weight sigma gamma (scale * ‖point‖) input ≤
      Real.exp (sigma + gamma) * envelope sigma gamma scale output input point :=
  weight_ratio_bound sigma gamma (scale * ‖point‖) output input gammaNonnegative
    (mul_nonneg scaleNonnegative (norm_nonneg _)) rateNonnegative

theorem conjugated_coefficient_bound {inputDimension outputDimension : ℕ}
    (coefficient : PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension)
    (sigma gamma scale : ℝ) (output input : ℤ) (point : Spatial)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    (rateNonnegative : 0 ≤ rate sigma gamma (scale * ‖point‖)) :
    ‖(weight sigma gamma (scale * ‖point‖) output /
        weight sigma gamma (scale * ‖point‖) input) • coefficient‖ ≤
      Real.exp (sigma + gamma) * (‖coefficient‖ * envelope sigma gamma scale output input point) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos
    (weight_pos sigma gamma (scale * ‖point‖) output) (weight_pos sigma gamma (scale * ‖point‖) input))]
  calc
    _ ≤ (Real.exp (sigma + gamma) * envelope sigma gamma scale output input point) * ‖coefficient‖ :=
      mul_le_mul_of_nonneg_right (physical_weight_ratio sigma gamma scale output input point
        gammaNonnegative scaleNonnegative rateNonnegative) (norm_nonneg _)
    _ = _ := by ring

end Grad.AnalyticWeights

