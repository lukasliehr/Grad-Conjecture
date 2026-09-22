import AW1Submultiplicative

noncomputable section

open Grad.PDEBootstrap Grad.GenericCarriers

namespace Grad.AnalyticWeights

theorem rate_nonnegative_on_unit_interval (sigma gamma radius : ℝ)
    (gammaNonnegative : 0 ≤ gamma) (gammaBound : gamma ≤ sigma) (radiusBound : radius ≤ 1) :
    0 ≤ rate sigma gamma radius := by
  have bound := mul_le_mul_of_nonneg_left radiusBound gammaNonnegative
  dsimp [rate]
  nlinarith

theorem rate_nonnegative_on_disk (sigma gamma scale radius : ℝ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    (widthBound : gamma * (scale * radius) ≤ sigma) (point : Spatial)
    (membership : point ∈ Metric.closedBall (0 : Spatial) radius) :
    0 ≤ rate sigma gamma (scale * ‖point‖) := by
  have pointBound : ‖point‖ ≤ radius := by simpa only [Metric.mem_closedBall, dist_zero_right] using membership
  exact sub_nonneg.mpr ((mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left pointBound scaleNonnegative) gammaNonnegative).trans widthBound)

theorem envelope_inward_dilation (sigma gamma scale dilation : ℝ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    (dilationNonnegative : 0 ≤ dilation) (dilationBound : dilation ≤ 1)
    (output input : ℤ) (point : Spatial) :
    envelope sigma gamma scale output input point ≤
      envelope sigma gamma scale output input (dilation • point) := by
  unfold envelope Grad.RepresentedKernel.radialEnvelope
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg dilationNonnegative]
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  dsimp [rate]
  have gap := mul_nonneg (sub_nonneg.mpr dilationBound)
    (mul_nonneg gammaNonnegative (mul_nonneg scaleNonnegative (norm_nonneg point)))
  nlinarith

theorem weight_orthogonal (sigma gamma scale : ℝ) (cell : ℤ)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (point : Spatial) :
    weight sigma gamma (scale * ‖orthogonal point‖) cell = weight sigma gamma (scale * ‖point‖) cell := by
  rw [orthogonal.norm_map]

theorem paper_phase_formula (sigma gamma radius : ℝ) (cell : ℤ) :
    phase sigma gamma radius cell =
      sigma * Real.sqrt (1 + (cell : ℝ) ^ 2) -
        gamma * (Real.sqrt (1 + radius ^ 2 * (1 + (cell : ℝ) ^ 2)) - 1) := by
  rw [phase, Grad.CellBinomial.cellWeight_sq]
  rfl

theorem paper_phase_axis (sigma gamma scale : ℝ) (cell : ℤ) :
    phase sigma gamma (scale * ‖(0 : Spatial)‖) cell = sigma * Grad.CellWeights.cellWeight cell ∧
      weight sigma gamma (scale * ‖(0 : Spatial)‖) cell = Real.exp (sigma * Grad.CellWeights.cellWeight cell) := by
  constructor <;> simp [weight, phase_axis]

theorem paper_weight_submultiplicative (sigma gamma radius : ℝ) (first second : ℤ)
    (positiveGamma : 0 < gamma) (gammaBound : gamma < sigma)
    (radiusNonnegative : 0 ≤ radius) (radiusBound : radius ≤ 1) :
    weight sigma gamma radius (first + second) ≤
      weight sigma gamma radius first * weight sigma gamma radius second :=
  weight_submultiplicative sigma gamma radius first second positiveGamma.le radiusNonnegative
    (rate_nonnegative_on_unit_interval sigma gamma radius positiveGamma.le gammaBound.le radiusBound)

theorem original_width_ratio (sigma gamma scale radius : ℝ) (output input : ℤ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    (widthBound : gamma * (scale * radius) ≤ sigma) (point : Spatial)
    (membership : point ∈ Metric.closedBall (0 : Spatial) radius) :
    weight sigma gamma (scale * ‖point‖) output / weight sigma gamma (scale * ‖point‖) input ≤
      Real.exp (sigma + gamma) *
        Real.exp ((sigma - gamma * (scale * ‖point‖)) * |((output - input : ℤ) : ℝ)|) :=
  physical_weight_ratio sigma gamma scale output input point gammaNonnegative scaleNonnegative
    (rate_nonnegative_on_disk sigma gamma scale radius gammaNonnegative scaleNonnegative widthBound point membership)

theorem actual_conjugated_coefficient {inputDimension outputDimension : ℕ}
    (coefficient : PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension)
    (sigma gamma scale : ℝ) (output input : ℤ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (point : Spatial)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    (rateNonnegative : 0 ≤ rate sigma gamma (scale * ‖point‖))
    (majorant : ℝ) (bounded : ‖coefficient‖ * envelope sigma gamma scale output input point ≤ majorant) :
    ‖(weight sigma gamma (scale * ‖point‖) output /
        weight sigma gamma (scale * ‖orthogonal point‖) input) • coefficient‖ ≤
      Real.exp (sigma + gamma) * majorant := by
  rw [weight_orthogonal]
  exact (conjugated_coefficient_bound coefficient sigma gamma scale output input point
    gammaNonnegative scaleNonnegative rateNonnegative).trans
      (mul_le_mul_of_nonneg_left bounded (Real.exp_pos _).le)

theorem original_envelope_composition {inputDimension middleDimension outputDimension : ℕ}
    (outer : PhysicalValue middleDimension →L[ℂ] PhysicalValue outputDimension)
    (inner : PhysicalValue inputDimension →L[ℂ] PhysicalValue middleDimension)
    (sigma gamma scale : ℝ) (output middle input : ℤ)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (point : Spatial)
    (rateNonnegative : 0 ≤ rate sigma gamma (scale * ‖point‖)) (outerBound innerBound : ℝ)
    (outerEstimate : ‖outer‖ * envelope sigma gamma scale output middle point ≤ outerBound)
    (innerEstimate : ‖inner‖ * envelope sigma gamma scale middle input (orthogonal point) ≤ innerBound) :
    ‖outer.comp inner‖ * envelope sigma gamma scale output input point ≤ outerBound * innerBound :=
  Grad.RepresentedKernel.composition_envelope_bound outer inner
    (fun radius => rate sigma gamma (scale * radius)) output middle input orthogonal point
      rateNonnegative outerBound innerBound outerEstimate innerEstimate

end Grad.AnalyticWeights
