import AW1Submultiplicative

noncomputable section

open Grad.PDEBootstrap Grad.GenericCarriers
open scoped BigOperators

namespace Grad.RepresentedKernel.Composition.Moments

theorem cellWeight_displacement (output middle input : ℤ) :
    Grad.CellWeights.cellWeight (output - input) ≤
      Grad.CellWeights.cellWeight (output - middle) + Grad.CellWeights.cellWeight (middle - input) := by
  simpa only [sub_add_sub_cancel] using Grad.AnalyticWeights.cellWeight_add_le (output - middle) (middle - input)

theorem allocated_displacement_power (moment : ℕ) (output middle input : ℤ) :
    Grad.CellWeights.cellWeight (output - input) ^ moment ≤
      ∑ allocation ∈ Finset.range (moment + 1),
        (moment.choose allocation : ℝ) * Grad.CellWeights.cellWeight (output - middle) ^ allocation *
          Grad.CellWeights.cellWeight (middle - input) ^ (moment - allocation) := by
  calc
    _ ≤ (Grad.CellWeights.cellWeight (output - middle) + Grad.CellWeights.cellWeight (middle - input)) ^ moment :=
      pow_le_pow_left₀ (Grad.CellWeights.cellWeight_pos _).le (cellWeight_displacement output middle input) moment
    _ = _ := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro allocation _membership
      ring

theorem allocated_envelope_comp_bound {inputDimension middleDimension outputDimension : ℕ}
    (outer : PhysicalValue middleDimension →L[ℂ] PhysicalValue outputDimension)
    (inner : PhysicalValue inputDimension →L[ℂ] PhysicalValue middleDimension)
    (width : ℝ → ℝ) (output middle input : ℤ)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (point : Spatial) (rateNonnegative : 0 ≤ width ‖point‖)
    (moment : ℕ) (outerBound innerBound : ℕ → ℝ)
    (outerEstimate : ∀ allocation ≤ moment,
      ‖outer‖ * Grad.CellWeights.cellWeight (output - middle) ^ allocation *
        radialEnvelope width output middle point ≤ outerBound allocation)
    (innerEstimate : ∀ allocation ≤ moment,
      ‖inner‖ * Grad.CellWeights.cellWeight (middle - input) ^ allocation *
        radialEnvelope width middle input (orthogonal point) ≤ innerBound allocation) :
    ‖outer.comp inner‖ * Grad.CellWeights.cellWeight (output - input) ^ moment *
        radialEnvelope width output input point ≤
      ∑ allocation ∈ Finset.range (moment + 1),
        (moment.choose allocation : ℝ) * outerBound allocation * innerBound (moment - allocation) := by
  have envelopeBound := composition_envelope_bound outer inner width output middle input orthogonal point
    rateNonnegative (‖outer‖ * radialEnvelope width output middle point)
      (‖inner‖ * radialEnvelope width middle input (orthogonal point)) le_rfl le_rfl
  calc
    _ = (‖outer.comp inner‖ * radialEnvelope width output input point) *
        Grad.CellWeights.cellWeight (output - input) ^ moment := by ring
    _ ≤ ((‖outer‖ * radialEnvelope width output middle point) *
        (‖inner‖ * radialEnvelope width middle input (orthogonal point))) *
      (∑ allocation ∈ Finset.range (moment + 1),
        (moment.choose allocation : ℝ) * Grad.CellWeights.cellWeight (output - middle) ^ allocation *
          Grad.CellWeights.cellWeight (middle - input) ^ (moment - allocation)) :=
      mul_le_mul envelopeBound (allocated_displacement_power moment output middle input)
        (pow_nonneg (Grad.CellWeights.cellWeight_pos _).le _)
        (mul_nonneg (mul_nonneg (norm_nonneg _) (radialEnvelope_pos _ _ _ _).le)
          (mul_nonneg (norm_nonneg _) (radialEnvelope_pos _ _ _ _).le))
    _ = ∑ allocation ∈ Finset.range (moment + 1),
        (moment.choose allocation : ℝ) *
          ((‖outer‖ * Grad.CellWeights.cellWeight (output - middle) ^ allocation *
            radialEnvelope width output middle point) *
          (‖inner‖ * Grad.CellWeights.cellWeight (middle - input) ^ (moment - allocation) *
            radialEnvelope width middle input (orthogonal point))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro allocation _membership
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro allocation membership
      have allocationBound : allocation ≤ moment := Nat.le_of_lt_succ (Finset.mem_range.mp membership)
      have otherBound : moment - allocation ≤ moment := Nat.sub_le _ _
      have outerNonnegative : 0 ≤ ‖outer‖ * Grad.CellWeights.cellWeight (output - middle) ^ allocation *
          radialEnvelope width output middle point :=
        mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (Grad.CellWeights.cellWeight_pos _).le _))
          (radialEnvelope_pos _ _ _ _).le
      have innerNonnegative : 0 ≤ ‖inner‖ * Grad.CellWeights.cellWeight (middle - input) ^ (moment - allocation) *
          radialEnvelope width middle input (orthogonal point) :=
        mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (Grad.CellWeights.cellWeight_pos _).le _))
          (radialEnvelope_pos _ _ _ _).le
      have productBound := mul_le_mul (outerEstimate allocation allocationBound)
        (innerEstimate (moment - allocation) otherBound) innerNonnegative
        (outerNonnegative.trans (outerEstimate allocation allocationBound))
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left productBound (Nat.cast_nonneg (moment.choose allocation))

end Grad.RepresentedKernel.Composition.Moments
