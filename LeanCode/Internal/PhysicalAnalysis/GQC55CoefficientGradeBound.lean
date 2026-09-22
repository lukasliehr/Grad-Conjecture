import GQC54ActualInversePolynomial

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity Grad.GaugeCoefficients.Physical.Allocation

def embeddedTopSlot {low high : ℕ} (ordered : low ≤ high) (index : DerivativeIndex low) : RegularitySlot high where
  first := ⟨index.val.1, by have := index.val.1.isLt; omega⟩
  second := ⟨index.val.2, by have := index.val.2.isLt; omega⟩
  moment := ⟨low - derivativeOrder index, by omega⟩
  total_le := by have := index.property; change (index.val.1 : ℕ) + (index.val.2 : ℕ) + (low - derivativeOrder index) ≤ high; unfold derivativeOrder; omega

theorem coherent_embedded_slot {L sigma gamma ell : ℝ} {input output low high : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (ordered : low ≤ high) (index : DerivativeIndex low) (cell : ℤ) :
    slotCoordinate (family high) (embeddedTopSlot ordered index) cell = weightedDerivative (family low) cell index := by
  apply ContinuousMap.ext
  intro point
  rw [slotCoordinate_apply, weighted_derivative_literal]
  rw [coherent high low (slotDerivativeIndex (embeddedTopSlot ordered index)) index rfl cell point]
  rfl

theorem coherent_coefficient_grade_bound {L sigma gamma ell : ℝ} {input output low high : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (ordered : low ≤ high) :
    ‖family low‖ ≤ (Fintype.card (DerivativeIndex low) : ℝ) * ‖family high‖ := by
  have coordinateBound (index : DerivativeIndex low) :
      (∑' cell : ℤ, ‖weightedDerivative (family low) cell index‖) ≤ ‖family high‖ := by
    have bound := slotNorm_le_norm (family high) (embeddedTopSlot ordered index)
    change (∑' cell : ℤ, ‖slotCoordinate (family high) (embeddedTopSlot ordered index) cell‖) ≤ _ at bound
    simpa only [coherent_embedded_slot family coherent] using bound
  calc
    ‖family low‖ = ∑ index : DerivativeIndex low, ∑' cell : ℤ, ‖weightedDerivative (family low) cell index‖ := by
      rw [coefficient_norm_formula]
      exact Summable.tsum_finsetSum (fun index _ => coordinate_norm_summable (family low).val index)
    _ ≤ ∑ _index : DerivativeIndex low, ‖family high‖ := Finset.sum_le_sum (fun index _ => coordinateBound index)
    _ = _ := finite_real_sum_const _

end Grad.GaugeCoefficients.Physical.Compensated
