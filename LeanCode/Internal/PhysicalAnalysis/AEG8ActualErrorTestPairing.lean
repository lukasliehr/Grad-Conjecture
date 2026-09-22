import AEG7ActualReconstructionEnergyInput

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularTiltedReference Grad.AnnularKernelL2

/-- The completed bulk inner product is its literal all-mode radial integral.
The test is in the first slot, so the pairing is complex-linear in the field. -/
theorem physicalBulk_inner {dimension : ℕ} (lower : ℝ)
    (test field : DivisionRow dimension lower) :
    inner ℂ test field = ∑' mode : ℤ × ℤ,
      ∫ radius, inner ℂ (test mode radius) (field mode radius) ∂volume.restrict (Icc lower 1) := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro mode
  exact L2.inner_def (test mode) (field mode)

/-- Actual reconstruction errors paired with the physical opposite-derivative
energy test; the constant is independent of the inner radius. This is a
coefficient-error estimate, not yet the eliminated current high form. -/
theorem actualReconstruction_energyTest_bound (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
        (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
        (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
        (state : AnnularReconstructionState parameters L compact) (flux : DivisionRow 1 lower)
        (field test : annularEnergySpace lower L positive),
      ‖inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)
        (normalizedCovariantErrorAction parameters L compact lower positive bounded state power
          (highSevenEnergyPacket lower L positive (flux, field)))‖ +
      ‖inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)
        (normalizedRotatedErrorAction parameters L compact lower positive bounded state power
          (highSevenEnergyPacket lower L positive (flux, field)))‖ ≤
      constant * state.errorBudget power * (‖flux‖ + (2 + 2 * |L|) * ‖field‖) * ‖test‖ := by
  obtain ⟨constant, nonnegative, errorBound⟩ := highSevenEnergyPacket_actualError_bound parameters L compact power
  refine ⟨5 * constant, mul_nonneg (by norm_num) nonnegative, ?_⟩
  intro lower positive bounded lengthPositive widthHalf widthLength state flux field test
  let testPacket := highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test
  let first := normalizedCovariantErrorAction parameters L compact lower positive bounded state power
    (highSevenEnergyPacket lower L positive (flux, field))
  let second := normalizedRotatedErrorAction parameters L compact lower positive bounded state power
    (highSevenEnergyPacket lower L positive (flux, field))
  have both : ‖first‖ + ‖second‖ ≤ constant * state.errorBudget power *
      (‖flux‖ + (2 + 2 * |L|) * ‖field‖) := errorBound lower positive bounded state flux field
  have testBound : ‖testPacket‖ ≤ 5 * ‖test‖ :=
    highEnergyTestPacket_bound parameters lower L positive lengthPositive widthHalf widthLength test
  calc
    _ ≤ ‖testPacket‖ * ‖first‖ + ‖testPacket‖ * ‖second‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ = ‖testPacket‖ * (‖first‖ + ‖second‖) := by ring
    _ ≤ (5 * ‖test‖) * (constant * state.errorBudget power *
        (‖flux‖ + (2 + 2 * |L|) * ‖field‖)) :=
      mul_le_mul testBound both (add_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ = _ := by ring

end Grad.AnnularCurrentEnergy
