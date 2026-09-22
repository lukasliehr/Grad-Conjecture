import AJB18OriginalLowGradeMembership
import AJB24OriginalLowSolutionLeibnizBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators
namespace Grad.AnnularLowOrbit
open Grad.CartesianState Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularFluxTrace
open Grad.CircularHighRegularity Grad.PhaseAlgebra

/-- A polynomially weighted original bulk coordinate is bounded by the
actual complete generator and the original bulk norm. -/
theorem lowWeighted_bulk_norm_bound (lower : ℝ) (field generator weighted : LowEnergyBulk lower)
    (order : ℕ) (actual : ∀ index, generator index = (Complex.I * (index.2.val.2 : ℂ)) ^ order • field index)
    (coefficient : LowAnnularIndex → ℝ)
    (weightedActual : ∀ index, weighted index = (coefficient index : ℂ) • field index)
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bound : ∀ index, |coefficient index| ≤ constant * (1 + |(index.2.val.2 : ℝ)| ^ order)) :
    ‖weighted‖ ≤ constant * (‖field‖ + ‖generator‖) := by
  have pointwise : ‖weighted‖ ≤ ‖constant • (lpNormFamily field + lpNormFamily generator)‖ := by
    apply lp.norm_mono (by norm_num)
    intro index
    change ‖weighted index‖ ≤ ‖constant • (‖field index‖ + ‖generator index‖)‖
    rw [weightedActual, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      norm_smul, Real.norm_of_nonneg nonnegative,
      Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),
      actual index, norm_smul, cellGeneratorFactor_norm]
    exact (mul_le_mul_of_nonneg_right (bound index) (norm_nonneg _)).trans_eq (by ring)
  apply pointwise.trans
  rw [norm_smul, Real.norm_of_nonneg nonnegative]
  exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans_eq (by rw [lpNormFamily_norm, lpNormFamily_norm])) nonnegative

/-- The literal original cell grade, on both genuine radial coordinates,
is controlled by the actual derivative vector in the complete original Y. -/
theorem lowGraph_originalCellGrade_norm (lower length : ℝ) (positive : 0 < lower)
    (field generator weighted : lowEnergyGraph lower length positive) (order : ℕ)
    (actual : ∀ (coordinate : Fin 2) (index : LowAnnularIndex),
      generator.val coordinate index = (Complex.I * (index.2.val.2 : ℂ)) ^ order • field.val coordinate index)
    (weightedActual : ∀ (coordinate : Fin 2) (index : LowAnnularIndex),
      weighted.val coordinate index = ((cellFrequency index.2.val.2 ^ order : ℝ) : ℂ) • field.val coordinate index) :
    ‖weighted‖ ≤ 2 * (2 : ℝ) ^ order * (‖field‖ + ‖generator‖) := by
  let bound := (2 : ℝ) ^ order * (‖field‖ + ‖generator‖)
  have boundNonnegative : 0 ≤ bound := mul_nonneg (by positivity) (add_nonneg (norm_nonneg _) (norm_nonneg _))
  have coordinateBound (coordinate : Fin 2) : ‖weighted.val coordinate‖ ≤ bound := by
    have estimate := lowWeighted_bulk_norm_bound lower (field.val coordinate) (generator.val coordinate)
      (weighted.val coordinate) order (actual coordinate) (fun index => cellFrequency index.2.val.2 ^ order)
      (weightedActual coordinate) (2 ^ order) (by positivity) (lowCellGrade_generator_bound order)
    apply estimate.trans
    exact mul_le_mul_of_nonneg_left
      (add_le_add (lowStoredCoordinate_bound lower length positive coordinate field)
        (lowStoredCoordinate_bound lower length positive coordinate generator)) (by positivity)
  have squared := lowEnergyGraph_norm_sq lower length positive weighted
  have first := pow_le_pow_left₀ (norm_nonneg _) (coordinateBound 0) 2
  have second := pow_le_pow_left₀ (norm_nonneg _) (coordinateBound 1) 2
  have final : ‖weighted‖ ≤ 2 * bound := by
    nlinarith only [squared, first, second, boundNonnegative, norm_nonneg weighted, sq_nonneg bound]
  exact final.trans_eq (by dsimp [bound]; ring)

end Grad.AnnularLowOrbit
