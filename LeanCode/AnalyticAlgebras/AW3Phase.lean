import AW3Spectral
import AW3Tensors

noncomputable section

open Grad.PDEBootstrap Grad.AnalyticWeights.Calculus
open scoped ContDiff

namespace Grad.AnalyticWeights.Higher

theorem physicalPhase_profile (sigma gamma scale : ℝ) (cell : ℤ) :
    physicalPhase sigma gamma scale cell =
      (fun _ : Spatial => sigma * Grad.CellWeights.cellWeight cell) -
        gamma • (fun source => profile ((scale * Grad.CellWeights.cellWeight cell) • source)) := by
  funext point
  rw [physicalPhase_formula]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, profile, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    radicand]
  ring_nf

theorem physicalPhase_iterated_scaling (sigma gamma scale : ℝ) (cell : ℤ)
    (rank : ℕ) (positiveRank : 1 ≤ rank) (point : Spatial) :
    iteratedFDeriv ℝ rank (physicalPhase sigma gamma scale cell) point =
      (-gamma * scale ^ rank) • spectralJet rank scale point (Grad.CellWeights.cellWeight cell) := by
  have composed : ContDiff ℝ ∞ (fun source : Spatial =>
      profile ((scale * Grad.CellWeights.cellWeight cell) • source)) :=
    profile_contDiff.comp
      ((contDiff_const : ContDiff ℝ ∞ (fun _ : Spatial => scale * Grad.CellWeights.cellWeight cell)).smul
        (contDiff_id : ContDiff ℝ ∞ (fun source : Spatial => source)))
  rw [physicalPhase_profile]
  change iteratedFDeriv ℝ rank ((fun _ : Spatial => sigma * Grad.CellWeights.cellWeight cell) -
      fun source => gamma • profile ((scale * Grad.CellWeights.cellWeight cell) • source)) point = _
  rw [iteratedFDeriv_sub_apply contDiff_const.contDiffAt
    ((composed.const_smul gamma).of_le (by exact_mod_cast le_top)).contDiffAt,
    iteratedFDeriv_const_of_ne (by omega)]
  simp only [Pi.zero_apply, zero_sub]
  change -iteratedFDeriv ℝ rank
      (gamma • fun source : Spatial => profile ((scale * Grad.CellWeights.cellWeight cell) • source)) point = _
  rw [iteratedFDeriv_const_smul_apply (composed.of_le (by exact_mod_cast le_top)).contDiffAt,
    iteratedFDeriv_comp_const_smul _ (profile_contDiff.of_le (by exact_mod_cast le_top))]
  simp only [spectralJet, smul_smul, mul_pow, ← neg_smul, mul_assoc]
  congr 1
  · ring
  · rw [mul_comm scale]

theorem spectralJet_cell_difference_bound (rank : ℕ) (positiveRank : 1 ≤ rank) (scale : ℝ)
    (point : Spatial) (output input : ℤ) :
    ‖spectralJet rank scale point (Grad.CellWeights.cellWeight output) -
      spectralJet rank scale point (Grad.CellWeights.cellWeight input)‖ ≤
      (spectralConstant rank *
        (Grad.CellWeights.cellWeight input + |((output - input : ℤ) : ℝ)|) ^ (rank - 1)) *
          |((output - input : ℤ) : ℝ)| := by
  have nonnegative : 0 ≤ spectralConstant rank *
      (Grad.CellWeights.cellWeight input + |((output - input : ℤ) : ℝ)|) ^ (rank - 1) :=
    mul_nonneg (spectralConstant_nonnegative _)
      (pow_nonneg (add_nonneg (Grad.CellWeights.cellWeight_pos input).le (abs_nonneg _)) _)
  rcases le_total (Grad.CellWeights.cellWeight input) (Grad.CellWeights.cellWeight output) with ordered | ordered
  · apply (spectralJet_ordered_segment_bound rank positiveRank scale point _ _ _
      (Grad.CellWeights.cellWeight_pos input) ordered (cellGoal output input).2).trans
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (cell_lipschitz output input)) nonnegative
  · rw [norm_sub_rev]
    apply (spectralJet_ordered_segment_bound rank positiveRank scale point _ _ _
      (Grad.CellWeights.cellWeight_pos output) ordered (le_add_of_nonneg_right (abs_nonneg _))).trans
    apply mul_le_mul_of_nonneg_left _ nonnegative
    exact (le_abs_self _).trans (by
      simpa [abs_sub_comm] using cell_lipschitz output input)

theorem physicalPhase_iterated_norm_bound (sigma gamma scale : ℝ) (cell : ℤ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    (rank : ℕ) (positiveRank : 1 ≤ rank) (point : Spatial) :
    ‖iteratedFDeriv ℝ rank (physicalPhase sigma gamma scale cell) point‖ ≤
      profileConstant rank * gamma * scale ^ rank * Grad.CellWeights.cellWeight cell ^ rank := by
  rw [physicalPhase_iterated_scaling sigma gamma scale cell rank positiveRank point,
    spectralJet, norm_smul, norm_smul, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_nonneg gammaNonnegative, abs_of_nonneg (pow_nonneg scaleNonnegative _),
    Real.norm_of_nonneg (pow_nonneg (Grad.CellWeights.cellWeight_pos cell).le _)]
  calc
    _ ≤ (gamma * scale ^ rank) * (Grad.CellWeights.cellWeight cell ^ rank * profileConstant rank) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (profile_iterated_norm_le rank positiveRank _)
          (pow_nonneg (Grad.CellWeights.cellWeight_pos cell).le _))
        (mul_nonneg gammaNonnegative (pow_nonneg scaleNonnegative _))
    _ = _ := by ring

theorem phaseDifference_iterated_norm_bound (sigma gamma scale : ℝ) (output input : ℤ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    (rank : ℕ) (positiveRank : 1 ≤ rank) (point : Spatial) :
    ‖iteratedFDeriv ℝ rank (phaseDifference sigma gamma scale output input) point‖ ≤
      spectralConstant rank * gamma * scale ^ rank * |((output - input : ℤ) : ℝ)| *
        (Grad.CellWeights.cellWeight input + |((output - input : ℤ) : ℝ)|) ^ (rank - 1) := by
  change ‖iteratedFDeriv ℝ rank (physicalPhase sigma gamma scale output - physicalPhase sigma gamma scale input) point‖ ≤ _
  rw [iteratedFDeriv_sub_apply
    ((physicalPhase_contDiff sigma gamma scale output).of_le (by exact_mod_cast le_top)).contDiffAt
    ((physicalPhase_contDiff sigma gamma scale input).of_le (by exact_mod_cast le_top)).contDiffAt,
    physicalPhase_iterated_scaling sigma gamma scale output rank positiveRank point,
    physicalPhase_iterated_scaling sigma gamma scale input rank positiveRank point,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_nonneg gammaNonnegative, abs_of_nonneg (pow_nonneg scaleNonnegative _)]
  calc
    _ ≤ (gamma * scale ^ rank) * ((spectralConstant rank *
        (Grad.CellWeights.cellWeight input + |((output - input : ℤ) : ℝ)|) ^ (rank - 1)) *
          |((output - input : ℤ) : ℝ)|) :=
      mul_le_mul_of_nonneg_left (spectralJet_cell_difference_bound rank positiveRank scale point output input)
        (mul_nonneg gammaNonnegative (pow_nonneg scaleNonnegative _))
    _ = _ := by ring

end Grad.AnalyticWeights.Higher
