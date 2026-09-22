import AW3Profile
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Grad.PDEBootstrap Grad.AnalyticWeights.Calculus
open scoped ContDiff BigOperators Topology

namespace Grad.AnalyticWeights.Higher

theorem cell_lipschitz (output input : ℤ) :
    |Grad.CellWeights.cellWeight output - Grad.CellWeights.cellWeight input| ≤ |((output - input : ℤ) : ℝ)| := by
  have outputPositive := (Grad.CellWeights.cellWeight_pos output).le
  have inputPositive := (Grad.CellWeights.cellWeight_pos input).le
  have productBound : 1 + (output : ℝ) * (input : ℝ) ≤
      Grad.CellWeights.cellWeight output * Grad.CellWeights.cellWeight input := by
    apply (le_abs_self _).trans
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg outputPositive inputPositive)).mp
    rw [sq_abs, mul_pow, Grad.CellBinomial.cellWeight_sq, Grad.CellBinomial.cellWeight_sq]
    nlinarith [sq_nonneg ((output : ℝ) - (input : ℝ))]
  apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
  rw [sq_abs, sq_abs, Int.cast_sub]
  nlinarith [Grad.CellBinomial.cellWeight_sq output, Grad.CellBinomial.cellWeight_sq input]

theorem cellGoal : CellGoal := by
  intro output input
  refine ⟨cell_lipschitz output input, ?_⟩
  have bound := (le_abs_self _).trans (cell_lipschitz output input)
  linarith

theorem profile_iterated_norm_le (rank : ℕ) (positiveRank : 1 ≤ rank) (point : Spatial) :
    ‖iteratedFDeriv ℝ rank profile point‖ ≤ profileConstant rank := by
  apply (profile_iterated_norm_decay rank positiveRank point).trans
  exact div_le_self (profileConstant_nonnegative _) (one_le_pow₀
    (Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg ‖point‖])))

theorem profile_radial_iterated_norm_le (rank : ℕ) (positiveRank : 1 ≤ rank) (point : Spatial) :
    ‖point‖ * ‖iteratedFDeriv ℝ (rank + 1) profile point‖ ≤ profileConstant (rank + 1) := by
  apply (profile_radial_iterated_norm_decay rank positiveRank point).trans
  exact div_le_self (profileConstant_nonnegative _) (one_le_pow₀
    (Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg ‖point‖])))

def spectralJet (rank : ℕ) (scale : ℝ) (point : Spatial) (frequency : ℝ) : Spatial [×rank]→L[ℝ] ℝ :=
  frequency ^ rank • iteratedFDeriv ℝ rank profile (frequency • (scale • point))

def spectralJetDerivative (rank : ℕ) (scale : ℝ) (point : Spatial) (frequency : ℝ) : Spatial [×rank]→L[ℝ] ℝ :=
  ((rank : ℝ) * frequency ^ (rank - 1)) • iteratedFDeriv ℝ rank profile (frequency • (scale • point)) +
    frequency ^ rank • (fderiv ℝ (iteratedFDeriv ℝ rank profile) (frequency • (scale • point)) (scale • point))

def spectralConstant (rank : ℕ) : ℝ := (rank : ℝ) * profileConstant rank + profileConstant (rank + 1)

theorem spectralConstant_nonnegative (rank : ℕ) : 0 ≤ spectralConstant rank := by
  exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (profileConstant_nonnegative _)) (profileConstant_nonnegative _)

theorem spectralJet_hasDerivAt (rank : ℕ) (scale : ℝ) (point : Spatial) (frequency : ℝ) :
    HasDerivAt (spectralJet rank scale point) (spectralJetDerivative rank scale point frequency) frequency := by
  have smooth := (profile_contDiff.contDiffAt (x := frequency • (scale • point))).differentiableAt_iteratedFDeriv
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl rank)
  change HasDerivAt (fun source : ℝ => source ^ rank •
    iteratedFDeriv ℝ rank profile (source • (scale • point))) _ frequency
  apply (((hasDerivAt_id frequency).pow rank).smul
    (smooth.hasFDerivAt.comp_hasDerivAt frequency ((hasDerivAt_id frequency).smul_const (scale • point)))).congr_deriv
  simp only [id_eq, Pi.pow_apply, Function.comp_apply, one_smul, mul_one, spectralJetDerivative]
  exact add_comm _ _

theorem spectralJetDerivative_bound (rank : ℕ) (positiveRank : 1 ≤ rank) (scale : ℝ)
    (point : Spatial) (frequency : ℝ) (positiveFrequency : 0 < frequency) :
    ‖spectralJetDerivative rank scale point frequency‖ ≤ spectralConstant rank * frequency ^ (rank - 1) := by
  have firstBound := profile_iterated_norm_le rank positiveRank (frequency • (scale • point))
  have radialBound := profile_radial_iterated_norm_le rank positiveRank (frequency • (scale • point))
  have powerSplit : frequency ^ rank = frequency ^ (rank - 1) * frequency := by
    rw [← pow_succ, Nat.sub_add_cancel positiveRank]
  have derivativeNorm : ‖fderiv ℝ (iteratedFDeriv ℝ rank profile) (frequency • (scale • point))‖ =
      ‖iteratedFDeriv ℝ (rank + 1) profile (frequency • (scale • point))‖ := norm_fderiv_iteratedFDeriv
  have normScaled : ‖frequency • (scale • point)‖ = frequency * ‖scale • point‖ := by
    rw [norm_smul, Real.norm_of_nonneg positiveFrequency.le]
  rw [normScaled] at radialBound
  unfold spectralJetDerivative
  calc
    _ ≤ ‖((rank : ℝ) * frequency ^ (rank - 1)) •
          iteratedFDeriv ℝ rank profile (frequency • (scale • point))‖ +
        ‖frequency ^ rank •
          (fderiv ℝ (iteratedFDeriv ℝ rank profile) (frequency • (scale • point)) (scale • point))‖ := norm_add_le _ _
    _ ≤ ((rank : ℝ) * frequency ^ (rank - 1)) * profileConstant rank +
        frequency ^ rank * (‖iteratedFDeriv ℝ (rank + 1) profile (frequency • (scale • point))‖ * ‖scale • point‖) := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      exact add_le_add (mul_le_mul_of_nonneg_left firstBound (by positivity))
        (mul_le_mul_of_nonneg_left (by rw [← derivativeNorm]; exact ContinuousLinearMap.le_opNorm _ _) (by positivity))
    _ ≤ ((rank : ℝ) * frequency ^ (rank - 1)) * profileConstant rank +
        frequency ^ (rank - 1) * profileConstant (rank + 1) := by
      apply add_le_add le_rfl
      rw [powerSplit]
      calc
        _ = frequency ^ (rank - 1) * ((frequency * ‖scale • point‖) *
            ‖iteratedFDeriv ℝ (rank + 1) profile (frequency • (scale • point))‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left radialBound (by positivity)
    _ = _ := by unfold spectralConstant; ring

theorem spectralJet_ordered_segment_bound (rank : ℕ) (positiveRank : 1 ≤ rank) (scale : ℝ)
    (point : Spatial) (first second upper : ℝ) (firstPositive : 0 < first)
    (ordered : first ≤ second) (upperBound : second ≤ upper) :
    ‖spectralJet rank scale point second - spectralJet rank scale point first‖ ≤
      (spectralConstant rank * upper ^ (rank - 1)) * (second - first) := by
  apply norm_image_sub_le_of_norm_deriv_le_segment'
    (fun frequency _ => (spectralJet_hasDerivAt rank scale point frequency).hasDerivWithinAt)
    (fun frequency inside => ?_) second ⟨ordered, le_rfl⟩
  apply (spectralJetDerivative_bound rank positiveRank scale point frequency
    (firstPositive.trans_le inside.1)).trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (firstPositive.trans_le inside.1).le
    (inside.2.le.trans upperBound) _) (spectralConstant_nonnegative _)

end Grad.AnalyticWeights.Higher
