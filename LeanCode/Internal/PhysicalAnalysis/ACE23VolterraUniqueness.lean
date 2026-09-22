import ACE22PinnedRadialInverse

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearRange Grad.NonlinearQuotientBounds

theorem volterraJet_smul {dimension : ℕ} (scalar : ℂ) (field : ClosedJet dimension) :
    volterraJet (scalar • field) = scalar • volterraJet field :=
  (volterraLinear dimension).map_smul scalar field

theorem volterra_homogeneous_iterate {dimension : ℕ} (parameter : ℝ) (field : ClosedJet dimension)
    (equation : field = (parameter : ℂ) • volterraJet field) (count : ℕ) :
    field = ((parameter ^ count : ℝ) : ℂ) • volterraPower count field := by
  induction count with
  | zero => simp only [pow_zero, Complex.ofReal_one, one_smul, volterraPower_zero]
  | succ count previous =>
    calc
      field = (parameter : ℂ) • volterraJet field := equation
      _ = (parameter : ℂ) • volterraJet (((parameter ^ count : ℝ) : ℂ) • volterraPower count field) :=
        congrArg (fun jet => (parameter : ℂ) • volterraJet jet) previous
      _ = ((parameter ^ (count + 1) : ℝ) : ℂ) • volterraPower (count + 1) field := by
        rw [volterraJet_smul, smul_smul, pow_succ, Complex.ofReal_mul]
        change ((parameter : ℂ) * ((parameter ^ count : ℝ) : ℂ)) • _ =
          (((parameter ^ count : ℝ) : ℂ) * (parameter : ℂ)) • _
        rw [mul_comm]
        rfl

/-- Factorial decay forces every smooth homogeneous Volterra solution to
vanish. This includes a zero parameter without cancellation or division. -/
theorem volterra_homogeneous_zero {dimension : ℕ} (parameter : ℝ) (field : ClosedJet dimension)
    (equation : field = (parameter : ℂ) • volterraJet field) : field = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have bounded (count : ℕ) : ‖field.value point‖ ≤
      |parameter| * volterraSeriesMajorant parameter field 0 count := by
    have identity := congrArg (fun jet : ClosedJet dimension => jet.value point)
      (volterra_homogeneous_iterate parameter field equation (count + 1))
    rw [identity, closedJet_value_smul, ContinuousMap.smul_apply, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_pow]
    have estimate := volterraPower_operator_bound 0 (count + 1) 0 le_rfl field point
    rw [norm_iteratedFDeriv_zero, volterraPowerValue_value] at estimate
    calc
      _ ≤ |parameter| ^ (count + 1) * volterraPowerMajorant 0 (count + 1) field :=
        mul_le_mul_of_nonneg_left estimate (pow_nonneg (abs_nonneg _) _)
      _ = _ := by unfold volterraSeriesMajorant; rw [pow_succ]; ring
  have limit := ((volterraSeriesMajorant_summable parameter field 0).mul_left |parameter|).tendsto_atTop_zero
  have nonpositive : ‖field.value point‖ ≤ 0 := ge_of_tendsto limit (Filter.Eventually.of_forall bounded)
  have zero : field.value point = 0 := norm_eq_zero.mp (le_antisymm nonpositive (norm_nonneg _))
  simpa only [closedJet_value_zero, ContinuousMap.zero_apply] using zero

end Grad.ActualCenterVolterra
