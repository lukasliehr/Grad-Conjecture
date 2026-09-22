import ACE19LaplacianSeriesPassage

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.NonlinearDivision (IsRotationInvariant laplacianJet)

theorem volterraResolvent_equation {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (parameter : ℝ) (field : ClosedJet dimension) (radial : IsRotationInvariant field) :
    laplacianJet (coordinateMultiplyJet (mode : ℝ) (volterraResolventJet parameter field)) =
      coordinateMultiplyJet (mode : ℝ) field +
        (parameter : ℂ) • coordinateMultiplyJet (mode : ℝ) (volterraResolventJet parameter field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  let series (count : ℕ) : ComplexEuclidean dimension := ((parameter ^ count : ℝ) : ℂ) •
    (coordinateMultiplyJet (mode : ℝ) (volterraPower count field)).value point
  have values := (ContinuousMap.evalCLM ℝ point).hasSum (volterraResolventJet_value_hasSum parameter field)
  simp only [ContinuousMap.evalCLM_apply] at values
  have scaled := (values.const_smul (signedComplexCoordinate (mode : ℝ) point.val)).const_smul (parameter : ℂ)
  have tail : HasSum (fun count => series (count + 1))
      ((parameter : ℂ) • (coordinateMultiplyJet (mode : ℝ) (volterraResolventJet parameter field)).value point) := by
    convert scaled using 1
    · funext count
      dsimp only [series, Function.comp_apply]
      rw [coordinateMultiplyJet_value, closedJet_value_smul, ContinuousMap.smul_apply,
        pow_succ, Complex.ofReal_mul]
      simp only [smul_smul]
      congr 1
      ring
    · rw [coordinateMultiplyJet_value]
  have whole := (hasSum_nat_add_iff 1).mp tail
  have equationSeries := volterraResolvent_laplacian_hasSum mode center parameter field radial point
  have identity := equationSeries.unique whole
  simp only [Finset.sum_range_one, series, pow_zero, Complex.ofReal_one, one_smul, volterraPower_zero] at identity
  rw [closedJet_value_add, ContinuousMap.add_apply, closedJet_value_smul, ContinuousMap.smul_apply]
  exact identity.trans (add_comm _ _)

end Grad.ActualCenterVolterra
