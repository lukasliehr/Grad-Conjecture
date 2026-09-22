import ACE11VolterraSeriesMajorant
import ProductSeriesL2

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct

/-- The actual convergent Volterra resolvent, for every real parameter. -/
def volterraResolventJet {dimension : ℕ} (parameter : ℝ) (field : ClosedJet dimension) : ClosedJet dimension :=
  smoothSeriesClosedJet (volterraSeriesTerm parameter field) (volterraSeriesTerm_smooth parameter field)
    (volterraSeriesMajorant parameter field) (volterraSeriesMajorant_summable parameter field)
    (volterraSeriesTerm_operator_bound parameter field)

theorem volterraResolventJet_value {dimension : ℕ} (parameter : ℝ) (field : ClosedJet dimension)
    (point : ClosedDisk) :
    (volterraResolventJet parameter field).value point =
      ∑' count : ℕ, parameter ^ count • (volterraPower (count + 1) field).value point := by
  rw [volterraResolventJet, smoothSeriesClosedJet_value]
  apply tsum_congr
  intro count
  exact congrArg (fun value => parameter ^ count • value) (volterraPowerValue_value _ _ point)

theorem volterraSeriesTerm_jet {dimension : ℕ} (parameter : ℝ) (field : ClosedJet dimension) (count : ℕ) :
    globalClosedJet (volterraSeriesTerm parameter field count) (volterraSeriesTerm_smooth parameter field count) =
      ((parameter ^ count : ℝ) : ℂ) • volterraPower (count + 1) field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change parameter ^ count • volterraPowerValue (count + 1) field point.val =
    ((parameter ^ count : ℝ) : ℂ) • (volterraPower (count + 1) field).value point
  rw [volterraPowerValue_value, Complex.coe_smul]

/-- Convergence holds for the literal prescribed derivative on the entire
closed disk, including the center and the circle. -/
theorem volterraResolventJet_derivative_hasSum {dimension order : ℕ} (parameter : ℝ)
    (field : ClosedJet dimension) (word : CartesianWord order) :
    HasSum (fun count : ℕ => closedDerivative
      (((parameter ^ count : ℝ) : ℂ) • volterraPower (count + 1) field) order word)
      (closedDerivative (volterraResolventJet parameter field) order word) := by
  have series := smoothSeriesClosedJet_derivative_hasSum
    (volterraSeriesTerm parameter field) (volterraSeriesTerm_smooth parameter field)
    (volterraSeriesMajorant parameter field) (volterraSeriesMajorant_summable parameter field)
    (volterraSeriesTerm_operator_bound parameter field) word
  simpa only [volterraSeriesTerm_jet, volterraResolventJet] using series

theorem volterraResolventJet_value_hasSum {dimension : ℕ} (parameter : ℝ)
    (field : ClosedJet dimension) :
    HasSum (fun count : ℕ => (((parameter ^ count : ℝ) : ℂ) • volterraPower (count + 1) field).value)
      (volterraResolventJet parameter field).value := by
  simpa only [closedDerivative_zero_order] using
    volterraResolventJet_derivative_hasSum parameter field emptyCartesianWord

end Grad.ActualCenterVolterra
