import ACE26LiteralCenterConsumer
import GQC9APClosedDerivatives

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterBounds
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.ActualCenterVolterra Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.Compensated (apWeightedDerivativeSup_bound)
open Grad.GaugeCoefficients.Physical.RadialLedger (apSupConstant apSupConstant_nonnegative)

/-- The exact native H3 datum pays for one Cartesian derivative in supremum
norm; no higher source derivative is charged in the center base estimate. -/
theorem sourceFirstDerivative_sup (direction : Fin 2) (source : ClosedJet 1) :
    ‖closedDerivative source 1 (fun _ => direction)‖ ≤ apSupConstant * ‖unitDiskCoreInto 3 source‖ := by
  have bound := apWeightedDerivativeSup_bound (dimension := 1) (grade := 3) 1 0 0 1
    (by omega : 1 + 2 ≤ 3) 0 source (fun _ : Fin 1 => direction)
  rw [unweightedJet] at bound
  rw [unitDiskCore_norm]
  exact bound

theorem sourceCenterDifferential_sup (mode : ℤ) (center : mode = 1 ∨ mode = -1) (source : ClosedJet 1) :
    ‖(centerDifferential mode source).value‖ ≤ 2 * apSupConstant * ‖unitDiskCoreInto 3 source‖ := by
  have coefficient : ‖Complex.I * (mode : ℂ)‖ = 1 := by rcases center with rfl | rfl <;> norm_num
  have value : (centerDifferential mode source).value =
      (partialJet 0 source).value - (Complex.I * (mode : ℂ)) • (partialJet 1 source).value := by
    simp only [centerDifferential, sub_eq_add_neg, closedJet_value_add, closedJet_value_neg, closedJet_value_smul]
  rw [value]
  calc
    _ ≤ ‖(partialJet 0 source).value‖ + ‖(Complex.I * (mode : ℂ)) • (partialJet 1 source).value‖ := norm_sub_le _ _
    _ = ‖closedDerivative source 1 (fun _ => 0)‖ + ‖closedDerivative source 1 (fun _ => 1)‖ := by
      rw [norm_smul, coefficient, one_mul]
      rfl
    _ ≤ apSupConstant * ‖unitDiskCoreInto 3 source‖ + apSupConstant * ‖unitDiskCoreInto 3 source‖ :=
      add_le_add (sourceFirstDerivative_sup 0 source) (sourceFirstDerivative_sup 1 source)
    _ = _ := by ring

theorem sourceCenterQuotient_sup (mode : ℤ) (center : mode = 1 ∨ mode = -1) (source : ClosedJet 1) :
    ‖(centerQuotientJet mode source).value‖ ≤ apSupConstant * ‖unitDiskCoreInto 3 source‖ := by
  have integral := powerDilationJet_derivative_norm 1 (centerDifferential mode source) emptyCartesianWord
  simp only [closedDerivative_zero_order, Nat.cast_zero, Nat.cast_one, add_zero] at integral
  change ‖(centerQuotientJet mode source).value‖ ≤ _ at integral
  exact integral.trans ((div_le_div_of_nonneg_right (sourceCenterDifferential_sup mode center source) (by norm_num)).trans_eq (by ring))

end Grad.ActualCenterBounds
