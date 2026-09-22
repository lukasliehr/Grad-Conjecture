import AKBZ8AdjustableOrdinaryMassOrder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 750000
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Algebra

/-- Pure cell power times all planar derivatives up to the specified order,
with complementary total order and the SAME original weighted field. -/
def originalMixedOrderNorm {dimension : ℕ} (parameters : PhaseParameters) (grade order : ℕ)
    (field : ACore parameters dimension) : ℝ :=
  Real.sqrt (∑' cell : ℤ,
    ((cellFrequency cell)^(grade-order)*‖apMassRow 1 order (phaseWeightedJet parameters cell (field.val cell))‖)^2)

theorem originalMixedOrderNorm_summable {dimension : ℕ} (parameters : PhaseParameters) (grade order : ℕ)
    (ordered : order≤grade) (field : ACore parameters dimension) :
    Summable (fun cell : ℤ =>
      ((cellFrequency cell)^(grade-order)*‖apMassRow 1 order (phaseWeightedJet parameters cell (field.val cell))‖)^2) := by
  have total := (original_rows_summable (grade:=grade) parameters field).mul_left ((apLoweringConstant order)^2)
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun cell => ?_) total
  rw [originalWeightedRow_mass,←mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg (pow_nonneg (cellFrequency_pos cell).le _) (norm_nonneg _))
    (apMassRow_ordinary_power (cellFrequency cell) (cellFrequency_one_le cell) ordered
      (phaseWeightedJet parameters cell (field.val cell))) 2

theorem originalMixedOrderNorm_sq {dimension : ℕ} (parameters : PhaseParameters) (grade order : ℕ)
    (field : ACore parameters dimension) :
    originalMixedOrderNorm parameters grade order field^2=
      ∑' cell : ℤ,
        ((cellFrequency cell)^(grade-order)*‖apMassRow 1 order (phaseWeightedJet parameters cell (field.val cell))‖)^2 :=
  Real.sq_sqrt (tsum_nonneg (fun _ => sq_nonneg _))

end Grad.OriginalCartesianTameEstimate
