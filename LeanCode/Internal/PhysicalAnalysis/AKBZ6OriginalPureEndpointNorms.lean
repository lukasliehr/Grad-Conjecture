import AKBZ5ActualPositiveOrderSumPayment
import AHJ4MassEndpointEstimate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Algebra

/-- The actual original weighted multi-index row is the accepted arbitrary
mass row applied to the SAME literal phase-weighted field. -/
theorem originalWeightedRow_mass {dimension grade : ℕ} (parameters : PhaseParameters)
    (cell : ℤ) (field : ClosedJet dimension) :
    cellGradeRowLinear (grade:=grade) parameters cell field=
      apMassRow (cellFrequency cell) grade (phaseWeightedJet parameters cell field) := rfl

/-- Full pure-planar Sobolev norm of the original weighted field, all cells. -/
def originalPlanarNorm {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (field : ACore parameters dimension) : ℝ :=
  Real.sqrt (∑' cell : ℤ, ‖apMassRow 1 grade (phaseWeightedJet parameters cell (field.val cell))‖^2)

/-- Full pure-cell endpoint of the same weighted field, with original lambda. -/
def originalCellNorm {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (field : ACore parameters dimension) : ℝ :=
  Real.sqrt (∑' cell : ℤ,
    ((cellFrequency cell)^grade*‖apMassRow (cellFrequency cell) 0 (phaseWeightedJet parameters cell (field.val cell))‖)^2)

theorem originalPlanarNorm_summable {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (field : ACore parameters dimension) :
    Summable (fun cell : ℤ => ‖apMassRow 1 grade (phaseWeightedJet parameters cell (field.val cell))‖^2) := by
  have total := (original_rows_summable (grade:=grade) parameters field).mul_left ((apLoweringConstant grade)^2)
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun cell => ?_) total
  rw [originalWeightedRow_mass,←mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (apMassRow_ordinary_le (cellFrequency cell) (cellFrequency_one_le cell) (phaseWeightedJet parameters cell (field.val cell))) 2

theorem originalCellNorm_summable {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (field : ACore parameters dimension) :
    Summable (fun cell : ℤ =>
      ((cellFrequency cell)^grade*‖apMassRow (cellFrequency cell) 0 (phaseWeightedJet parameters cell (field.val cell))‖)^2) := by
  have total := (original_rows_summable (grade:=grade) parameters field).mul_left ((apLoweringConstant 0)^2)
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun cell => ?_) total
  rw [originalWeightedRow_mass,←mul_pow]
  apply pow_le_pow_left₀ (mul_nonneg (pow_nonneg (cellFrequency_pos cell).le _) (norm_nonneg _)) _ 2
  simpa only [Nat.sub_zero] using apMassRow_lower_power (cellFrequency cell) (cellFrequency_one_le cell)
    (Nat.zero_le grade) (phaseWeightedJet parameters cell (field.val cell))

theorem originalPlanarNorm_sq {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (field : ACore parameters dimension) :
    originalPlanarNorm parameters grade field^2=
      ∑' cell : ℤ, ‖apMassRow 1 grade (phaseWeightedJet parameters cell (field.val cell))‖^2 :=
  Real.sq_sqrt (tsum_nonneg (fun _ => sq_nonneg _))

theorem originalCellNorm_sq {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (field : ACore parameters dimension) :
    originalCellNorm parameters grade field^2=
      ∑' cell : ℤ,
        ((cellFrequency cell)^grade*‖apMassRow (cellFrequency cell) 0 (phaseWeightedJet parameters cell (field.val cell))‖)^2 :=
  Real.sq_sqrt (tsum_nonneg (fun _ => sq_nonneg _))

end Grad.OriginalCartesianTameEstimate
