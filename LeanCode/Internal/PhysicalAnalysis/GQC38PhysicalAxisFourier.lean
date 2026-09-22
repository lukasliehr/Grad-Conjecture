import GQC37PhysicalDerivative

noncomputable section

set_option maxHeartbeats 1600000

open Set Filter
open scoped Topology

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.NonlinearDivision

theorem apSmoothJet_value_trace {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (large : 2 ≤ grade) (field : APSmooth L sigma gamma ell dimension) (cell : ℤ) :
    (apSmoothJet admissible dimension cell field).value = apTrace admissible large cell (field.val grade) :=
  apFamilyJet_value_trace admissible field.val field.property large cell

theorem apSmoothPhysicalValue_hasSum_point {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (field : APSmooth L sigma gamma ell dimension) (angle : ℝ) (point : ClosedDisk) :
    HasSum (fun cell => axialPhase cell angle • (apSmoothJet admissible dimension cell field).value point)
      (apSmoothPhysicalValue admissible dimension angle field point) := by
  have summed := (ContinuousMap.evalCLM ℂ point).hasSum
    (apPhysicalValue_hasSum admissible (by omega : 2 ≤ 2) angle (field.val 2))
  apply summed.congr_fun
  intro cell
  rw [apSmoothJet_value_trace admissible (by omega : 2 ≤ 2) field cell]
  rfl

theorem apSmoothJet_point_norm_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (field : APSmooth L sigma gamma ell dimension) (point : ClosedDisk) :
    Summable (fun cell => ‖(apSmoothJet admissible dimension cell field).value point‖) := by
  apply (apTrace_value_norm_summable admissible (by omega : 2 ≤ 2) (field.val 2)).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro cell
  rw [apSmoothJet_value_trace admissible (by omega : 2 ≤ 2) field cell]
  exact ContinuousMap.norm_coe_le_norm _ point

/-- Axis (and any fixed-point) Fourier faithfulness uses every cell,
with the actual original-width summable series. -/
theorem apSmoothPhysicalValue_pointwise_zero_iff {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (field : APSmooth L sigma gamma ell dimension) (point : ClosedDisk) :
    (∀ angle, apSmoothPhysicalValue admissible dimension angle field point = 0) ↔
      ∀ cell, (apSmoothJet admissible dimension cell field).value point = 0 := by
  constructor
  · intro zero
    have same := axialSeries_ext (fun cell => (apSmoothJet admissible dimension cell field).value point)
      (fun _ : ℤ => (0 : ComplexEuclidean dimension)) (apSmoothJet_point_norm_summable admissible field point)
      (by simp) (by
        intro angle
        simp only [smul_zero, tsum_zero]
        exact (apSmoothPhysicalValue_hasSum_point admissible field angle point).tsum_eq.trans (zero angle))
    exact fun cell => congrFun same cell
  · intro zero angle
    rw [← (apSmoothPhysicalValue_hasSum_point admissible field angle point).tsum_eq]
    simp only [zero, smul_zero, tsum_zero]

def APSmoothAxisValueZero {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension) : Prop :=
  ∀ cell, (apSmoothJet admissible dimension cell field).value closedOrigin = 0

def APSmoothAxisFirstJetZero {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension) : Prop :=
  APSmoothAxisValueZero admissible field ∧
    ∀ coordinate, APSmoothAxisValueZero admissible (apSmoothPartial admissible dimension coordinate field)

end Grad.GaugeCoefficients.Physical.Compensated
