import GC18APL2Weights

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Envelope
open Grad.NonlinearQuotientBounds Grad.NonlinearRange

attribute [local irreducible] apL2Trace

theorem apL2Trace_norm_summable {dimension grade : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) :
    Summable (fun cell : ℤ => ‖apL2Trace (dimension := dimension) (grade := grade) L sigma gamma ell cell‖) :=
  apOperator_norm_summable (fun cell => apL2Trace (dimension := dimension) (grade := grade) L sigma gamma ell cell)
    (fun cell => Real.exp (-((sigma - gamma) * |(cell : ℝ)|)))
    (apDecay_summable (sub_pos.mpr (lt_min_iff.mp admissible.2.2.1).2))
    (fun _ => (Real.exp_pos _).le) (fun cell field => apL2Trace_bound admissible cell field)

theorem apL2Trace_phase_norm_summable {dimension grade : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (angle : ℝ) :
    Summable (fun cell : ℤ => ‖axialPhase cell angle • apL2Trace (dimension := dimension) (grade := grade) L sigma gamma ell cell‖) :=
  apPhaseOperator_norm_summable (fun cell => apL2Trace (dimension := dimension) (grade := grade) L sigma gamma ell cell)
    (fun cell => axialPhase cell angle) (fun cell => norm_axialPhase cell angle) (apL2Trace_norm_summable admissible)

/-- Full faithful L2 Fourier realization at every AP2 grade, including zero. -/
def apL2PhysicalValue {dimension grade : ℕ} {L sigma gamma ell : ℝ}
    (_admissible : Admissible L sigma gamma ell) (angle : ℝ) :
    apGrade L sigma gamma ell dimension grade →L[ℂ] DiskL2 dimension :=
  ∑' cell : ℤ, axialPhase cell angle • apL2Trace L sigma gamma ell cell

theorem apL2PhysicalValue_hasSum {dimension grade : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (angle : ℝ) (field : apGrade L sigma gamma ell dimension grade) :
    HasSum (fun cell : ℤ => axialPhase cell angle • apL2Trace L sigma gamma ell cell field)
      (apL2PhysicalValue admissible angle field) := by
  have summable : Summable (fun cell : ℤ => axialPhase cell angle • apL2Trace (dimension := dimension) (grade := grade) L sigma gamma ell cell) :=
    Summable.of_norm (f := fun cell : ℤ => axialPhase cell angle • apL2Trace (dimension := dimension) (grade := grade) L sigma gamma ell cell)
      (apL2Trace_phase_norm_summable admissible angle)
  exact operatorHasSum_apply (fun cell => axialPhase cell angle • apL2Trace (dimension := dimension) (grade := grade) L sigma gamma ell cell)
    (apL2PhysicalValue admissible angle) summable.hasSum field

theorem apL2Trace_value_norm_summable {dimension grade : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (field : apGrade L sigma gamma ell dimension grade) :
    Summable (fun cell : ℤ => ‖apL2Trace L sigma gamma ell cell field‖) :=
  ((apL2Trace_norm_summable admissible).mul_right ‖field‖).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun cell => (apL2Trace L sigma gamma ell cell).le_opNorm field)

theorem apL2PhysicalValue_single {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (angle : ℝ) (cell : ℤ) (field : ClosedJet dimension) :
    apL2PhysicalValue admissible angle (apFiniteInto (grade := grade) L sigma gamma ell (Finsupp.single cell field)) =
      axialPhase cell angle • closedContinuousToDiskL2 field.value := by
  rw [← (apL2PhysicalValue_hasSum admissible angle (apFiniteInto (grade := grade) L sigma gamma ell (Finsupp.single cell field))).tsum_eq]
  simp_rw [apL2Trace_core]
  rw [tsum_eq_single cell]
  · rw [Finsupp.single_eq_same]
  · intro other different
    rw [Finsupp.single_eq_of_ne different]
    change axialPhase other angle • apClosedL2Linear dimension 0 = 0
    rw [map_zero]
    exact smul_zero (M := ℂ) (A := DiskL2 dimension) _

theorem apL2PhysicalValue_ext {dimension grade : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    (first second : apGrade L sigma gamma ell dimension grade)
    (equality : ∀ angle : ℝ, apL2PhysicalValue admissible angle first = apL2PhysicalValue admissible angle second) : first = second := by
  apply apL2Trace_ext L sigma gamma ell
  have coefficients := axialSeries_ext
    (fun cell => apL2Trace L sigma gamma ell cell first) (fun cell => apL2Trace L sigma gamma ell cell second)
    (apL2Trace_value_norm_summable admissible first) (apL2Trace_value_norm_summable admissible second) (by
      intro angle
      rw [(apL2PhysicalValue_hasSum admissible angle first).tsum_eq,
        (apL2PhysicalValue_hasSum admissible angle second).tsum_eq, equality])
  exact congrFun coefficients

end Grad.GaugeCoefficients.Physical.RadialLedger
