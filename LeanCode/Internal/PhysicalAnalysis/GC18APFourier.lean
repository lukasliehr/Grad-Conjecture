import GC18APUnweight

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Envelope
open Grad.NonlinearQuotientBounds Grad.NonlinearRange

attribute [local irreducible] apTrace

theorem apOperator_norm_summable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (family : ℤ → E →L[ℂ] F) (majorant : ℤ → ℝ)
    (summable : Summable majorant) (nonnegative : ∀ cell, 0 ≤ majorant cell)
    (bound : ∀ cell field, ‖family cell field‖ ≤ majorant cell * ‖field‖) :
    Summable (fun cell => ‖family cell‖) :=
  summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun cell => ContinuousLinearMap.opNorm_le_bound (family cell) (nonnegative cell) (bound cell))

theorem apPhaseOperator_norm_summable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (family : ℤ → E →L[ℂ] F)
    (phase : ℤ → ℂ) (normalized : ∀ cell, ‖phase cell‖ = 1)
    (summable : Summable (fun cell => ‖family cell‖)) :
    Summable (fun cell => ‖phase cell • family cell‖) := by
  apply summable.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro cell
  exact (norm_smul_le (phase cell) (family cell)).trans_eq (by rw [normalized, one_mul])

theorem apDecay_summable {rate : ℝ} (positive : 0 < rate) :
    Summable (fun cell : ℤ => Real.exp (-(rate * |(cell : ℝ)|))) := by
  have natural : Summable (fun index : ℕ => Real.exp (-(rate * (index : ℝ)))) := by
    have geometric := summable_geometric_of_lt_one (Real.exp_pos (-rate)).le
      (Real.exp_lt_one_iff.mpr (neg_neg_of_pos positive))
    apply geometric.congr
    intro index
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simpa only [Int.cast_natCast, Nat.abs_cast] using natural
  · simpa only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast] using natural

theorem apTrace_norm_summable {dimension grade : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (large : 2 ≤ grade) :
    Summable (fun cell : ℤ => ‖apTrace (dimension := dimension) admissible large cell‖) := by
  have positive : 0 < sigma - gamma := sub_pos.mpr (lt_min_iff.mp admissible.2.2.1).2
  exact apOperator_norm_summable (fun cell => apTrace (dimension := dimension) admissible large cell)
    (fun cell => Real.exp (-((sigma - gamma) * |(cell : ℝ)|)) * apSupConstant)
    ((apDecay_summable positive).mul_right apSupConstant)
    (fun _ => mul_nonneg (Real.exp_pos _).le apSupConstant_nonnegative)
    (fun cell field => apTrace_bound admissible large cell field)

theorem apTrace_phase_norm_summable {dimension grade : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (large : 2 ≤ grade) (angle : ℝ) :
    Summable (fun cell : ℤ => ‖axialPhase cell angle • apTrace (dimension := dimension) admissible large cell‖) := by
  exact apPhaseOperator_norm_summable (fun cell => apTrace (dimension := dimension) admissible large cell)
    (fun cell => axialPhase cell angle) (fun cell => norm_axialPhase cell angle)
    (apTrace_norm_summable (dimension := dimension) admissible large)

def apPhysicalValue {dimension grade : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (large : 2 ≤ grade) (angle : ℝ) :
    apGrade L sigma gamma ell dimension grade →L[ℂ] C(ClosedDisk, ComplexEuclidean dimension) :=
  ∑' cell : ℤ, axialPhase cell angle • apTrace admissible large cell

theorem apPhysicalValue_hasSum {dimension grade : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (large : 2 ≤ grade) (angle : ℝ)
    (field : apGrade L sigma gamma ell dimension grade) :
    HasSum (fun cell : ℤ => axialPhase cell angle • apTrace admissible large cell field)
      (apPhysicalValue admissible large angle field) :=
  by
    have summable : Summable (fun cell : ℤ => axialPhase cell angle • apTrace (dimension := dimension) admissible large cell) :=
      Summable.of_norm (f := fun cell : ℤ => axialPhase cell angle • apTrace (dimension := dimension) admissible large cell)
        (apTrace_phase_norm_summable (dimension := dimension) admissible large angle)
    exact operatorHasSum_apply (fun cell => axialPhase cell angle • apTrace (dimension := dimension) admissible large cell)
      (apPhysicalValue admissible large angle) summable.hasSum field

theorem apTrace_value_norm_summable {dimension grade : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (large : 2 ≤ grade)
    (field : apGrade L sigma gamma ell dimension grade) :
    Summable (fun cell : ℤ => ‖apTrace admissible large cell field‖) :=
  ((apTrace_norm_summable admissible large).mul_right ‖field‖).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun cell => (apTrace admissible large cell).le_opNorm field)

theorem apPhysicalValue_core {dimension grade : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (large : 2 ≤ grade) (angle : ℝ)
    (core : ℤ →₀ ClosedJet dimension) :
    apPhysicalValue admissible large angle (apFiniteInto L sigma gamma ell core) =
      ∑ cell ∈ core.support, axialPhase cell angle • (core cell).value := by
  rw [← (apPhysicalValue_hasSum admissible large angle (apFiniteInto L sigma gamma ell core)).tsum_eq]
  simp_rw [apTrace_core]
  apply tsum_eq_sum
  intro cell missing
  rw [Finsupp.notMem_support_iff.mp missing]
  change axialPhase cell angle • (0 : C(ClosedDisk, ComplexEuclidean dimension)) = 0
  exact smul_zero (M := ℂ) (A := C(ClosedDisk, ComplexEuclidean dimension)) (axialPhase cell angle)

/-- Faithful full Fourier realization, with neither a finite-band cut nor a width loss. -/
theorem apPhysicalValue_ext {dimension grade : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (large : 2 ≤ grade)
    (first second : apGrade L sigma gamma ell dimension grade)
    (equality : ∀ angle : ℝ, apPhysicalValue admissible large angle first = apPhysicalValue admissible large angle second) :
    first = second := by
  apply apTrace_ext admissible large
  have coefficients := axialSeries_ext
    (fun cell => apTrace admissible large cell first) (fun cell => apTrace admissible large cell second)
    (apTrace_value_norm_summable admissible large first) (apTrace_value_norm_summable admissible large second) (by
      intro angle
      rw [(apPhysicalValue_hasSum admissible large angle first).tsum_eq,
        (apPhysicalValue_hasSum admissible large angle second).tsum_eq, equality])
  exact congrFun coefficients

end Grad.GaugeCoefficients.Physical.RadialLedger
