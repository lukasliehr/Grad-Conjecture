import GC18APClosure
import GC18FourierContinuity

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Physical.Ledger

theorem cMapCoefficient_point_norms {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade input output : ℕ} (coefficient : Coefficient L sigma gamma ell grade input output) (angle : ℝ) (point : ClosedDisk) :
    Summable (fun cell : ℤ => ‖fourierPhase cell angle • coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) point‖) := by
  apply Summable.of_nonneg_of_le
    (fun cell => norm_nonneg (fourierPhase cell angle • coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) point))
    ?_ (coordinate_norm_summable coefficient.val (zeroDerivativeIndexAt grade))
  intro cell
  rw [norm_smul, fourierPhase_norm, one_mul]
  exact coefficientDerivative_point_norm_le admissible coefficient cell (zeroDerivativeIndexAt grade) point

theorem cMapCoefficient_point_summable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade input output : ℕ} (coefficient : Coefficient L sigma gamma ell grade input output) (angle : ℝ) (point : ClosedDisk) :
    Summable (fun cell : ℤ => fourierPhase cell angle • coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) point) :=
  Summable.of_norm (f := fun cell : ℤ => fourierPhase cell angle • coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) point)
    (cMapCoefficient_point_norms admissible coefficient angle point)

theorem cMapCoefficient_continuous {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade input output : ℕ} (coefficient : Coefficient L sigma gamma ell grade input output) (angle : ℝ) :
    Continuous (coefficientPhysicalValue coefficient angle) := by
  apply continuous_tsum
    (fun cell : ℤ => (coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade)).continuous.const_smul (fourierPhase cell angle))
    (coordinate_norm_summable coefficient.val (zeroDerivativeIndexAt grade))
  intro cell point
  change ‖fourierPhase cell angle • coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) point‖ ≤ _
  rw [norm_smul, fourierPhase_norm, one_mul]
  exact coefficientDerivative_point_norm_le admissible coefficient cell (zeroDerivativeIndexAt grade) point

def cMapCoefficientLinear {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade input output : ℕ) (angle : ℝ) :
    Coefficient L sigma gamma ell grade input output →ₗ[ℂ] C(ClosedDisk, OperatorValue input output) where
  toFun coefficient := ⟨coefficientPhysicalValue coefficient angle, cMapCoefficient_continuous admissible coefficient angle⟩
  map_add' first second := by
    apply ContinuousMap.ext
    intro point
    change coefficientPhysicalValue (first + second) angle point =
      coefficientPhysicalValue first angle point + coefficientPhysicalValue second angle point
    unfold coefficientPhysicalValue
    simp_rw [coefficientDerivative_add_apply, smul_add]
    exact (cMapCoefficient_point_summable admissible first angle point).tsum_add
      (cMapCoefficient_point_summable admissible second angle point)
  map_smul' scalar coefficient := by
    apply ContinuousMap.ext
    intro point
    change coefficientPhysicalValue (scalar • coefficient) angle point = scalar • coefficientPhysicalValue coefficient angle point
    unfold coefficientPhysicalValue
    simp_rw [coefficientDerivative_smul_apply, smul_comm (fourierPhase _ angle) scalar]
    exact (cMapCoefficient_point_summable admissible coefficient angle point).tsum_const_smul scalar

theorem cMapCoefficient_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade input output : ℕ} (coefficient : Coefficient L sigma gamma ell grade input output) (angle : ℝ) :
    ‖cMapCoefficientLinear admissible grade input output angle coefficient‖ ≤ ‖coefficient‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro point
  change ‖coefficientPhysicalValue coefficient angle point‖ ≤ _
  calc
    _ ≤ ∑' cell : ℤ, ‖fourierPhase cell angle • coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) point‖ :=
      norm_tsum_le_tsum_norm (cMapCoefficient_point_norms admissible coefficient angle point)
    _ ≤ ∑' cell : ℤ, ‖weightedDerivative coefficient cell (zeroDerivativeIndexAt grade)‖ := by
      apply (cMapCoefficient_point_norms admissible coefficient angle point).tsum_le_tsum _
        (coordinate_norm_summable coefficient.val (zeroDerivativeIndexAt grade))
      intro cell
      rw [norm_smul, fourierPhase_norm, one_mul]
      exact coefficientDerivative_point_norm_le admissible coefficient cell (zeroDerivativeIndexAt grade) point
    _ ≤ ‖coefficient‖ := coordinate_norm_sum_le coefficient.val (zeroDerivativeIndexAt grade)

def cMapCoefficient {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade input output : ℕ) (angle : ℝ) :
    Coefficient L sigma gamma ell grade input output →L[ℂ] C(ClosedDisk, OperatorValue input output) :=
  @LinearMap.mkContinuous ℂ ℂ (Coefficient L sigma gamma ell grade input output)
    (C(ClosedDisk, OperatorValue input output)) _ _ _ _ _ _ (RingHom.id ℂ)
    (cMapCoefficientLinear admissible grade input output angle) 1
    (fun coefficient => by
      change ‖cMapCoefficientLinear admissible grade input output angle coefficient‖ ≤ 1 * ‖coefficient‖
      rw [one_mul]
      exact cMapCoefficient_bound admissible coefficient angle)

theorem cMapCoefficient_apply {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade input output : ℕ} (coefficient : Coefficient L sigma gamma ell grade input output) (angle : ℝ) (point : ClosedDisk) :
    cMapCoefficient admissible grade input output angle coefficient point = coefficientPhysicalValue coefficient angle point := rfl

end Grad.GaugeCoefficients.Physical.RadialLedger
