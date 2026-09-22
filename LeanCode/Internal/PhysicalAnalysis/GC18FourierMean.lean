import GC18DeterminantValue

noncomputable section

set_option maxHeartbeats 1400000

open Set MeasureTheory
open scoped Topology BigOperators Interval

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

theorem fourierAngularTerm_continuous {L sigma gamma ell : ℝ} {input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell 0 input output) (angle : ℝ)
    (point : ClosedDisk) (cell : ℤ) :
    Continuous (fun time : ℝ => fourierPhase cell angle •
      coefficientValue coefficient cell (Grad.GaugeCoefficients.Radial.rotatedPoint (2 * Real.pi * time) point)) := by
  have pairContinuous : Continuous (fun time : ℝ => (2 * Real.pi * time, point)) :=
    ((continuous_const : Continuous (fun _ : ℝ => 2 * Real.pi)).mul continuous_id).prodMk
      (continuous_const : Continuous (fun _ : ℝ => point))
  have orbit := Grad.GaugeCoefficients.Radial.continuous_rotatedPoint_joint.comp pairContinuous
  have result := ((coefficientValue coefficient cell).continuous.comp orbit).const_smul (fourierPhase cell angle)
  change Continuous (fun time : ℝ => fourierPhase cell angle •
      coefficientValue coefficient cell (Grad.GaugeCoefficients.Radial.rotatedPoint (2 * Real.pi * time) point)) at result
  exact result

/-- Full-cell Fourier summation commutes with the literal spatial angular
mean. The dominating l1 sequence is the original coefficient graph norm. -/
theorem coefficientAngular_fourier {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell 0 input output)
    (angle : ℝ) (point : ClosedDisk) :
    fourierEvaluation (coefficientAngularMap L sigma gamma ell 0 input output coefficient) angle point =
      ∫ time in Icc (0 : ℝ) 1,
        fourierEvaluation coefficient angle (Grad.GaugeCoefficients.Radial.rotatedPoint (2 * Real.pi * time) point) := by
  let term : ℤ → ℝ → OperatorValue input output := fun cell time => fourierPhase cell angle •
    coefficientValue coefficient cell (Grad.GaugeCoefficients.Radial.rotatedPoint (2 * Real.pi * time) point)
  have termIntegrable : ∀ cell, IntegrableOn (term cell) (Icc (0 : ℝ) 1) volume :=
    fun cell => (fourierAngularTerm_continuous coefficient angle point cell).continuousOn.integrableOn_Icc
  have major : Summable (fun cell : ℤ => ‖weightedDerivative coefficient cell zeroDerivativeIndex‖) :=
    coordinate_norm_summable coefficient.val zeroDerivativeIndex
  have volumeOne : (volume.restrict (Icc (0 : ℝ) 1)).real Set.univ = 1 := by
    rw [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num
  have integralNorms : Summable (fun cell : ℤ => ∫ time in Icc (0 : ℝ) 1, ‖term cell time‖) := by
    apply Summable.of_nonneg_of_le (fun cell => integral_nonneg (fun _ => norm_nonneg _)) ?_ major
    intro cell
    calc
      _ ≤ ∫ _time in Icc (0 : ℝ) 1, ‖weightedDerivative coefficient cell zeroDerivativeIndex‖ := by
        apply integral_mono_ae (termIntegrable cell).norm (integrable_const _)
        filter_upwards with time
        change ‖fourierPhase cell angle • coefficientValue coefficient cell
          (Grad.GaugeCoefficients.Radial.rotatedPoint (2 * Real.pi * time) point)‖ ≤ _
        rw [norm_smul, fourierPhase_norm, one_mul]
        exact coefficientValue_point_norm_le admissible coefficient cell _
      _ = ‖weightedDerivative coefficient cell zeroDerivativeIndex‖ := by
        rw [integral_const, volumeOne, one_smul]
  change (∑' cell : ℤ, fourierPhase cell angle •
      coefficientDerivative (coefficientAngularMap L sigma gamma ell 0 input output coefficient)
        cell (zeroDerivativeIndexAt 0) point) = ∫ time in Icc (0 : ℝ) 1, ∑' cell : ℤ, term cell time
  simp_rw [coefficientAngular_value]
  unfold angularMeanValue
  simp_rw [← integral_smul]
  exact integral_tsum_of_summable_integral_norm termIntegrable integralNorms

theorem angularFamily_physicalValue {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (angularFamily family grade) angle point =
      ∫ time in Icc (0 : ℝ) 1, coefficientPhysicalValue (family grade) angle
        (Grad.GaugeCoefficients.Radial.rotatedPoint (2 * Real.pi * time) point) := by
  rw [coherent_physicalValue (angularFamily family) (angularFamily_coherent family coherent)]
  simp_rw [coherent_physicalValue family coherent]
  exact coefficientAngular_fourier admissible (family 0) angle point

end Grad.GaugeCoefficients.Physical.RadialLedger
