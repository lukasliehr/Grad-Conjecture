import GC18AngularGenerator
import GC18RadialJetIdentity

noncomputable section

set_option maxHeartbeats 1400000

open Set MeasureTheory
open scoped Topology BigOperators Interval

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.Ledger
open Grad.RepresentedKernel.SpatialProduct Grad.Constraints Grad.NonlinearDivision
open Grad.GaugeCoefficients.Envelope
open Grad.NonlinearRadial Grad.NonlinearQuotientBounds Grad.NonlinearQuotient

theorem firstLaplacian_zero_word : derivativeWord (firstLaplacianIndex (zeroDerivativeIndexAt 0)) = fun _ => 0 := by
  funext index
  have bounded := index.isLt
  change (if index.val < 2 then (0 : Fin 2) else 1) = 0
  exact if_pos bounded

theorem secondLaplacian_zero_word : derivativeWord (secondLaplacianIndex (zeroDerivativeIndexAt 0)) = fun _ => 1 := by
  funext index
  rfl

theorem laplacian_angular_single_column (L sigma gamma ell : ℝ) (cell other : ℤ)
    {input output : ℕ} (field : SmoothOperatorJet input output) (column : PhysicalValue input)
    (point : ClosedDisk) :
    coefficientDerivative (coefficientLaplacianMap L sigma gamma ell 0 input output
      (coefficientAngularMap L sigma gamma ell 2 input output
        (singleJetCoefficient L sigma gamma ell 2 cell field))) other (zeroDerivativeIndexAt 0) point column =
      if other = cell then (laplacianJet (angularClosedJet 0 (operatorJetColumn field column))).value point else 0 := by
  rw [coefficientLaplacian_derivative]
  unfold laplacianDerivative
  rw [add_apply, angular_single_column, angular_single_column]
  by_cases same : other = cell
  · simp only [if_pos same, firstLaplacian_zero_word, secondLaplacian_zero_word]
    rw [laplacianJet_value]
    rfl
  · simp only [if_neg same, add_zero]

theorem coefficientRadial_zero_column {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell 0 input output)
    (cell : ℤ) (point : ClosedDisk) (column : PhysicalValue input) :
    coefficientDerivative (coefficientRadialMap admissible 0 input output coefficient) cell (zeroDerivativeIndexAt 0) point column =
      ∫ time in Icc (0 : ℝ) 1, (Real.negMulLog time : ℂ) •
        coefficientDerivative coefficient cell (zeroDerivativeIndexAt 0) (radialPoint time point) column := by
  rw [coefficientRadial_derivative]
  unfold radialIntegralDerivative
  simp only [show derivativeOrder (zeroDerivativeIndexAt 0) = 0 from rfl,
    pow_zero, Complex.ofReal_one, one_smul]
  have continuous : Continuous (fun time : ℝ => (Real.negMulLog time : ℂ) •
      coefficientDerivative coefficient cell (zeroDerivativeIndexAt 0) (radialPoint time point)) :=
    (Complex.continuous_ofReal.comp Real.continuous_negMulLog).smul
      ((coefficientDerivative coefficient cell (zeroDerivativeIndexAt 0)).continuous.comp
        (continuous_radialPoint_joint.comp (continuous_id.prodMk
          (continuous_const : Continuous (fun _ : ℝ => point)))))
  have integrable : IntegrableOn (fun time : ℝ => (Real.negMulLog time : ℂ) •
      coefficientDerivative coefficient cell (zeroDerivativeIndexAt 0) (radialPoint time point)) (Icc (0 : ℝ) 1) volume :=
    continuous.continuousOn.integrableOn_Icc
  change (ContinuousLinearMap.apply ℂ (PhysicalValue output) column)
    (∫ time in Icc (0 : ℝ) 1, (Real.negMulLog time : ℂ) •
      coefficientDerivative coefficient cell (zeroDerivativeIndexAt 0) (radialPoint time point)) = _
  rw [← (ContinuousLinearMap.apply ℂ (PhysicalValue output) column).integral_comp_comm integrable]
  rfl

theorem integralCoefficient_eq_clamped {dimension : ℕ} (field : ClosedJet dimension) (point : ClosedDisk) :
    integralCoefficient field point =
      ∫ time in Icc (0 : ℝ) 1, (Real.negMulLog time : ℂ) • field.value (radialPoint time point) := by
  unfold integralCoefficient radialIntegral
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with time inside
  rw [Complex.coe_smul]
  apply congrArg (fun value : PhysicalValue dimension => Real.negMulLog time • value)
  have identity := smoothClosedExtension_value field (radialPoint time point)
  simpa only [radialPoint, unitClamp_of_mem inside] using identity

theorem radial_laplacian_angular_single_column {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (cell other : ℤ)
    {input output : ℕ} (field : SmoothOperatorJet input output) (column : PhysicalValue input)
    (point : ClosedDisk) :
    coefficientDerivative (coefficientRadialMap admissible 0 input output
      (coefficientLaplacianMap L sigma gamma ell 0 input output
        (coefficientAngularMap L sigma gamma ell 2 input output
          (singleJetCoefficient L sigma gamma ell 2 cell field)))) other (zeroDerivativeIndexAt 0) point column =
      if other = cell then integralCoefficient (laplacianJet (angularClosedJet 0 (operatorJetColumn field column))) point else 0 := by
  rw [coefficientRadial_zero_column]
  simp_rw [laplacian_angular_single_column]
  by_cases same : other = cell
  · simp only [if_pos same]
    exact (integralCoefficient_eq_clamped _ _).symm
  · simp only [if_neg same, smul_zero, integral_zero]

end Grad.GaugeCoefficients.Physical.RadialLedger
