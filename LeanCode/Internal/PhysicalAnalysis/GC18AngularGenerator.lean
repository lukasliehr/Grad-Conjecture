import GC18JetBridge
import AngularProjectionDerivatives

noncomputable section

set_option maxHeartbeats 1400000

open Set MeasureTheory
open scoped Topology BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.Ledger
open Grad.RepresentedKernel.SpatialProduct Grad.Constraints

def singleJetCoefficient (L sigma gamma ell : ℝ) (grade : ℕ) (cell : ℤ)
    {input output : ℕ} (field : SmoothOperatorJet input output) : Coefficient L sigma gamma ell grade input output :=
  coreInclusion L sigma gamma ell grade input output
    ⟨weightedSingle L sigma gamma ell grade cell field,
      Submodule.subset_span (Set.mem_range.mpr ⟨(cell, field), rfl⟩)⟩

theorem singleJetCoefficient_derivative (L sigma gamma ell : ℝ) (grade : ℕ) (cell other : ℤ)
    {input output : ℕ} (field : SmoothOperatorJet input output) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (singleJetCoefficient L sigma gamma ell grade cell field) other index point =
      if other = cell then smoothOperatorDerivative field (derivativeMultiIndex index) point else 0 := by
  change ((coefficientScale L sigma gamma ell grade other index point : ℂ)⁻¹) •
    weightedSingle L sigma gamma ell grade cell field (other, index) point = _
  rw [weightedSingle_apply]
  by_cases same : other = cell
  · subst other
    rw [if_pos rfl, if_pos rfl]
    change ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
      ((coefficientScale L sigma gamma ell grade cell index point : ℂ) •
        smoothOperatorDerivative field (derivativeMultiIndex index) point) = _
    rw [← mul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
      (coefficientScale_pos L sigma gamma ell grade cell index point).ne'), one_smul]
  · rw [if_neg same, if_neg same]
    change ((coefficientScale L sigma gamma ell grade other index point : ℂ)⁻¹) • (0 : OperatorValue input output) = 0
    exact smul_zero (M := ℂ) (A := OperatorValue input output)
      ((coefficientScale L sigma gamma ell grade other index point : ℂ)⁻¹)

theorem orthogonal_single_column (L sigma gamma ell : ℝ) (grade : ℕ) (cell other : ℤ)
    {input output : ℕ} (field : SmoothOperatorJet input output) (column : PhysicalValue input)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (coefficientOrthogonalMap L sigma gamma ell grade input output orthogonal
      (singleJetCoefficient L sigma gamma ell grade cell field)) other index point column =
      if other = cell then orthogonalDerivative orthogonal (operatorJetColumn field column)
        (derivativeOrder index) (derivativeWord index) point else 0 := by
  rw [coefficientOrthogonal_derivative]
  simp_rw [singleJetCoefficient_derivative]
  by_cases same : other = cell
  · simp only [if_pos same, sum_apply, smul_apply]
    change (∑ target : Word (derivativeOrder index),
      (chainFactor (derivativeOrder index) orthogonal (derivativeWord index) target : ℂ) •
        smoothOperatorDerivative field (derivativeMultiIndex (orthogonalDerivativeIndex index target))
          (orthogonalClosedPoint orthogonal point) column) =
      ∑ target : CartesianWord (derivativeOrder index),
        chainFactor (derivativeOrder index) orthogonal (derivativeWord index) target •
          closedDerivative (operatorJetColumn field column) (derivativeOrder index) target (orthogonalClosedPoint orthogonal point)
    apply Finset.sum_congr rfl
    intro target _
    rw [operatorJetColumn_derivative]
    exact Complex.coe_smul _ _
  · simp only [if_neg same]
    simp_rw [smul_zero (M := ℂ) (A := OperatorValue input output)]
    rw [Finset.sum_const_zero]
    rfl

theorem continuous_rotation_coefficientDerivative (L sigma gamma ell : ℝ) (grade input output : ℕ)
    (coefficient : Coefficient L sigma gamma ell grade input output)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    Continuous (fun time : ℝ => coefficientDerivative
      (coefficientOrthogonalMap L sigma gamma ell grade input output (planeRotationEquiv (2 * Real.pi * time)) coefficient)
      cell index point) := by
  have continuous : Continuous (fun time : ℝ =>
      rawRotationCoordinateJoint coefficient.val cell index (time, point)) :=
    (rawRotationCoordinateJoint coefficient.val cell index).continuous.comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => point)))
  change Continuous (fun time : ℝ => ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
    rawOrthogonalCoordinate (planeRotationEquiv (2 * Real.pi * time)) coefficient.val cell index point)
  have result := continuous.const_smul ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹)
  change Continuous (fun time : ℝ => ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
    rawRotationCoordinateJoint coefficient.val cell index (time, point)) at result
  simpa only [rawRotationCoordinateJoint_apply] using result

theorem normalizedAngularIntegral {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (field : ℝ → Target) :
    (∫ time in Icc (0 : ℝ) 1, field (2 * Real.pi * time)) =
      (2 * Real.pi)⁻¹ • ∫ angle in Icc (0 : ℝ) (2 * Real.pi), field angle := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  simpa only [mul_zero, mul_one] using intervalIntegral.integral_comp_mul_left
    (f := field) (a := 0) (b := 1) (by positivity : (2 * Real.pi : ℝ) ≠ 0)

theorem angular_single_column (L sigma gamma ell : ℝ) (grade : ℕ) (cell other : ℤ)
    {input output : ℕ} (field : SmoothOperatorJet input output) (column : PhysicalValue input)
    (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (coefficientAngularMap L sigma gamma ell grade input output
      (singleJetCoefficient L sigma gamma ell grade cell field)) other index point column =
      if other = cell then closedDerivative (angularClosedJet 0 (operatorJetColumn field column))
        (derivativeOrder index) (derivativeWord index) point else 0 := by
  rw [coefficientAngular_derivative_integral]
  have integrable : IntegrableOn (fun time : ℝ => coefficientDerivative
      (coefficientOrthogonalMap L sigma gamma ell grade input output (planeRotationEquiv (2 * Real.pi * time))
        (singleJetCoefficient L sigma gamma ell grade cell field)) other index point)
      (Icc (0 : ℝ) 1) volume := (continuous_rotation_coefficientDerivative L sigma gamma ell grade input output
    (singleJetCoefficient L sigma gamma ell grade cell field) other index point).continuousOn.integrableOn_Icc
  change (ContinuousLinearMap.apply ℂ (PhysicalValue output) column)
    (∫ time in Icc (0 : ℝ) 1, coefficientDerivative
      (coefficientOrthogonalMap L sigma gamma ell grade input output (planeRotationEquiv (2 * Real.pi * time))
        (singleJetCoefficient L sigma gamma ell grade cell field)) other index point) = _
  rw [← (ContinuousLinearMap.apply ℂ (PhysicalValue output) column).integral_comp_comm integrable]
  change (∫ time in Icc (0 : ℝ) 1, coefficientDerivative
      (coefficientOrthogonalMap L sigma gamma ell grade input output (planeRotationEquiv (2 * Real.pi * time))
        (singleJetCoefficient L sigma gamma ell grade cell field)) other index point column) = _
  simp_rw [orthogonal_single_column]
  by_cases same : other = cell
  · simp only [if_pos same]
    rw [angularClosedJet_derivative]
    simp only [angularCharacter_zero_mode, one_smul]
    exact normalizedAngularIntegral (Target := PhysicalValue output)
      (fun angle => orthogonalDerivative (planeRotationEquiv angle) (operatorJetColumn field column)
        (derivativeOrder index) (derivativeWord index) point)
  · simp only [if_neg same, integral_zero]

end Grad.GaugeCoefficients.Physical.RadialLedger
