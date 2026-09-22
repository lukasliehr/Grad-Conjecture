import GC17Consumer
import GC13Proof

noncomputable section

set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.RepresentedKernel.SpatialProduct

def radialFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (family : CoefficientFamily L sigma gamma ell input output) :
    CoefficientFamily L sigma gamma ell input output :=
  fun grade => coefficientRadialMap admissible grade input output (family grade)

def laplacianFamily {L sigma gamma ell : ℝ} {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) :
    CoefficientFamily L sigma gamma ell input output :=
  fun grade => coefficientLaplacianMap L sigma gamma ell grade input output (family (grade + 2))

def angularFamily {L sigma gamma ell : ℝ} {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) :
    CoefficientFamily L sigma gamma ell input output :=
  fun grade => coefficientAngularMap L sigma gamma ell grade input output (family grade)

theorem radialFamily_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (family : CoefficientFamily L sigma gamma ell input output)
    (coherent : FamilyCoherent family) : FamilyCoherent (radialFamily admissible family) := by
  intro grade other index otherIndex same cell point
  rw [radialFamily, radialFamily, coefficientRadial_derivative, coefficientRadial_derivative]
  unfold radialIntegralDerivative
  have orderSame : derivativeOrder index = derivativeOrder otherIndex := congrArg cartesianOrder same
  apply integral_congr_ae
  filter_upwards with time
  rw [orderSame, coherent grade other index otherIndex same]

theorem laplacianFamily_coherent {L sigma gamma ell : ℝ} {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output)
    (coherent : FamilyCoherent family) : FamilyCoherent (laplacianFamily family) := by
  intro grade other index otherIndex same cell point
  rw [laplacianFamily, laplacianFamily, coefficientLaplacian_derivative, coefficientLaplacian_derivative]
  unfold laplacianDerivative
  congr 1
  · apply coherent
    change (index.val.1.val + 2, index.val.2.val) = (otherIndex.val.1.val + 2, otherIndex.val.2.val)
    exact congrArg (fun pair : ℕ × ℕ => (pair.1 + 2, pair.2)) same
  · apply coherent
    change (index.val.1.val, index.val.2.val + 2) = (otherIndex.val.1.val, otherIndex.val.2.val + 2)
    exact congrArg (fun pair : ℕ × ℕ => (pair.1, pair.2 + 2)) same

theorem coefficientAngular_derivative_integral (L sigma gamma ell : ℝ) (grade input output : ℕ)
    (coefficient : Coefficient L sigma gamma ell grade input output)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (coefficientAngularMap L sigma gamma ell grade input output coefficient)
      cell index point =
      ∫ time in Icc (0 : ℝ) 1,
        coefficientDerivative (coefficientOrthogonalMap L sigma gamma ell grade input output
          (planeRotationEquiv (2 * Real.pi * time)) coefficient) cell index point := by
  change ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
    (∫ time in Icc (0 : ℝ) 1, rawRotationCoordinateJoint coefficient.val cell index (time, point)) = _
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with time
  rw [rawRotationCoordinateJoint_apply]
  rfl

def rawOrthogonalFamilyDerivative {L sigma gamma ell : ℝ} {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (cell : ℤ)
    (index : CartesianMultiIndex) (point : ClosedDisk) : OperatorValue input output :=
  ∑ target : Word (cartesianOrder index),
    (chainFactor (cartesianOrder index) orthogonal (cartesianMultiIndexWord index) target : ℂ) •
      rawFamilyDerivative family cell
        (Grad.WeakTesting.Commutation.directionCount target 0,
          Grad.WeakTesting.Commutation.directionCount target 1)
        (orthogonalClosedPoint orthogonal point)

theorem orthogonalFamily_coherent {L sigma gamma ell : ℝ} {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output)
    (coherent : FamilyCoherent family) (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) :
    FamilyCoherent (fun grade => coefficientOrthogonalMap L sigma gamma ell grade input output
      orthogonal (family grade)) := by
  intro grade other index otherIndex same cell point
  rw [coefficientOrthogonal_derivative, coefficientOrthogonal_derivative]
  simp_rw [coherent_derivative_raw family coherent]
  change rawOrthogonalFamilyDerivative family orthogonal cell (derivativeMultiIndex index) point =
    rawOrthogonalFamilyDerivative family orthogonal cell (derivativeMultiIndex otherIndex) point
  rw [same]

theorem angularFamily_coherent {L sigma gamma ell : ℝ} {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output)
    (coherent : FamilyCoherent family) : FamilyCoherent (angularFamily family) := by
  intro grade other index otherIndex same cell point
  rw [angularFamily, angularFamily, coefficientAngular_derivative_integral,
    coefficientAngular_derivative_integral]
  apply integral_congr_ae
  filter_upwards with time
  exact orthogonalFamily_coherent family coherent (planeRotationEquiv (2 * Real.pi * time))
    grade other index otherIndex same cell point

/-- The literal nonsingular IΔΠ construction; two grades, no width change. -/
def radialDivisionFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (family : CoefficientFamily L sigma gamma ell input output) :
    CoefficientFamily L sigma gamma ell input output :=
  radialFamily admissible (laplacianFamily (angularFamily family))

theorem radialDivisionFamily_coherent {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family) :
    FamilyCoherent (radialDivisionFamily admissible family) :=
  radialFamily_coherent admissible _ (laplacianFamily_coherent _ (angularFamily_coherent family coherent))

def radialDivisionConstant (grade : ℕ) : ℝ :=
  (1 / 4 : ℝ) * laplacianBound grade * angularBound (grade + 2)

theorem radialDivisionConstant_nonnegative (grade : ℕ) : 0 ≤ radialDivisionConstant grade := by
  unfold radialDivisionConstant laplacianBound angularBound
  positivity

theorem radialDivisionFamily_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (grade : ℕ) :
    ‖radialDivisionFamily admissible family grade‖ ≤ radialDivisionConstant grade * ‖family (grade + 2)‖ := by
  have first := coefficientRadial_bound admissible grade input output (laplacianFamily (angularFamily family) grade)
  have second := coefficientLaplacian_bound L sigma gamma ell grade input output (angularFamily family (grade + 2))
  have third := coefficientAngular_bound L sigma gamma ell (grade + 2) input output (family (grade + 2))
  have lapNonneg : 0 ≤ laplacianBound grade := by unfold laplacianBound; positivity
  exact first.trans ((mul_le_mul_of_nonneg_left
    (second.trans (mul_le_mul_of_nonneg_left third lapNonneg)) (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans_eq (by
      unfold radialDivisionConstant
      ring))

end Grad.GaugeCoefficients.Physical.RadialLedger
