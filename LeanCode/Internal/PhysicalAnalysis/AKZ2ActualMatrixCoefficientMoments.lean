import AKZ1ActualInverseTransposeFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter
open scoped Topology BigOperators
namespace Grad.ActualPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarAngular
open Grad.SourceCollarRestriction
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

variable {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family)

/-- Literal row-column Fourier coefficient of the existing original family. -/
def physicalMatrixScalar (row : Fin output) (column : Fin input)
    (radial : ℕ) (radius : ℝ) (mode : ℤ × ℤ) : ℂ :=
  coefficientPolarFourier parameters family coherent (operatorBasis column) radial radius mode row

theorem physicalMatrixScalar_continuous (row : Fin output) (column : Fin input) (radial : ℕ) (mode : ℤ × ℤ) :
    Continuous (fun radius => physicalMatrixScalar parameters family coherent row column radial radius mode) := by
  have vector : Continuous (fun radius => coefficientPolarFourier parameters family coherent (operatorBasis column) radial radius mode) :=
    continuous_iff_continuousAt.mpr (fun radius =>
      (radialCoefficientJet_hasDerivAt _ (originalPolarValue_smooth
        (coefficientColumnJet parameters family coherent mode.2 (operatorBasis column))) mode.1 radial radius).continuousAt)
  exact (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin output => ℂ) row).continuous.comp vector

theorem physicalMatrixScalar_moment_le (row : Fin output) (column : Fin input) (tangential radial : ℕ)
    (radius : ℝ) (mode : ℤ × ℤ) :
    productMoment parameters tangential radius (physicalMatrixScalar parameters family coherent row column radial radius) mode ≤
      coefficientFourierWeightedNorm parameters family coherent (operatorBasis column) tangential radial radius mode :=
  mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ row)
    (mul_nonneg (coefficientRadialEnvelope_pos _ _ _).le (pow_nonneg (annularFrequency_nonnegative _ _) _))

theorem physicalMatrixScalar_moment_summable (row : Fin output) (column : Fin input) (tangential radial : ℕ)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (productMoment parameters tangential radius (physicalMatrixScalar parameters family coherent row column radial radius)) :=
  Summable.of_nonneg_of_le (productMoment_nonnegative _ _ _ _)
    (physicalMatrixScalar_moment_le parameters family coherent row column tangential radial radius)
    (coefficient_fourier_summable parameters family coherent (operatorBasis column) tangential radial radius nonnegative bounded)

theorem physicalMatrixScalar_moment_bound (row : Fin output) (column : Fin input) (tangential radial : ℕ)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    ∑' mode, productMoment parameters tangential radius (physicalMatrixScalar parameters family coherent row column radial radius) mode ≤
      coefficientFourierConstant tangential radial * ‖family (tangential + radial + 1)‖ * ‖operatorBasis column‖ :=
  ((physicalMatrixScalar_moment_summable parameters family coherent row column tangential radial radius nonnegative bounded).tsum_le_tsum
    (physicalMatrixScalar_moment_le parameters family coherent row column tangential radial radius)
    (coefficient_fourier_summable parameters family coherent (operatorBasis column) tangential radial radius nonnegative bounded)).trans
    (coefficient_fourier_bound parameters family coherent (operatorBasis column) tangential radial radius nonnegative bounded)

end Grad.ActualPhysicalField
