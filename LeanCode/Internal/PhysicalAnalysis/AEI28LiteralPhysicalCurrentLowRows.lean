import AEI27ExactRhoPhysicalKernelAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.ActualBoundaryPrimitives Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger

open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients

/-- The three original physical output coefficients are the SAME completed
J, c=Rb3 and P-projected rV actions used in the current low generator. -/
def lowOriginalCurrentRow (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (field : lowEnergyGraph lower length positive)
    (row : Fin 3) (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  lowRhoPhysicalCoefficient parameters lower positive
    (lowPhysicalRowAction parameters length compact lower positive bounded.le state row
      (lowNormalizedSevenInput parameters lower length lengthPositive positive (field.val 0))) radius mode

/-- Literal physical convolution of every original low input coefficient,
with zero complementary input modes. The radial storage factor cancels on
both sides, and rV is AHW28's P-projected physical provider. -/
theorem lowOriginalCurrentRow_hasSum (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (field : lowEnergyGraph lower length positive) (row : Fin 3) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (lowPhysicalRowKernel parameters length compact state row (collarRadius lower positive bounded.le radius)).entry
        shift (twoFrequencyTranslation shift mode)
        (lowOriginalSevenCoefficient parameters lower length positive bounded field radius (twoFrequencyTranslation shift mode)))
        (lowOriginalCurrentRow parameters length compact lower lengthPositive positive bounded state field row radius mode) := by
  let input := lowNormalizedSevenInput parameters lower length lengthPositive positive (field.val 0)
  filter_upwards [lowRegularAction_physical parameters lower positive bounded.le
      (lowPhysicalRowKernel parameters length compact state row) (lowPhysicalRowKernel_regular parameters length compact state row) input,
    lowNormalizedSevenInput_original parameters lower length lengthPositive positive bounded field]
    with radius actual packet
  intro mode
  apply (actual mode).congr_fun
  intro shift
  congr 1
  symm
  change (lowRhoPhysicalWeight parameters lower positive radius (twoFrequencyTranslation shift mode) : ℂ)⁻¹ •
    lowNormalizedSevenInput parameters lower length lengthPositive positive (field.val 0) (twoFrequencyTranslation shift mode) radius = _
  rw [packet (twoFrequencyTranslation shift mode), smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast (lowRhoPhysicalWeight_pos parameters lower positive radius (twoFrequencyTranslation shift mode)).ne'

/-- Encoding the original output returns the actual completed stored row. -/
theorem lowOriginalCurrentRow_encode (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (field : lowEnergyGraph lower length positive)
    (row : Fin 3) (radius : ℝ) (mode : ℤ × ℤ) :
    (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ) •
      lowOriginalCurrentRow parameters length compact lower lengthPositive positive bounded state field row radius mode =
    lowPhysicalRowAction parameters length compact lower positive bounded.le state row
      (lowNormalizedSevenInput parameters lower length lengthPositive positive (field.val 0)) mode radius := by
  unfold lowOriginalCurrentRow lowRhoPhysicalCoefficient
  rw [smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast (lowRhoPhysicalWeight_pos parameters lower positive radius mode).ne'

end Grad.AnnularCurrentLow
