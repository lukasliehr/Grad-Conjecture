import AKCB12FullDisplacementMatrixWeak

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

theorem startupAxialFrequency_binomial (L ell : ℝ) (output input : ℤ) (power : ℕ) :
    startupAxialFrequency L ell output^power =
      ∑ j ∈ Finset.range (power+1), (power.choose j : ℂ) *
        startupAxialFrequency L ell (output-input)^j * startupAxialFrequency L ell input^(power-j) := by
  have same : startupAxialFrequency L ell output =
      startupAxialFrequency L ell (output-input)+startupAxialFrequency L ell input := by
    rw [startupAxialFrequency_sub]
    ring
  conv_lhs => rw [same,add_pow]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Literal cell-binomial formula at one actual matrix entry. This uses the
output-input displacement, so axial-dependent coefficients keep all cells. -/
theorem startupDisplacementEntry_binomial {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade) (power : ℕ) (output input : ℤ)
    (field : Lp (PhysicalValue inputDimension) 2 (volume.restrict openUnitDisk)) :
    startupAxialFrequency L ell output^power •
      Grad.FullCellKernel.entry (startupDerivativeKernelData admissible family coherent index) output input field =
    ∑ j ∈ Finset.range (power+1), (power.choose j : ℂ) •
      Grad.FullCellKernel.entry (startupDisplacementKernelData admissible family coherent index j) output input
        (startupAxialFrequency L ell input^(power-j) • field) := by
  simp_rw [startupDisplacementKernel_entry,smul_apply,map_smul,smul_smul]
  rw [startupDerivativeKernel_entry,startupAxialFrequency_binomial,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc]

end Grad.CartesianStartup
