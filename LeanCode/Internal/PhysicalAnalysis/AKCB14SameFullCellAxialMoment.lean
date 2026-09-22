import AKCB13CellBinomialEntries

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

/-- Construct the output axial moment as a finite sum of bounded actual
full-cell displacement kernels on the existing input moments. -/
def startupKernelAxialMoment {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade) (power : ℕ)
    (moments : ℕ → StartupL2 inputDimension) : StartupL2 outputDimension :=
  ∑ j ∈ Finset.range (power+1), (power.choose j : ℂ) •
    startupDisplacementKernel admissible family coherent index j (moments (power-j))

/-- SAME-field full infinite-cell binomial identity; no output moment is
assumed. All needed input moments are finite L2 fields. -/
theorem startupKernelAxialMoment_projection {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade) (power : ℕ)
    (field : StartupL2 inputDimension) (moments : ℕ → StartupL2 inputDimension)
    (same : ∀ j ≤ power, ∀ cell : ℤ,
      fieldCellProjection inputDimension openUnitDisk cell (moments j) =
        startupAxialFrequency L ell cell^j • fieldCellProjection inputDimension openUnitDisk cell field)
    (output : ℤ) :
    fieldCellProjection outputDimension openUnitDisk output
      (startupKernelAxialMoment admissible family coherent index power moments) =
    startupAxialFrequency L ell output^power • fieldCellProjection outputDimension openUnitDisk output
      (startupDerivativeKernel admissible family coherent index field) := by
  have left := hasSum_sum (s:=Finset.range (power+1)) (fun j _ =>
    (startupKernel_row_hasSum (startupDisplacementKernelData admissible family coherent index j)
      (moments (power-j)) output).const_smul (power.choose j : ℂ))
  have right := (startupKernel_row_hasSum (startupDerivativeKernelData admissible family coherent index)
    field output).const_smul (startupAxialFrequency L ell output^power)
  have terms (input : ℤ) :
      (∑ j ∈ Finset.range (power+1), (power.choose j : ℂ) •
        Grad.FullCellKernel.entry (startupDisplacementKernelData admissible family coherent index j) output input
          (fieldCellProjection inputDimension openUnitDisk input (moments (power-j)))) =
      startupAxialFrequency L ell output^power •
        Grad.FullCellKernel.entry (startupDerivativeKernelData admissible family coherent index) output input
          (fieldCellProjection inputDimension openUnitDisk input field) := by
    rw [startupDisplacementEntry_binomial]
    apply Finset.sum_congr rfl
    intro j _
    rw [same (power-j) (Nat.sub_le _ _) input]
  have result := (left.congr_fun (fun input => (terms input).symm)).unique right
  simpa only [startupKernelAxialMoment,map_sum,map_smul,startupDisplacementKernel,startupDerivativeKernel] using result

end Grad.CartesianStartup
