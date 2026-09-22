import AKZ1ActualInverseTransposeFamily

noncomputable section
set_option autoImplicit false
namespace Grad.ActualPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollar
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

/-- A state-independent nonnegative numerical envelope of the accepted
literal inverse-transpose profile. The actual matrix family is unchanged. -/
def originalInverseTransposeAbsoluteProfile (parameters : PhaseParameters) (length : ℝ) : EstimateProfile :=
  ⟨fun grade => |(originalInverseTransposeProfile parameters length).fixed grade|,
    fun grade => |(originalInverseTransposeProfile parameters length).deviation grade|⟩

theorem originalInverseTransposeFamily_absoluteEstimate (parameters : PhaseParameters)
    (length rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length) :
    FamilyEstimate parameters field rho epsilon 4 (originalInverseTransposeAbsoluteProfile parameters length)
      (originalInverseTransposeFamily parameters length epsilon field)
      (transposeFamily (unitDiskAdmissible parameters)
        (constantFamily 1 parameters.sigma0 parameters.gamma 1 Grad.GaugeCoefficients.Physical.Frame.referenceFrame)) := by
  let original := originalInverseTransposeFamily_estimate parameters length rho epsilon field small
  exact {
    actualCoherent := original.actualCoherent
    referenceCoherent := original.referenceCoherent
    fixedNonnegative := fun _ => abs_nonneg _
    deviationNonnegative := fun _ => abs_nonneg _
    referenceBound := fun grade => (original.referenceBound grade).trans (le_abs_self _)
    deviationBound := fun grade => (original.deviationBound grade).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _)
        (physicalBudget_nonnegative parameters field rho epsilon (4+grade))) }

end Grad.ActualPhysicalField
