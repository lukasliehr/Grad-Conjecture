import AKCB14SameFullCellAxialMoment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

theorem startupKernelAxialMoment_ae {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade) (power : ℕ)
    (field : StartupL2 inputDimension) (moments : ℕ → StartupL2 inputDimension)
    (same : ∀ j ≤ power, ∀ cell : ℤ,
      fieldCellProjection inputDimension openUnitDisk cell (moments j) =
        startupAxialFrequency L ell cell^j • fieldCellProjection inputDimension openUnitDisk cell field) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      startupKernelAxialMoment admissible family coherent index power moments point cell =
      startupAxialFrequency L ell cell^power •
        startupDerivativeKernel admissible family coherent index field point cell := by
  apply ae_all_iff.mpr
  intro cell
  filter_upwards [fieldCellProjection_ae outputDimension openUnitDisk
    (startupKernelAxialMoment admissible family coherent index power moments),
    fieldCellProjection_ae outputDimension openUnitDisk (startupDerivativeKernel admissible family coherent index field),
    Lp.coeFn_smul (startupAxialFrequency L ell cell^power)
      (fieldCellProjection outputDimension openUnitDisk cell (startupDerivativeKernel admissible family coherent index field))]
    with point left right scaled
  have value := congrArg (fun f : Lp (PhysicalValue outputDimension) 2 (volume.restrict openUnitDisk) => f point)
    (startupKernelAxialMoment_projection admissible family coherent index power field moments same cell)
  rw [left cell,scaled,Pi.smul_apply,right cell] at value
  exact value

/-- Explicit finite bound for the constructed axial moment. This is a
coarse membership bound; the sharp one-high allocation is a separate result. -/
theorem startupKernelAxialMoment_norm {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade) (power : ℕ)
    (moments : ℕ → StartupL2 inputDimension) :
    ‖startupKernelAxialMoment admissible family coherent index power moments‖ ≤
      ∑ j ∈ Finset.range (power+1), (power.choose j : ℝ) *
        (startupDerivativeConstant L sigma gamma (startupCellReserveIndex j index) * ‖family (grade+j)‖ *
          ‖moments (power-j)‖) := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_smul,Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact ((startupDisplacementKernel admissible family coherent index j).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (startupDisplacementKernel_norm admissible family coherent index j) (norm_nonneg _))

end Grad.CartesianStartup
