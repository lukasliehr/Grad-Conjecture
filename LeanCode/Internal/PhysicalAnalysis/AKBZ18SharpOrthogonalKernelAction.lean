import AKBZ17ActualOriginalMixedDerivativeCarrier

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory MeasureTheory.Measure
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.CartesianState Grad.NonlinearProduct Grad.GenericCarriers Grad.Constraints

/-- The same sharp coefficient with an actual orthogonal spatial pullback.
This includes every rotation and reflection, with no norm loss. -/
def sharpOrthogonalKernelData {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (rank displacement : ℕ) (positive : 0<rank)
    (word : Fin rank → Fin 2) (index : CartesianMultiIndex)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) :
    Grad.FullCellKernel.L2KernelData (Measure.dirac (0:ℝ)) inputDimension outputDimension openUnitDisk :=
  { sharpAllocatedKernelData admissible family coherent rank displacement positive word index with
    orthogonal := fun _ => orthogonal
    invariant := fun _ => Grad.GaugeCoefficients.Radial.openUnitDisk_invariant orthogonal
    actionMeasurable := orthogonal.continuous.measurable.comp measurable_snd }

def sharpOrthogonalKernel {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (rank displacement : ℕ) (positive : 0<rank)
    (word : Fin rank → Fin 2) (index : CartesianMultiIndex)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) :=
  Grad.FullCellKernel.kernel (sharpOrthogonalKernelData admissible family coherent rank displacement positive word index orthogonal)

theorem sharpOrthogonalKernel_norm {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (rank displacement : ℕ) (positive : 0<rank)
    (word : Fin rank → Fin 2) (index : CartesianMultiIndex)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) :
    ‖sharpOrthogonalKernel admissible family coherent rank displacement positive word index orthogonal‖≤
      sharpPhaseConstant L sigma gamma rank*‖family (cartesianOrder index+displacement)‖ := by
  have bound := Grad.FullCellKernel.kernel_norm_le
    (sharpOrthogonalKernelData admissible family coherent rank displacement positive word index orthogonal)
  change ‖sharpOrthogonalKernel admissible family coherent rank displacement positive word index orthogonal‖≤
    Real.sqrt ((sharpPhaseConstant L sigma gamma rank*‖family (cartesianOrder index+displacement)‖)*
      (sharpPhaseConstant L sigma gamma rank*‖family (cartesianOrder index+displacement)‖)) at bound
  simpa only [Real.sqrt_mul_self (mul_nonneg (sharpPhaseConstant_nonnegative admissible rank) (norm_nonneg _))] using bound

/-- Apply a genuine sharp full-cell kernel to the same original weighted
input derivative. Its total input grade is c+a-d, exactly q-(b+d). -/
theorem sharpOrthogonalKernel_originalDerivative_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (phaseRank displacement inputRank : ℕ) (positive : 0<phaseRank)
    (word : Fin phaseRank → Fin 2) (index : CartesianMultiIndex)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (parameters : PhaseParameters)
    (field : ACore parameters inputDimension) (inputWord : CartesianWord inputRank) :
    ‖sharpOrthogonalKernel admissible family coherent phaseRank displacement positive word index orthogonal
      (originalMixedDerivativeCarrier parameters admissible field inputRank (phaseRank-displacement) inputWord)‖≤
    sharpPhaseConstant L sigma gamma phaseRank*‖family (cartesianOrder index+displacement)‖*
      originalGradeNorm (inputRank+(phaseRank-displacement)) field := by
  have operator := sharpOrthogonalKernel_norm admissible family coherent phaseRank displacement positive word index orthogonal
  have inputBound := originalMixedDerivativeCarrier_norm parameters admissible field inputRank (phaseRank-displacement) inputWord
  exact ((sharpOrthogonalKernel admissible family coherent phaseRank displacement positive word index orthogonal).le_opNorm _).trans
    (mul_le_mul operator inputBound (norm_nonneg _) (mul_nonneg (sharpPhaseConstant_nonnegative admissible phaseRank) (norm_nonneg _)))

end Grad.OriginalCartesianTameEstimate
