import AKBZ14ExactPhaseDisplacementSplit
import FullCellKernelProof

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.AnalyticWeights.Higher Grad.AnalyticWeights.Calculus
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation

/-- Genuine d-th phase allocation: coefficient grade b+d, with no hidden
high input reserve. The missing a-d frequencies are restored exactly by BZ14. -/
theorem sharpAllocatedCoefficient_point_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (rank displacement : ℕ) (positive : 0<rank)
    (word : Fin rank → Fin 2) (index : CartesianMultiIndex)
    (input shift : ℤ) (point : ClosedDisk) :
    ‖sharpAllocatedCoefficient family rank displacement word index input shift point‖ ≤
      sharpPhaseConstant L sigma gamma rank*
        ‖weightedDerivative (family (cartesianOrder index+displacement)) shift
          (sharpCoefficientIndex index displacement)‖ := by
  have denominator := sharpPhaseDenominator_pos L ell rank positive input shift
  have constant := sharpPhaseConstant_nonnegative admissible rank
  have shiftNonnegative := scaledCellWeight_nonnegative L ell shift
  have phase := (orderedDerivative_norm_le rank word _ point.val).trans
    (sharpOriginalPhase_derivative_bound admissible rank positive input shift point)
  have normalized : |apRatioDerivative sigma gamma ell rank word input shift point|/
      sharpPhaseDenominator L ell rank input shift ≤
      sharpPhaseConstant L sigma gamma rank*originalEnvelope sigma gamma ell shift point.val := by
    apply (div_le_iff₀ denominator).mpr
    exact phase
  have coefficient := sharpCoefficientDisplacement_bound family coherent index displacement shift point
  change ‖((_ : ℝ) : ℂ) • rawFamilyDerivative family shift index point‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_nonneg (pow_nonneg shiftNonnegative _), abs_of_pos denominator]
  calc
    _ = (|apRatioDerivative sigma gamma ell rank word input shift point|/
      sharpPhaseDenominator L ell rank input shift)*scaledCellWeight L ell shift^displacement*
        ‖rawFamilyDerivative family shift index point‖ := by ring
    _ ≤ (sharpPhaseConstant L sigma gamma rank*originalEnvelope sigma gamma ell shift point.val)*
      scaledCellWeight L ell shift^displacement*‖rawFamilyDerivative family shift index point‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right normalized (pow_nonneg shiftNonnegative _)) (norm_nonneg _)
    _ = sharpPhaseConstant L sigma gamma rank*(scaledCellWeight L ell shift^displacement*
      originalEnvelope sigma gamma ell shift point.val*‖rawFamilyDerivative family shift index point‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left coefficient constant

theorem sharpAllocatedCoefficient_norm_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (rank displacement : ℕ) (positive : 0<rank)
    (word : Fin rank → Fin 2) (index : CartesianMultiIndex) (input shift : ℤ) :
    ‖sharpAllocatedCoefficient family rank displacement word index input shift‖ ≤
      sharpPhaseConstant L sigma gamma rank*
        ‖weightedDerivative (family (cartesianOrder index+displacement)) shift
          (sharpCoefficientIndex index displacement)‖ :=
  (ContinuousMap.norm_le (sharpAllocatedCoefficient family rank displacement word index input shift)
    (mul_nonneg (sharpPhaseConstant_nonnegative admissible rank)
      (norm_nonneg (weightedDerivative (family (cartesianOrder index+displacement)) shift
        (sharpCoefficientIndex index displacement))))).mpr
    (sharpAllocatedCoefficient_point_bound admissible family coherent rank displacement positive word index input shift)

end Grad.OriginalCartesianTameEstimate
