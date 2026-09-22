import AKBZ12SharpOriginalPhaseJets

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.AnalyticWeights.Higher Grad.AnalyticWeights.Calculus
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation

/-- A raw b-th coefficient derivative with exactly d displacement moments. -/
def sharpCoefficientIndex (index : CartesianMultiIndex) (displacement : ℕ) :
    DerivativeIndex (cartesianOrder index+displacement) :=
  ⟨(⟨index.1, by unfold cartesianOrder; omega⟩,
    ⟨index.2, by unfold cartesianOrder; omega⟩), by
      change index.1+index.2≤cartesianOrder index+displacement
      unfold cartesianOrder
      omega⟩

theorem sharpCoefficientIndex_order (index : CartesianMultiIndex) (displacement : ℕ) :
    derivativeOrder (sharpCoefficientIndex index displacement)=cartesianOrder index := rfl

/-- The original envelope and precisely d frequencies cost grade b+d of
one coherent actual coefficient family. -/
theorem sharpCoefficientDisplacement_bound {L sigma gamma ell : ℝ}
    {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : CartesianMultiIndex) (displacement : ℕ)
    (shift : ℤ) (point : ClosedDisk) :
    scaledCellWeight L ell shift^displacement*originalEnvelope sigma gamma ell shift point.val*
      ‖rawFamilyDerivative family shift index point‖ ≤
    ‖weightedDerivative (family (cartesianOrder index+displacement)) shift
      (sharpCoefficientIndex index displacement)‖ := by
  have bound := coefficientDerivative_scaled_norm
    (family (cartesianOrder index+displacement)) shift (sharpCoefficientIndex index displacement) point
  rw [coherent_derivative_raw family coherent] at bound
  have same : derivativeMultiIndex (sharpCoefficientIndex index displacement)=index := rfl
  simpa only [coefficientScale, sharpCoefficientIndex_order, Nat.add_sub_cancel_left, same, mul_comm] using bound

/-- The literal positive phase/coefficient product keeps every displacement
allocation. Its d-th term uses coefficient grade b+d and input reserve a-d. -/
theorem sharpActualPhaseCoefficient_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (rank : ℕ) (positive : 0<rank)
    (word : Fin rank → Fin 2) (index : CartesianMultiIndex)
    (input shift : ℤ) (point : ClosedDisk) (value : Grad.GenericCarriers.PhysicalValue inputDimension) :
    ‖apRatioDerivative sigma gamma ell rank word input shift point •
      ((rawFamilyDerivative family shift index point) value)‖ ≤
    sharpPhaseConstant L sigma gamma rank*∑ displacement ∈ Finset.Icc 1 rank,
      ‖weightedDerivative (family (cartesianOrder index+displacement)) shift
        (sharpCoefficientIndex index displacement)‖*
      (scaledCellWeight L ell input^(rank-displacement)*‖value‖) := by
  have phase := (orderedDerivative_norm_le rank word _ point.val).trans
    (sharpOriginalPhase_derivative_bound admissible rank positive input shift point)
  have constant := sharpPhaseConstant_nonnegative admissible rank
  have envelope : 0≤originalEnvelope sigma gamma ell shift point.val := (Real.exp_pos _).le
  have inputNonnegative := scaledCellWeight_nonnegative L ell input
  have shiftNonnegative := scaledCellWeight_nonnegative L ell shift
  have coefficient := norm_nonneg (rawFamilyDerivative family shift index point)
  have action := (rawFamilyDerivative family shift index point).le_opNorm value
  rw [norm_smul]
  calc
    _ ≤ (sharpPhaseConstant L sigma gamma rank*originalEnvelope sigma gamma ell shift point.val*
        ∑ displacement ∈ Finset.Icc 1 rank,
          scaledCellWeight L ell shift^displacement*scaledCellWeight L ell input^(rank-displacement))*
        (‖rawFamilyDerivative family shift index point‖*‖value‖) :=
      mul_le_mul phase action (norm_nonneg _) (by positivity)
    _ = sharpPhaseConstant L sigma gamma rank*∑ displacement ∈ Finset.Icc 1 rank,
        (scaledCellWeight L ell shift^displacement*originalEnvelope sigma gamma ell shift point.val*
          ‖rawFamilyDerivative family shift index point‖)*
        (scaledCellWeight L ell input^(rank-displacement)*‖value‖) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro displacement membership
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun displacement membership =>
      mul_le_mul_of_nonneg_right (sharpCoefficientDisplacement_bound family coherent index displacement shift point)
        (mul_nonneg (pow_nonneg (scaledCellWeight_nonnegative L ell input) _) (norm_nonneg _))) constant

end Grad.OriginalCartesianTameEstimate
