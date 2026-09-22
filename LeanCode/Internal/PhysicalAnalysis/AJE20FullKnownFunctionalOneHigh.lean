import AJE18KnownCoordinateNorms
import AJD24ActualBetaInverseJetBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularReconstruction
open Grad.AnnularHighInverseOrbit Grad.AnnularCrossOrbit Grad.AnnularKernelL2 Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentBoundary Grad.AnnularUniformBoundary Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule

section NormAlgebra
variable {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

theorem precompose_scaled_bound (input : X →L[ℝ] E) (mapping : E →L[ℂ] F)
    (inputSize coefficient budget : ℝ) (inputBound : ‖input‖ ≤ inputSize)
    (operatorBound : ‖mapping‖ ≤ coefficient * budget) :
    ‖realInputPrecompose input mapping‖ ≤ (coefficient * inputSize) * budget :=
  (realInputPrecompose_bound input mapping).trans
    ((mul_le_mul operatorBound inputBound (norm_nonneg input)
      ((norm_nonneg mapping).trans operatorBound)).trans_eq (by ring))
end NormAlgebra

theorem sum_scaled_bound {E : Type*} [NormedAddCommGroup E] (first second : E)
    (a b budget : ℝ) (hf : ‖first‖ ≤ a * budget) (hg : ‖second‖ ≤ b * budget) :
    ‖first + second‖ ≤ (a + b) * budget :=
  (norm_add_le _ _).trans ((add_le_add hf hg).trans_eq (by ring))

private theorem abstractDifferenceBound {E : Type*} [SeminormedAddCommGroup E] (first second : E) :
    ‖first - second‖ ≤ ‖first‖ + ‖second‖ := norm_sub_le first second

section PairingAlgebra
variable {X V D E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
local instance boundDRealInner : InnerProductSpace ℝ D := InnerProductSpace.rclikeToReal ℂ D
local instance boundERealInner : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E

theorem pairedDifference_scaled_bound (firstTest : V →L[ℝ] D) (secondTest : V →L[ℝ] E)
    (first : X →L[ℝ] D) (second : X →L[ℝ] E) (a b c d budget : ℝ)
    (testFirst : ‖firstTest‖ ≤ a) (testSecond : ‖secondTest‖ ≤ b)
    (firstBound : ‖first‖ ≤ c * budget) (secondBound : ‖second‖ ≤ d * budget) :
    ‖pairedRealOperator firstTest first - pairedRealOperator secondTest second‖ ≤
      (a * c + b * d) * budget := by
  have firstEstimate := (pairedRealOperator_bound firstTest first).trans
    (mul_le_mul testFirst firstBound (norm_nonneg first) ((norm_nonneg firstTest).trans testFirst))
  have secondEstimate := (pairedRealOperator_bound secondTest second).trans
    (mul_le_mul testSecond secondBound (norm_nonneg second) ((norm_nonneg secondTest).trans testSecond))
  calc
    ‖pairedRealOperator firstTest first - pairedRealOperator secondTest second‖ ≤
        ‖pairedRealOperator firstTest first‖ + ‖pairedRealOperator secondTest second‖ :=
          abstractDifferenceBound (E := X →L[ℝ] V →L[ℝ] ℝ)
            (pairedRealOperator firstTest first) (pairedRealOperator secondTest second)
    _ ≤ a * (c * budget) + b * (d * budget) := add_le_add firstEstimate secondEstimate
    _ = (a * c + b * d) * budget := by ring
end PairingAlgebra

/-- Positive known bulk jets use a single original primitive size at j+8. -/
theorem knownBulkOrbitJet_positive_oneHigh (parameters : PhaseParameters) (length compact : ℝ)
    (angular cell : ℕ) (orderPositive : 0 < angular + cell) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (state : RetainedInverseState parameters length compact)
      (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (tau : OrbitParameter),
      ‖knownBulkOrbitJet parameters length compact lower positive lowerHalf state angular cell tau‖ ≤
        constant * state.val.val.size (1 + (angular + cell)) := by
  obtain ⟨coefficient,nonnegative,bound⟩ := actualEliminatedOrbitJet_oneHigh parameters length compact 0 angular cell orderPositive
  refine ⟨coefficient * 4,mul_nonneg nonnegative (by norm_num),?_⟩
  intro state lower positive lowerHalf tau
  have budget : state.val.errorBudget (0 + (angular + cell)) ≤ state.val.val.size (1 + (angular + cell)) := by
    change physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (0 + (angular + cell) + 7) ≤
      1 + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (1 + (angular + cell) + 7)
    exact (physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon (by omega)).trans
      (le_add_of_nonneg_left zero_le_one)
  have operatorBound := (bound state lower positive (lowerHalf.trans (by norm_num)) tau).trans
    (mul_le_mul_of_nonneg_left budget nonnegative)
  unfold knownBulkOrbitJet
  rw [constantOrbitJet,if_neg (ne_of_gt orderPositive),add_zero]
  exact precompose_scaled_bound (knownAmbientEight parameters lower 0 0) _ 4 coefficient _
    (knownAmbientEight_norm parameters lower) operatorBound

/-- Both actual beta inverse and genuine source lift use one primitive factor,
with the original negative-half trace cost of one derivative. -/
theorem knownBoundaryOrbitJet_positive_oneHigh (parameters : PhaseParameters) (length compact : ℝ)
    (angular cell : ℕ) (orderPositive : 0 < angular + cell) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (state : RetainedInverseState parameters length compact)
      (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (tau : OrbitParameter),
      ‖knownBoundaryOrbitJet parameters length compact lower positive lowerHalf state angular cell tau‖ ≤
        constant * state.val.val.size (1 + (angular + cell)) := by
  obtain ⟨coefficient,nonnegative,bound⟩ := actualBoundaryInverseOrbitJet_positive_oneHigh parameters length compact angular cell orderPositive
  let sourceCoefficient := sourceLiftJetConstant parameters 0 0 length compact angular cell
  have sourceNonnegative : 0 ≤ sourceCoefficient := sourceLiftJetConstant_nonnegative parameters 0 0 length compact angular cell
  refine ⟨coefficient * 1 + sourceCoefficient * (3 * uniformSourceOuterConstant),
    add_nonneg (mul_nonneg nonnegative zero_le_one)
      (mul_nonneg sourceNonnegative (mul_nonneg (by norm_num) uniformSourceOuterConstant_nonnegative)),?_⟩
  intro state lower positive lowerHalf tau
  have budget : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (8 + (angular + cell)) ≤
      state.val.val.size (1 + (angular + cell)) := by
    change _ ≤ 1 + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (1 + (angular + cell) + 7)
    rw [show 1 + (angular + cell) + 7 = 8 + (angular + cell) by omega]
    exact le_add_of_nonneg_left zero_le_one
  have beta := precompose_scaled_bound (highKnownDatumProjection parameters lower 0 0)
    (actualBoundaryInverseOrbitJet parameters length compact state angular cell tau) 1 coefficient _
    (knownAmbientDatum_norm parameters lower)
    ((bound state tau).trans (mul_le_mul_of_nonneg_left budget nonnegative))
  have source := precompose_scaled_bound
    (knownAmbientSourceTuple parameters lower 0 0 positive (lowerHalf.trans_lt (by norm_num)))
    (graphSourceLiftOrbitJet parameters length compact state.outerInverseState 0 0 angular cell tau)
    (3 * uniformSourceOuterConstant) sourceCoefficient (state.val.val.size (1 + (angular + cell)))
    (knownAmbientSourceTuple_norm parameters lower positive lowerHalf)
    (graphSourceLiftOrbitJet_oneHigh parameters 0 0 length compact angular cell state.outerInverseState tau)
  exact sum_scaled_bound _ _ _ _ _ beta source

/-- Full AEK12 forcing jets have one original high primitive factor, uniformly
in the inner radius and with the original angular/cell width unchanged. -/
theorem knownFunctionalOrbitJet_positive_oneHigh (parameters : PhaseParameters) (length compact : ℝ)
    (angular cell : ℕ) (orderPositive : 0 < angular + cell) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (state : RetainedInverseState parameters length compact)
      (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
      (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
      (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) (tau : OrbitParameter),
      ‖knownFunctionalOrbitJet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
        state angular cell tau‖ ≤ constant * state.val.val.size (1 + (angular + cell)) := by
  obtain ⟨bulk,bulkNonnegative,bulkBound⟩ := knownBulkOrbitJet_positive_oneHigh parameters length compact angular cell orderPositive
  obtain ⟨boundary,boundaryNonnegative,boundaryBound⟩ := knownBoundaryOrbitJet_positive_oneHigh parameters length compact angular cell orderPositive
  refine ⟨5 * bulk + uniformOuterTraceConstant length * boundary,
    add_nonneg (mul_nonneg (by norm_num) bulkNonnegative)
      (mul_nonneg (uniformOuterTraceConstant_nonnegative length) boundaryNonnegative),?_⟩
  intro state lower positive lowerHalf lengthPositive widthHalf widthLength tau
  exact pairedDifference_scaled_bound
    ((highEnergyTestPacket parameters lower length positive lengthPositive widthHalf widthLength).restrictScalars ℝ)
    ((actualCurrentHighOuterTrace parameters lower length positive lowerHalf lengthPositive 0 0).restrictScalars ℝ)
    (knownBulkOrbitJet parameters length compact lower positive lowerHalf state angular cell tau)
    (knownBoundaryOrbitJet parameters length compact lower positive lowerHalf state angular cell tau)
    5 (uniformOuterTraceConstant length) bulk boundary (state.val.val.size (1 + (angular + cell)))
    (knownEnergyTest_norm parameters lower length positive lengthPositive widthHalf widthLength)
    (knownOuterTest_norm parameters lower length positive lowerHalf lengthPositive)
    (bulkBound state lower positive lowerHalf tau) (boundaryBound state lower positive lowerHalf tau)

end Grad.AnnularStrongOrbit
