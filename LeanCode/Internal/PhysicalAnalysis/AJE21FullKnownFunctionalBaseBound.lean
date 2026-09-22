import AJE20FullKnownFunctionalOneHigh
import AJE17ExactFullKnownFunctionalOrbit

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

private theorem bulkScalarBound (coefficient size known auxiliary data : ℝ) (positive : 0 ≤ coefficient)
    (knownNonnegative : 0 ≤ known) (sizeBound : size ≤ 2) (knownBound : known ≤ data) (auxiliaryBound : auxiliary ≤ data) :
    4 * coefficient * size * known + 3 * auxiliary ≤ (8 * coefficient + 3) * data := by
  nlinarith [mul_le_mul_of_nonneg_left knownBound (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) positive),
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left sizeBound (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) positive)) knownNonnegative]

theorem knownBulkOrbitJet_base_bound (parameters : PhaseParameters) (length compact : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (state : RetainedInverseState parameters length compact)
      (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
      (_small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ 1) (tau : OrbitParameter),
      ‖knownBulkOrbitJet parameters length compact lower positive lowerHalf state 0 0 tau‖ ≤ constant := by
  refine ⟨8 * eliminatedBulkConstant parameters length compact 0 + 3,
    add_nonneg (mul_nonneg (by norm_num) (eliminatedBulkConstant_nonnegative parameters length compact 0)) (by norm_num),?_⟩
  intro state lower positive lowerHalf small tau
  have sizeBound : state.val.val.size 0 ≤ 2 := by
    have monotone := physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon (by norm_num : 7 ≤ 8)
    change 1 + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 7 ≤ 2
    linarith
  apply ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg (mul_nonneg (by norm_num) (eliminatedBulkConstant_nonnegative parameters length compact 0)) (by norm_num))
  intro data
  rw [knownBulkOrbit_apply parameters length compact lower positive lowerHalf state tau data]
  let translated := highKnownAmbientTranslation parameters lower 0 0 (-tau) data
  change ‖orbitLpEquivalence (RadialL2 3 lower) tau
    (actualHighKnownBulkOutput parameters length compact lower positive (lowerHalf.trans (by norm_num)) state
      translated.ofLp.1.ofLp.1 translated.ofLp.1.ofLp.2)‖ ≤ _
  rw [(orbitLpEquivalence (RadialL2 3 lower) tau).norm_map]
  have bound := actualHighKnownBulkOutput_bound parameters length compact lower positive lowerHalf state
    translated.ofLp.1.ofLp.1 translated.ofLp.1.ofLp.2
  exact bound.trans (bulkScalarBound _ _ _ _ _
    (eliminatedBulkConstant_nonnegative parameters length compact 0) (norm_nonneg _) sizeBound
    ((knownAmbientWeighted_bound parameters lower translated).trans_eq
      ((highKnownAmbientTranslation parameters lower 0 0 (-tau)).norm_map data))
    ((knownAmbientAuxiliary_bound parameters lower translated).trans_eq
      ((highKnownAmbientTranslation parameters lower 0 0 (-tau)).norm_map data)))

theorem knownBoundaryOrbitJet_base_bound (parameters : PhaseParameters) (length compact : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (state : RetainedInverseState parameters length compact)
      (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
      (_small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ 1) (tau : OrbitParameter),
      ‖knownBoundaryOrbitJet parameters length compact lower positive lowerHalf state 0 0 tau‖ ≤ constant := by
  obtain ⟨coefficient,nonnegative,bound⟩ := actualBoundaryInverseOrbit_zero_uniform parameters length compact
  let sourceCoefficient := 2 * sourceLiftJetConstant parameters 0 0 length compact 0 0
  have sourceNonnegative : 0 ≤ sourceCoefficient := mul_nonneg (by norm_num)
    (sourceLiftJetConstant_nonnegative parameters 0 0 length compact 0 0)
  refine ⟨coefficient * 1 + sourceCoefficient * (3 * uniformSourceOuterConstant),
    add_nonneg (mul_nonneg nonnegative zero_le_one)
      (mul_nonneg sourceNonnegative (mul_nonneg (by norm_num) uniformSourceOuterConstant_nonnegative)),?_⟩
  intro state lower positive lowerHalf small tau
  have sizeBound : state.outerInverseState.val.val.size (0 + 0 + 1 + (0 + 0)) ≤ 2 := by
    change 1 + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ 2
    linarith
  have sourceBound := (graphSourceLiftOrbitJet_oneHigh parameters 0 0 length compact 0 0 state.outerInverseState tau).trans
    (mul_le_mul_of_nonneg_left sizeBound (sourceLiftJetConstant_nonnegative parameters 0 0 length compact 0 0))
  have beta := precompose_scaled_bound (highKnownDatumProjection parameters lower 0 0)
    (actualBoundaryInverseOrbitJet parameters length compact state 0 0 tau) 1 coefficient 1
    (knownAmbientDatum_norm parameters lower) ((bound state small tau).trans_eq (mul_one coefficient).symm)
  have source := precompose_scaled_bound
    (knownAmbientSourceTuple parameters lower 0 0 positive (lowerHalf.trans_lt (by norm_num)))
    (graphSourceLiftOrbitJet parameters length compact state.outerInverseState 0 0 0 0 tau)
    (3 * uniformSourceOuterConstant) sourceCoefficient 1
    (knownAmbientSourceTuple_norm parameters lower positive lowerHalf)
    (sourceBound.trans_eq (by dsimp only [sourceCoefficient]; ring))
  exact (sum_scaled_bound _ _ _ _ _ beta source).trans_eq (mul_one _)

theorem knownFunctionalOrbitJet_base_bound (parameters : PhaseParameters) (length compact : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (state : RetainedInverseState parameters length compact)
      (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
      (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
      (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
      (_small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ 1) (tau : OrbitParameter),
      ‖knownFunctionalOrbitJet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
        state 0 0 tau‖ ≤ constant := by
  obtain ⟨bulk,bulkNonnegative,bulkBound⟩ := knownBulkOrbitJet_base_bound parameters length compact
  obtain ⟨boundary,boundaryNonnegative,boundaryBound⟩ := knownBoundaryOrbitJet_base_bound parameters length compact
  refine ⟨5 * bulk + uniformOuterTraceConstant length * boundary,
    add_nonneg (mul_nonneg (by norm_num) bulkNonnegative)
      (mul_nonneg (uniformOuterTraceConstant_nonnegative length) boundaryNonnegative),?_⟩
  intro state lower positive lowerHalf lengthPositive widthHalf widthLength small tau
  exact (pairedDifference_scaled_bound
    ((highEnergyTestPacket parameters lower length positive lengthPositive widthHalf widthLength).restrictScalars ℝ)
    ((actualCurrentHighOuterTrace parameters lower length positive lowerHalf lengthPositive 0 0).restrictScalars ℝ)
    (knownBulkOrbitJet parameters length compact lower positive lowerHalf state 0 0 tau)
    (knownBoundaryOrbitJet parameters length compact lower positive lowerHalf state 0 0 tau)
    5 (uniformOuterTraceConstant length) bulk boundary 1
    (knownEnergyTest_norm parameters lower length positive lengthPositive widthHalf widthLength)
    (knownOuterTest_norm parameters lower length positive lowerHalf lengthPositive)
    ((bulkBound state lower positive lowerHalf small tau).trans_eq (mul_one bulk).symm)
    ((boundaryBound state lower positive lowerHalf small tau).trans_eq (mul_one boundary).symm)).trans_eq (mul_one _)

end Grad.AnnularStrongOrbit
