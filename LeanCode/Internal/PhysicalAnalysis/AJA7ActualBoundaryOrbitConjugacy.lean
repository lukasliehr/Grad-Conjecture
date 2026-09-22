import AJA4ActualBulkOrbitConjugacy
import AJA6ActualBoundaryFormOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularHighInverseOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularKernelL2 Grad.AnnularCurrentEnergy Grad.AnnularCurrentBoundary
open Grad.AnnularUniformBoundary Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (state : RetainedInverseState parameters L compact)

theorem retainedEnergyInput_translation (tau : OrbitParameter) (field : annularEnergySpace lower L positive) :
    retainedEnergyInput parameters L lower positive lowerHalf lengthPositive
      (energyTranslation lower L positive tau field) =
      orbitLpAction (ComplexEuclidean 3) tau
        (retainedEnergyInput parameters L lower positive lowerHalf lengthPositive field) := by
  change originalRetainedBoundaryVector parameters L 0 0
    (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0
      (energyTranslation lower L positive tau field)) = _
  rw [actualOuterTrace_translation, originalRetainedTuple_translation]
  rfl

/-- The actual boundary coefficient orbit is exactly the genuine energy
pullback of the SAME physical current boundary form. -/
theorem highBoundaryFormOrbit_pullback (tau : OrbitParameter) (field test : annularEnergySpace lower L positive) :
    highBoundaryFormOrbitJet parameters L lower positive lowerHalf lengthPositive compact state tau 0 0 field test =
      highBoundaryRealForm parameters L compact lower positive lowerHalf lengthPositive state
        (energyTranslation lower L positive (-tau) field) (energyTranslation lower L positive (-tau) test) := by
  change highBoundaryPairing parameters L lower positive lowerHalf lengthPositive
    (boundaryOrbitJetAction parameters 0 0 (actualRetainedBoundaryLiftKernel state.outerInverseState) tau 0 0) field test = _
  rw [highBoundaryPairing_literal, highBoundaryRealForm_literal]
  unfold boundaryOrbitJetAction
  rw [kernelOrbitJet_zero, fullNegativeKernelAction_orbit]
  simp only [ContinuousLinearMap.comp_apply]
  rw [orbitLp_inner_move, ← actualOuterTrace_translation parameters lower L positive lowerHalf lengthPositive 0 0 (-tau) test,
    ← retainedEnergyInput_translation parameters L lower positive lowerHalf lengthPositive (-tau) field]
  unfold actualCurrentHighBoundaryFormValue
  rw [actualCurrentHighBoundaryD_kernel]
  rfl

/-- All boundary orbital jets vanish with the physical error and have one
original B_(j+8) factor, uniformly in the inner radius. -/
theorem highBoundaryFormOrbitJet_oneHigh (angular cell : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
        (state : RetainedInverseState parameters L compact) (tau : OrbitParameter),
      ‖highBoundaryFormOrbitJet parameters L lower positive lowerHalf lengthPositive compact state tau angular cell‖ ≤
        constant * state.val.errorBudget (1 + (angular + cell)) := by
  let momentConstant := retainedBoundaryLiftMomentConstant parameters L compact (1 + (angular + cell))
  let pairingConstant := originalRetainedBoundaryConstant parameters 0 0 * uniformOuterTraceConstant L ^ 2
  have firstNonnegative : 0 ≤ momentConstant := retainedBoundaryLiftMomentConstant_nonnegative parameters L compact _
  have secondNonnegative : 0 ≤ pairingConstant := mul_nonneg
    (originalRetainedBoundaryConstant_nonnegative parameters 0 0) (sq_nonneg _)
  refine ⟨pairingConstant * momentConstant, mul_nonneg secondNonnegative firstNonnegative, ?_⟩
  intro lower positive lowerHalf lengthPositive state tau
  change ‖highBoundaryPairing parameters L lower positive lowerHalf lengthPositive
    (boundaryOrbitJetAction parameters 0 0 (actualRetainedBoundaryLiftKernel state.outerInverseState) tau angular cell)‖ ≤ _
  have moment := retainedBoundaryLiftMomentConstant_bound parameters L compact (1 + (angular + cell)) state.outerInverseState
  have action := boundaryOrbitJetAction_norm_le parameters 0 0
    (actualRetainedBoundaryLiftKernel state.outerInverseState) tau angular cell
  simp only [zero_add] at action
  have paired := highBoundaryPairing_norm_bound parameters L lower positive lowerHalf lengthPositive
    (boundaryOrbitJetAction parameters 0 0 (actualRetainedBoundaryLiftKernel state.outerInverseState) tau angular cell)
  exact paired.trans ((mul_le_mul_of_nonneg_left (action.trans moment) secondNonnegative).trans_eq (by
    change pairingConstant * (momentConstant * state.val.errorBudget (1 + (angular + cell))) = _
    ring))

end Grad.AnnularHighInverseOrbit
