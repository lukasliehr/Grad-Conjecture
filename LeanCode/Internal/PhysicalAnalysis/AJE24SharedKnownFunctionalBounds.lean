import AJE22SharedKnownFunctionalTower
import AJE20FullKnownFunctionalOneHigh
import AJE21FullKnownFunctionalBaseBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open scoped ContDiff
namespace Grad.AnnularStrongOrbit
open Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.Allocation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.AnnularStrongData Grad.AnnularHighInverseOrbit Grad.AnnularCrossOrbit Grad.AnnularKernelL2
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse
attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

section Restriction
variable {X W V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem sourceTestRestriction_bound (inclusion : V →L[ℝ] W) (bound : ∀ test, ‖inclusion test‖ ≤ ‖test‖)
    (mapping : X →L[ℝ] W →L[ℝ] ℝ) : ‖operatorTestRestriction inclusion mapping‖ ≤ ‖mapping‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg mapping)
  intro data
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg mapping) (norm_nonneg data))
  intro test
  exact ((mapping data).le_opNorm (inclusion test)).trans
    (mul_le_mul (mapping.le_opNorm data) (bound test) (norm_nonneg _) (mul_nonneg (norm_nonneg mapping) (norm_nonneg data)))
theorem restrictedSourceTower_bound (tower : RealOrbitTower (X →L[ℝ] W →L[ℝ] ℝ))
    (inclusion : V →L[ℝ] W) (bound : ∀ test, ‖inclusion test‖ ≤ ‖test‖)
    (angular cell : ℕ) (tau : OrbitParameter) :
    ‖(tower.map (F := X →L[ℝ] V →L[ℝ] ℝ) (operatorTestRestriction (X := X) inclusion)).jet angular cell tau‖ ≤ ‖tower.jet angular cell tau‖ :=
  sourceTestRestriction_bound inclusion bound (tower.jet angular cell tau)
end Restriction

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) (state : RetainedInverseState parameters length compact)

theorem sharedKnownZeroFunctionalOrbitJet_bound (angular cell : ℕ) (tau : OrbitParameter) :
    ‖sharedKnownZeroFunctionalOrbitJet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau‖ ≤
      ‖knownFunctionalOrbitJet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau‖ := by
  have restricted := restrictedSourceTower_bound
    (sharedKnownFunctionalTower parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    (annularZeroRealInclusion lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)
    (fun test => le_rfl) angular cell tau
  exact restricted.trans (sharedKnownFunctionalOrbitJet_bound parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau)

theorem sharedKnownZeroFunctionalOrbitJet_positive_oneHigh (angular cell : ℕ) (orderPositive : 0 < angular + cell) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (state : RetainedInverseState parameters length compact)
      (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
      (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
      (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) (tau : OrbitParameter),
      ‖sharedKnownZeroFunctionalOrbitJet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
        state angular cell tau‖ ≤ constant * state.val.val.size (1 + (angular + cell)) := by
  obtain ⟨constant,nonnegative,bound⟩ := knownFunctionalOrbitJet_positive_oneHigh parameters length compact angular cell orderPositive
  exact ⟨constant,nonnegative,fun state lower positive lowerHalf lengthPositive widthHalf widthLength tau =>
    (sharedKnownZeroFunctionalOrbitJet_bound parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau).trans
      (bound state lower positive lowerHalf lengthPositive widthHalf widthLength tau)⟩

theorem sharedKnownZeroFunctionalOrbitJet_base_bound :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (state : RetainedInverseState parameters length compact)
      (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
      (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
      (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
      (_small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ 1) (tau : OrbitParameter),
      ‖sharedKnownZeroFunctionalOrbitJet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 tau‖ ≤ constant := by
  obtain ⟨constant,nonnegative,bound⟩ := knownFunctionalOrbitJet_base_bound parameters length compact
  exact ⟨constant,nonnegative,fun state lower positive lowerHalf lengthPositive widthHalf widthLength small tau =>
    (sharedKnownZeroFunctionalOrbitJet_bound parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 tau).trans
      (bound state lower positive lowerHalf lengthPositive widthHalf widthLength small tau)⟩

end Grad.AnnularStrongOrbit
