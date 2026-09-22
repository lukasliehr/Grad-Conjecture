import AJF26SameSharedKnownHighFlux
import AJB13SameLowInverseSmoothness
import AIT9OneOriginalCoupledNeighborhood

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularReconstruction Grad.CartesianState Grad.AnnularKernelOrbit
open Grad.AnnularStrongData Grad.AnnularStrongOrbit Grad.AnnularCoupledOrbit Grad.AnnularCoupledInverse
open Grad.AnnularLowEnergy Grad.AnnularLowOrbit Grad.AnnularCurrentLow Grad.AnnularKnownLow
open Grad.GaugeCoefficients.Physical.Allocation

section Generic
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

theorem operator_restrictScalars_contDiff (family : P → E →L[ℂ] F) (smooth : ContDiff ℝ ∞ family) :
    ContDiff ℝ ∞ (fun point => (family point).restrictScalars ℝ) :=
  (ContinuousLinearMap.restrictScalarsIsometry ℂ E F ℝ ℝ).toContinuousLinearMap.contDiff.comp smooth

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] in
theorem sameTransportedOperator_apply (input : E ≃ₗᵢ[ℂ] E) (output : F ≃ₗᵢ[ℂ] F)
    (inverse : E →L[ℂ] F) (data original : E) (same : data = input original) :
    output (inverse (input.symm data)) = output (inverse original) := by
  rw [same, input.symm_apply_apply]
end Generic

attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
  (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
  (state : RetainedInverseState parameters L compact)
  (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters L compact)

/-- The SAME actual low inverse receives the full known low right-hand side
of the once-prescribed strong datum. -/
def sharedKnownLowResponseOrbit (tau : OrbitParameter) :
    StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 →L[ℝ] lowEnergyGraph lower L positive :=
  ((actualLowInverseOrbit parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state tau).restrictScalars ℝ).comp
    (sharedLowDataOrbitJet parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 0 tau)

include small in
theorem sharedKnownLowResponseOrbit_contDiff :
    ContDiff ℝ ∞ (sharedKnownLowResponseOrbit parameters L compact lower positive lowerHalf lengthPositive state) := by
  have inverse := operator_restrictScalars_contDiff (P := OrbitParameter) (E := LowEnergyData lower)
    (F := lowEnergyGraph lower L positive)
    (actualLowInverseOrbit parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state)
    (actualLowInverseOrbit_contDiff parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state
      (coupledPrimitive_lowSmall parameters L compact state small))
  have data := realOperatorComposition_contDiff
    (knownLowDataOrbitJet parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 0)
    (fun _ : OrbitParameter => strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (knownLowDataOrbitJet_contDiff parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 0) contDiff_const
  exact realOperatorComposition_contDiff _ _ inverse data

/-- Exact original rho-normalized low graph response to the SAME translated
strong source. No independent translated coefficient state is introduced. -/
theorem sharedKnownLowResponseOrbit_apply (tau : OrbitParameter)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    sharedKnownLowResponseOrbit parameters L compact lower positive lowerHalf lengthPositive state tau data =
      lowTranslation lower L positive tau
        (knownLowResponse parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state
          (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
            (strongDataTranslation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 (-tau) data))) := by
  let original := strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
    (strongDataTranslation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 (-tau) data)
  let source := knownLowDataMap parameters L compact lower positive (lowerHalf.trans (by norm_num)) state
  let translated := strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data
  have first := knownLowDataOrbit_apply parameters L compact lower positive (lowerHalf.trans (by norm_num)) state tau translated
  have sourceSame := congrArg (fun datum : KnownLowData lower => lowDataTranslationEquivalence lower tau (source datum))
    (strongToLow_translation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 (-tau) data).symm
  have actual := first.trans sourceSame
  exact sameTransportedOperator_apply (lowDataTranslationEquivalence lower tau)
    (lowTranslationEquivalence lower L positive tau)
    (lowCurrentInverse parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state)
    _ (source original) actual

end Grad.AnnularHighGenerators
