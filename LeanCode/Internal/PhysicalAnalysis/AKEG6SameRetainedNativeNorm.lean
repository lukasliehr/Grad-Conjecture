import AKEG5ActualPhysicalUnitNativeRows
import AKAN2NativeCompatibleJetFamily
import AKM15SameGradedRestrictionCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.FinitePhysicalJetLift
open Grad.ActualPuncturedFamily
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum Grad.AnnularStrongOrbit
open Grad.AnnularForwardTraces Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularRestriction
open Grad.AnnularExhaustionEstimate Grad.AnnularWeakExhaustion Grad.AnnularFullSource
open Grad.AnnularHighGenerators Grad.AnnularCrossOrbit Grad.ActualAnnularExhaustion
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.SourceCollarFullSource Grad.ExhaustionSourceAllocation
open Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  sourceRadialRealInner sourceGraphRealInner sourceKnownGraphRealInner
  weakRetainedRealInner weakSourcesRealInner weakFiveRealInner

attribute [local instance] weakWeightedRetainedRealInner
attribute [local instance] Grad.AnnularStrongOrbit.knownAmbientNormed Grad.AnnularStrongOrbit.knownAmbientSeminormed Grad.AnnularStrongOrbit.knownAmbientRealNormed Grad.AnnularStrongOrbit.knownAmbientRealModule
  Grad.AnnularStrongOrbit.strongCarrierNormed Grad.AnnularStrongOrbit.strongCarrierSeminormed Grad.AnnularStrongOrbit.strongCarrierRealNormed Grad.AnnularStrongOrbit.strongCarrierRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace
  Grad.AnnularCrossOrbit.coupledNormed Grad.AnnularCrossOrbit.coupledSeminormed
  Grad.AnnularCrossOrbit.coupledComplexNormed Grad.AnnularCrossOrbit.coupledComplexModule
  Grad.AnnularCrossOrbit.coupledRealNormed Grad.AnnularCrossOrbit.coupledRealModule
  Grad.AnnularCrossOrbit.coupledOperatorRealNormed Grad.AnnularCrossOrbit.coupledOperatorRealModule




open Grad.ClosedJets Grad.AnnularVariational Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentInverse Grad.AnnularCurrentSource Grad.AnnularKernelL2 Grad.AnnularCrossMaps
open Grad.AnnularUniformBoundary Grad.AnnularKnownLow Grad.AnnularLowEnergy Grad.AnnularCurrentLow

/-- The actual independent source coefficient has a strictly positive fixed reserve. -/
theorem nativeIndependentDataConstant_positive (parameters : PhaseParameters) (length compact : ℝ) :
    0 < independentCoupledDataConstant parameters length compact := by
  have bulk := eliminatedBulkConstant_nonnegative parameters length compact 0
  have source := actualHighKnownBF13BallConstant_nonnegative parameters length compact
  have lift : 0 ≤ uniformInnerLiftConstant length := Real.sqrt_nonneg _
  have high : 0 < fullKnownHighBallConstant parameters length compact := by
    unfold fullKnownHighBallConstant
    positivity
  exact mul_pos (by norm_num) (add_pos_of_pos_of_nonneg high
    (knownLowResponseConstant_nonnegative parameters length compact))

variable {parameters : PhaseParameters} {length compact : ℝ} {lengthPositive : 0 < length}
    {widthHalf : parameters.gamma ≤ 1 / 2} {widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)}
    {state : RetainedInverseState parameters length compact}
    {small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact}
    {source : SmoothQuotient parameters} {flat : IsFlat source}


/-- Grade zero is the same retained observation, so its norm is contained
in the already retained native norm, with no new solve or selection. -/
theorem NativeCartesianFamily.retainedNorm_le_nativeNorm
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (index : ℕ) :
    originalWeightedRetainedNorm parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive
      (family.limit index).ofLp.1 ≤ family.nativeNorm index 0 := by
  let observed := originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length
    (originalExhaustionRadius_positive length lengthPositive index)
    ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (family.limit index)
  have selfInserted : CoupledInsertedGrade (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index) lengthPositive 0 observed observed := by
    constructor
    · intro mode
      simp only [pow_zero,Complex.ofReal_one,one_smul]
    constructor
    · intro coordinate mode
      simp only [pow_zero,Complex.ofReal_one,one_smul]
    · intro coordinate mode
      simp only [pow_zero,Complex.ofReal_one,one_smul]
  have same := coupledInsertedGrade_unique (originalExhaustionRadius length index) length
    (originalExhaustionRadius_positive length lengthPositive index) lengthPositive 0 observed
    (family.graded index 0) observed (family.inserted index 0) selfInserted
  have normSame : originalWeightedRetainedNorm parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive
      (family.limit index).ofLp.1 = ‖family.graded index 0‖ := by
    exact congrArg (fun value : CoupledSpace (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index) lengthPositive => ‖value‖) same.symm
  rw [normSame]
  unfold NativeCartesianFamily.nativeNorm exhaustionDatumNorm originalWeightedDatumNorm
  exact le_add_of_nonneg_left (norm_nonneg _)

end Grad.FinitePhysicalJetLift
