import AKCD4TwoNativeEnergyInputs
import AKAN4LiteralOriginalJetExhaustionConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.OriginalCartesianTameEstimate
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




open Grad.FinitePhysicalJetLift Grad.ActualSmoothPhysicalField Grad.ActualNativeCellMoments
open Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.ClosedJets Grad.SourceBoundaryTrace
open MeasureTheory
open scoped ENNReal BigOperators
attribute [local irreducible] originalWeightedDatum

variable {parameters : PhaseParameters} {length compact : ℝ} {lengthPositive : 0 < length}
    {widthHalf : parameters.gamma ≤ 1 / 2} {widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)}
    {state : RetainedInverseState parameters length compact}
    {small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact}
    {source : SmoothQuotient parameters} {flat : IsFlat source}

def nativeSevenCurves
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (index : ℕ) :
    SmoothLowPhysicalRow parameters (originalExhaustionRadius length index)
      (originalExhaustionRadius_positive length lengthPositive index)
      (originalSevenPacket parameters (originalExhaustionRadius length index) length
        (originalExhaustionRadius_positive length lengthPositive index)
        ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive
        (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0)
        (family.limit index).ofLp.1) :=
  actualCartesianSevenCurves parameters length compact (originalExhaustionRadius length index)
    (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index)
    lengthPositive widthHalf widthLength state
    (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    source flat (family.limit index) (family.equations index).1 (family.equations index).2.1
    (fun grade => ⟨family.graded index grade,family.inserted index grade⟩)

/-- The accepted seven-packet energy is paid directly by AN's d_q+Z_q.
No new source allocation or additional physical derivative is used. -/
theorem nativeSevenCurve_energy
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (index grade : ℕ) :
    (∫⁻ radius in Icc (originalExhaustionRadius length index) 1,
      ENNReal.ofReal (‖(nativeSevenCurves family index).curve grade radius‖^2)) ≤
      ENNReal.ofReal (((11+4*length)*family.nativeNorm index grade)^2) := by
  dsimp only [nativeSevenCurves]
  let low := originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small
  let data := actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field low
    (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index)
    ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) grade source flat
  let datum := originalWeightedDatum parameters (originalExhaustionRadius length index) length
    (originalExhaustionRadius_positive length lengthPositive index)
    ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive data
  have actual := actualObservedOutput_insertedEnergy parameters length compact (originalExhaustionRadius length index)
    (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index)
    lengthPositive widthHalf widthLength state
    (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    low source flat (family.limit index) (family.equations index).1 (family.equations index).2.1
    (fun grade => ⟨family.graded index grade,family.inserted index grade⟩)
    grade ((nativeSevenCurves family index).curve grade) (family.graded index grade) (family.inserted index grade)
    1 (by norm_num) (fun radius => by simp only [one_mul]; exact le_refl _)
  have zero : zeroBoundaryDatum parameters (originalExhaustionRadius length index) data = data := rfl
  have exactNorm : family.nativeNorm index grade = ‖datum‖+‖family.graded index grade‖ := by
    dsimp only [NativeCartesianFamily.nativeNorm,exhaustionDatumNorm,originalWeightedDatumNorm,
      cartesianExhaustionDatum,actualExhaustionContextDatum,cartesianExhaustionContext,fixedExhaustionContext]
    change ‖originalWeightedDatum parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive
      (zeroBoundaryDatum parameters (originalExhaustionRadius length index) data)‖ + ‖family.graded index grade‖ = _
    exact congrArg (fun value : OriginalStrongCarrier parameters (originalExhaustionRadius length index) 0 0 =>
      ‖originalWeightedDatum parameters (originalExhaustionRadius length index) length
        (originalExhaustionRadius_positive length lengthPositive index)
        ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive value‖ +
        ‖family.graded index grade‖) zero
  change _ ≤ ENNReal.ofReal ((1*((11+4*length)*‖family.graded index grade‖+3*‖datum‖))^2) at actual
  apply actual.trans
  rw [exactNorm]
  apply ENNReal.ofReal_le_ofReal
  apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
  nlinarith [norm_nonneg datum]

end Grad.OriginalCartesianTameEstimate
