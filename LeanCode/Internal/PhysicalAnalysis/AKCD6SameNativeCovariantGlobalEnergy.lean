import AKCD5SameNativeSevenEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
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

variable {parameters : PhaseParameters} {length compact : ℝ} {lengthPositive : 0 < length}
    {widthHalf : parameters.gamma ≤ 1 / 2} {widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)}
    {state : RetainedInverseState parameters length compact}
    {small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact}
    {source : SmoothQuotient parameters} {flat : IsFlat source}

open Grad.ActualPhysicalField Grad.ActualCartesianFlux Grad.ActualPuncturedReconstruction
open Grad.PuncturedRetainedEnergy Grad.AnnularPhysicalReconstruction

abbrev nativeCovariantRows
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (index : ℕ) :=
  cartesianCovariantRow (originalExhaustionRadius length index)
    (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat family.limit index)

abbrev nativeCovariantCurves
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (index : ℕ) :=
  (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat family.limit
    (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
    (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) index).cartesianCovariant

theorem nativeCovariantRows_compatible
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (first second : ℕ) (ordered : first ≤ second) :
    originalBulkRestriction 3 (originalExhaustionRadius length second) (originalExhaustionRadius length first)
      (originalExhaustionRadius_antitone length lengthPositive ordered) (nativeCovariantRows family second) =
      nativeCovariantRows family first :=
  cartesianCovariantRows_compatible (originalExhaustionRadius length)
    (originalExhaustionRadius_antitone length lengthPositive)
    (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat family.limit)
    (fun first second ordered => (cartesianSourcePolarAndXi_compatible parameters length compact lengthPositive widthHalf widthLength state small
      source flat family.limit family.compatible first second ordered).1) first second ordered

def nativeCovariantEndpointConstant (parameters : PhaseParameters) (length compact : ℝ) (grade : ℕ) : ℝ :=
  2 * (actualCovariantCurve_oneHigh parameters length compact grade).choose * (11+4*length)

theorem nativeCovariantEndpointConstant_nonnegative (parameters : PhaseParameters) (length compact : ℝ)
    (lengthPositive : 0<length) (grade : ℕ) : 0≤nativeCovariantEndpointConstant parameters length compact grade := by
  have positive := (actualCovariantCurve_oneHigh parameters length compact grade).choose_spec.1
  unfold nativeCovariantEndpointConstant
  positivity

/-- Global SAME original-width covariant energy, with the two independent
native payments retained. Constants are fixed before the state and source. -/
theorem nativeCovariant_globalEnergy
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (small12 : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 12 ≤ 1)
    (grade : ℕ) (high low : ℝ) (highNonnegative : 0≤high) (lowNonnegative : 0≤low)
    (highBound : ∀ index, family.nativeNorm index grade ≤ high)
    (lowBound : ∀ index, family.nativeNorm index 0 ≤ low) :
    (∫⁻ radius in Ioc (0:ℝ) 1, ENNReal.ofReal
      (‖gluedWeightedFamilyCurve parameters (originalExhaustionRadius length)
        (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_tendsto length)
        (nativeCovariantRows family) (nativeCovariantCurves family) grade radius‖^2)) ≤
      ENNReal.ofReal ((nativeCovariantEndpointConstant parameters length compact grade *
        (high+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+12)*low))^2) := by
  let C := (actualCovariantCurve_oneHigh parameters length compact grade).choose
  have Cnonnegative : 0≤C := (actualCovariantCurve_oneHigh parameters length compact grade).choose_spec.1
  let B := physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+12)
  have Bnonnegative : 0≤B := physicalBudget_nonnegative _ _ _ _ _
  have factorNonnegative : 0≤11+4*length := by positivity
  have collar (index : ℕ) :
      (∫⁻ radius in Icc (originalExhaustionRadius length index) 1, ENNReal.ofReal
        (‖(nativeCovariantCurves family index).curve grade radius‖^2)) ≤
      ENNReal.ofReal ((nativeCovariantEndpointConstant parameters length compact grade * (high+B*low))^2) := by
    have inputEnergy (rank : ℕ) (payment : ℝ) (paymentNonnegative : 0≤payment)
        (paymentBound : family.nativeNorm index rank ≤ payment) :
        (∫⁻ radius in Icc (originalExhaustionRadius length index) 1, ENNReal.ofReal
          (‖(nativeSevenCurves family index).curve rank radius‖^2)) ≤ ENNReal.ofReal (((11+4*length)*payment)^2) := by
      apply (nativeSevenCurve_energy family index rank).trans
      apply ENNReal.ofReal_le_ofReal
      apply (sq_le_sq₀ (mul_nonneg factorNonnegative (by
          unfold NativeCartesianFamily.nativeNorm exhaustionDatumNorm originalWeightedDatumNorm
          exact add_nonneg (norm_nonneg _) (norm_nonneg _)))
        (mul_nonneg factorNonnegative paymentNonnegative)).mpr
      exact mul_le_mul_of_nonneg_left paymentBound factorNonnegative
    have pointBound : ∀ᵐ radius ∂volume.restrict (Icc (originalExhaustionRadius length index) 1),
        ‖(nativeCovariantCurves family index).curve grade radius‖ ≤
          C*(‖(nativeSevenCurves family index).curve grade radius‖+B*‖(nativeSevenCurves family index).curve 0 radius‖) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
      exact (actualCovariantCurve_oneHigh parameters length compact grade).choose_spec.2 state.val small12
        (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index)
        ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) _ (nativeSevenCurves family index) radius inside
    have actual := twoInput_squareEnergy (volume.restrict (Icc (originalExhaustionRadius length index) 1))
      ((nativeCovariantCurves family index).curve grade) ((nativeSevenCurves family index).curve grade)
      ((nativeSevenCurves family index).curve 0)
      (((nativeSevenCurves family index).smooth grade).continuousOn.aestronglyMeasurable measurableSet_Icc)
      (((nativeSevenCurves family index).smooth 0).continuousOn.aestronglyMeasurable measurableSet_Icc)
      C B ((11+4*length)*high) ((11+4*length)*low) Cnonnegative Bnonnegative
      (mul_nonneg factorNonnegative highNonnegative) (mul_nonneg factorNonnegative lowNonnegative)
      pointBound (inputEnergy grade high highNonnegative (highBound index)) (inputEnergy 0 low lowNonnegative (lowBound index))
    exact actual.trans_eq (by congr 2; unfold nativeCovariantEndpointConstant; dsimp [C]; ring)
  have gluedCollar (index : ℕ) :
      (∫⁻ radius in Icc (originalExhaustionRadius length index) 1, ENNReal.ofReal
        (‖gluedWeightedFamilyCurve parameters (originalExhaustionRadius length)
          (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_tendsto length)
          (nativeCovariantRows family) (nativeCovariantCurves family) grade radius‖^2)) ≤
        ENNReal.ofReal ((nativeCovariantEndpointConstant parameters length compact grade*(high+B*low))^2) := by
    convert collar index using 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
    rw [gluedWeightedFamilyCurve_same parameters (originalExhaustionRadius length)
      (originalExhaustionRadius_positive length lengthPositive)
      (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
      (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive)
      (nativeCovariantRows family) (nativeCovariantCurves family) (nativeCovariantRows_compatible family) grade index radius inside]
  have global := cofinalEnergy_bound 1 (originalExhaustionRadius length)
    (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_antitone length lengthPositive)
    (originalExhaustionRadius_tendsto length)
    (fun radius => ENNReal.ofReal (‖gluedWeightedFamilyCurve parameters (originalExhaustionRadius length)
      (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_tendsto length)
      (nativeCovariantRows family) (nativeCovariantCurves family) grade radius‖^2))
    0 (ENNReal.ofReal ((nativeCovariantEndpointConstant parameters length compact grade*(high+B*low))^2))
    (fun index => by simpa only [add_zero] using gluedCollar index)
  simpa only [add_zero] using global

end Grad.OriginalCartesianTameEstimate
