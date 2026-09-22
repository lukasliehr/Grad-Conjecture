import AKDN61SameSevenBalancedEnergy
import AKCD5SameNativeSevenEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
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

open Grad.AnnularGeneralSourceRegularity

/-- The SAME compatible family's balanced native curve. -/
def nativeBalancedCurve
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (index grade : ℕ) : ℝ → Grad.AnnularSmoothCore.PhysicalHilbertPair :=
  balancedOriginalPairCurve parameters (originalExhaustionRadius length index) length
    (originalExhaustionRadius_positive length lengthPositive index)
    ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) lengthPositive
    (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (family.limit index)) grade

/-- Literal packet equality isolates the completed observation projection
before applying any Hilbert norm or energy theorem. -/
theorem originalPacket_observation_full (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (original : OriginalStrongCarrier parameters lower 0 0)
    (point : OriginalFiveBlockAmbient parameters lower length positive) :
    originalSevenPacket parameters lower length positive bounded lengthPositive original point.ofLp.1 =
      fullStrongSevenInput parameters length lower lengthPositive positive bounded
        (originalStrongWeightEquivalence parameters lower length positive bounded lengthPositive 0 0 original)
        (originalWeightedRetainedObservation parameters lower length positive bounded lengthPositive point) := rfl

/-- The stored seven curve with an explicit propositional row transport.
Its actual curve is unchanged. -/
def nativeSevenCurves_full
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (index : ℕ) :
    SmoothLowPhysicalRow parameters (originalExhaustionRadius length index)
      (originalExhaustionRadius_positive length lengthPositive index)
      (fullStrongSevenInput parameters length (originalExhaustionRadius length index) lengthPositive
        (originalExhaustionRadius_positive length lengthPositive index)
        ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num))
        (originalStrongWeightEquivalence parameters (originalExhaustionRadius length index) length
          (originalExhaustionRadius_positive length lengthPositive index)
          ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive 0 0
          (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0))
        (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length
          (originalExhaustionRadius_positive length lengthPositive index)
          ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (family.limit index))) where
  curve := (nativeSevenCurves family index).curve
  smooth := (nativeSevenCurves family index).smooth
  same grade := by
    have actual := (nativeSevenCurves family index).same grade
    filter_upwards [actual] with radius same
    intro mode
    apply (same mode).trans
    exact congrArg (fun row => (annularFrequency mode.1 mode.2 : ℂ)^grade •
      (Real.exp (Grad.PhaseAlgebra.radialPhase parameters radius mode.2) : ℂ) •
        Grad.AnnularCurrentLow.lowRhoPhysicalCoefficient parameters (originalExhaustionRadius length index)
          (originalExhaustionRadius_positive length lengthPositive index) row radius mode)
      (originalPacket_observation_full parameters (originalExhaustionRadius length index) length
        (originalExhaustionRadius_positive length lengthPositive index)
        ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive
        (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0)
        (family.limit index))

theorem nativeSevenCurves_full_curve
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (index grade : ℕ) (radius : ℝ) :
    (nativeSevenCurves_full family index).curve grade radius = (nativeSevenCurves family index).curve grade radius := rfl

theorem nativeSevenCurves_full_energy
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (index grade : ℕ) :
    (∫⁻ radius in Icc (originalExhaustionRadius length index) 1,
      ENNReal.ofReal (‖(nativeSevenCurves_full family index).curve grade radius‖^2)) ≤
      ENNReal.ofReal (((11+4*length)*family.nativeNorm index grade)^2) := by
  have same : (∫⁻ radius in Icc (originalExhaustionRadius length index) 1,
      ENNReal.ofReal (‖(nativeSevenCurves_full family index).curve grade radius‖^2)) =
      (∫⁻ radius in Icc (originalExhaustionRadius length index) 1,
        ENNReal.ofReal (‖(nativeSevenCurves family index).curve grade radius‖^2)) := by
    apply lintegral_congr
    intro radius
    exact congrArg (fun value : CellL2 7 => ENNReal.ofReal (‖value‖^2)) (nativeSevenCurves_full_curve family index grade radius)
  exact same.le.trans (nativeSevenCurve_energy family index grade)

theorem nativeBalancedCurve_formula
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (index grade : ℕ) (radius : ℝ) :
    nativeBalancedCurve family index grade radius =
      balancedOriginalPairCurve parameters (originalExhaustionRadius length index) length
        (originalExhaustionRadius_positive length lengthPositive index)
        ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) lengthPositive
        (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length
          (originalExhaustionRadius_positive length lengthPositive index)
          ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (family.limit index)) grade radius := rfl

/-- Direct CD5 payment of the SAME balanced pair at one fixed collar.
The projection is fixed before state/source; only one extra native grade is used. -/
theorem nativeBalancedCurve_pureEnergy
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (index grade : ℕ) :
    (∫⁻ radius in Icc (originalExhaustionRadius length index) 1,
      ENNReal.ofReal (‖nativeBalancedCurve family index grade radius‖^2)) ≤
      ENNReal.ofReal ((‖nativeBalancedSevenProjection parameters‖*((11+4*length)*family.nativeNorm index (grade+1)))^2) := by
  let lower := originalExhaustionRadius length index
  let positive := originalExhaustionRadius_positive length lengthPositive index
  let bounded := (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num : (1:ℝ)/2<1)
  let low := originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small
  let original := cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0
  let data := originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 original
  let field := originalWeightedRetainedObservation parameters lower length positive bounded.le lengthPositive (family.limit index)
  have sameSources : original.val.ofLp.1 =
      (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field low
        lower positive bounded 0 source flat).val.ofLp.1 := rfl
  let curves := actualCartesianSourceCurves_of_sourceBlocks parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    low lower positive bounded lengthPositive source flat original sameSources
  have allGrades (power : ℕ) : ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive power field weighted :=
    ⟨family.graded index power,family.inserted index power⟩
  have knownZero (power : ℕ) (radius : ℝ) : nativeBalancedSevenProjection parameters (curves.seven power radius)=0 := by
    change nativeBalancedSevenProjection parameters (actualCartesianKnownSevenCurve parameters length lower positive bounded source power radius)=0
    exact nativeBalancedSevenProjection_known parameters length lower positive bounded source power radius
  let seven := nativeSevenCurves_full family index
  have energy := nativeSevenCurves_full_energy family index (grade+1)
  have result := sameSevenCurve_balancedEnergy parameters lower length positive bounded lengthPositive data field curves allGrades
    seven knownZero grade ((11+4*length)*family.nativeNorm index (grade+1)) energy
  have same : (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖nativeBalancedCurve family index grade radius‖^2)) =
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal
        (‖balancedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade radius‖^2)) := by
    apply lintegral_congr
    intro radius
    exact congrArg (fun value : Grad.AnnularSmoothCore.PhysicalHilbertPair => ENNReal.ofReal (‖value‖^2))
      (nativeBalancedCurve_formula family index grade radius)
  exact same.le.trans result

end Grad.OriginalCartesianTameEstimate
