import AKDN62ActualNativePureBalancedEnergy
import AKDN63SameObservedInverseFidelity

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

open Grad.AnnularSmoothCore

/-- SAME compatible native family, full joint Euler energy, with its two
independent native norm payments still visible. -/
theorem nativeBalancedCurve_jointEulerEnergy
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (index total : ℕ) (totalPositive : 0 < total) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ state : RetainedInverseState parameters length compact,
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
        originalExhaustionPrimitiveRadius parameters length compact)
      (source : SmoothQuotient parameters) (flat : IsFlat source)
      (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat),
    ∀ extra grade order : ℕ, extra+grade+order ≤ total →
    (∫⁻ radius in Icc (originalExhaustionRadius length index) 1, ENNReal.ofReal
      (‖(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)) •
        vectorEulerWithinIteratedDerivative (Icc (originalExhaustionRadius length index) 1) order
          (nativeBalancedCurve family index grade) radius‖^2)) ≤
      ENNReal.ofReal ((constant*(family.nativeNorm index (total+1)+
        (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+total))*family.nativeNorm index 1+
        (‖quotientEta parameters (4+total) source‖+
          (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+total))*
            ‖quotientEta parameters 4 source‖)))^2) := by
  let lower := originalExhaustionRadius length index
  let positive := originalExhaustionRadius_positive length lengthPositive index
  let lowerHalf := originalExhaustionRadius_half length lengthPositive index
  let bounded : lower < 1 := lowerHalf.trans_lt (by norm_num)
  let result := sameNativeBalanced_jointEulerIntegral parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength total totalPositive
  let constant := result.choose
  have constant0 : 0 ≤ constant := result.choose_spec.1
  have bound := result.choose_spec.2
  let projection := ‖nativeBalancedSevenProjection parameters‖*(11+4*length)
  have projection0 : 0 ≤ projection := mul_nonneg (norm_nonneg _) (by linarith)
  refine ⟨constant*(projection+1),mul_nonneg constant0 (by positivity),?_⟩
  intro state unit small source flat family extra grade order allocated
  let low := originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small
  let recovery := observedWeightedRetained_as_shared parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state low (family.limit index) (family.equations index).1
  let original := recovery.choose
  have sameOriginal := recovery.choose_spec.1
  have same := recovery.choose_spec.2
  have sameSources : original.val.ofLp.1 =
      (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
        lower positive bounded 0 source flat).val.ofLp.1 :=
    sameOriginal.trans (family.equations index).2.1
  have allGrades (power : ℕ) : ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive power
        (originalWeightedRetainedObservation parameters lower length positive bounded.le lengthPositive (family.limit index)) weighted :=
    ⟨family.graded index power,family.inserted index power⟩
  have native0 (power : ℕ) : 0 ≤ family.nativeNorm index power := by
    unfold NativeCartesianFamily.nativeNorm exhaustionDatumNorm originalWeightedDatumNorm
    exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  have highEnergy := nativeBalancedCurve_pureEnergy family index total
  have baseEnergy := nativeBalancedCurve_pureEnergy family index 0
  have highSame : ‖nativeBalancedSevenProjection parameters‖*((11+4*length)*family.nativeNorm index (total+1)) =
      projection*family.nativeNorm index (total+1) := (mul_assoc _ _ _).symm
  have baseSame : ‖nativeBalancedSevenProjection parameters‖*((11+4*length)*family.nativeNorm index (0+1)) =
      projection*family.nativeNorm index 1 := (mul_assoc _ _ _).symm
  rw [highSame] at highEnergy
  rw [baseSame] at baseEnergy
  let response := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state low
    (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 original)
  have sameResponse : originalWeightedRetainedObservation parameters lower length positive bounded.le lengthPositive (family.limit index)=response := same
  have responseGrades (power : ℕ) : ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive power response weighted := by
    rw [←sameResponse]
    exact allGrades power
  have curveSame (power : ℕ) (radius : ℝ) : nativeBalancedCurve family index power radius =
      balancedOriginalPairCurve parameters lower length positive bounded lengthPositive response power radius :=
    (nativeBalancedCurve_formula family index power radius).trans
      (congrArg (fun field => balancedOriginalPairCurve parameters lower length positive bounded lengthPositive field power radius) sameResponse)
  have integralSame (power : ℕ) :
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal
        (‖balancedOriginalPairCurve parameters lower length positive bounded lengthPositive response power radius‖^2)) =
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖nativeBalancedCurve family index power radius‖^2)) := by
    apply lintegral_congr
    intro radius
    exact congrArg (fun value : PhysicalHilbertPair => ENNReal.ofReal (‖value‖^2)) (curveSame power radius).symm
  have energy := bound state unit low source flat original sameSources responseGrades
    (projection*family.nativeNorm index (total+1)) (projection*family.nativeNorm index 1)
    (mul_nonneg projection0 (native0 _)) (mul_nonneg projection0 (native0 _))
    ((integralSame total).le.trans highEnergy) ((integralSame 0).le.trans baseEnergy) extra grade order allocated
  have eulerSame := eulerCurve_squareEnergy_congr lower (nativeBalancedCurve family index grade)
    (balancedOriginalPairCurve parameters lower length positive bounded lengthPositive response grade)
    (fun radius _ => curveSame grade radius) order
    (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra))
  apply eulerSame.le.trans
  apply energy.trans
  apply ENNReal.ofReal_le_ofReal
  let budget := 1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+total)
  have budget0 : 0 ≤ budget := add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)
  have source0 : 0 ≤ ‖quotientEta parameters (4+total) source‖+budget*‖quotientEta parameters 4 source‖ :=
    add_nonneg (norm_nonneg _) (mul_nonneg budget0 (norm_nonneg _))
  have pure0 : 0 ≤ family.nativeNorm index (total+1)+budget*family.nativeNorm index 1 :=
    add_nonneg (native0 _) (mul_nonneg budget0 (native0 _))
  apply (sq_le_sq₀ (mul_nonneg constant0 (add_nonneg
    (add_nonneg (mul_nonneg projection0 (native0 _))
      (mul_nonneg budget0 (mul_nonneg projection0 (native0 _)))) source0))
    (mul_nonneg (mul_nonneg constant0 (add_nonneg projection0 zero_le_one)) (add_nonneg pure0 source0))).mpr
  nlinarith only [mul_nonneg constant0 (add_nonneg pure0 (mul_nonneg projection0 source0))]

end Grad.OriginalCartesianTameEstimate
