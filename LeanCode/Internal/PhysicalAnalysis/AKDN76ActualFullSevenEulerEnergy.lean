import AKDN75ActualNativeSevenUnknownEnergy
import AKDN74ActualKnownSevenEulerEnergy

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
open scoped ENNReal BigOperators ContDiff
attribute [local irreducible] originalWeightedDatum

open Grad.AnnularSmoothCore Grad.AnnularGeneralSourceRegularity

/-- Complete SAME stored seven-slot Euler energy, with the original
source term included exactly once and only one high state factor. -/
theorem nativeSevenCurves_originalSourceEnergy
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0<length)
    (widthHalf : parameters.gamma≤1/2) (widthLength : parameters.gamma≤Real.sqrt 5/(6*length))
    (index total extra power rank : ℕ) (paid : extra+power+rank≤total)
    (cost : ℕ → ℝ) (cost0 : ∀ order,0≤cost order) :
    ∃ constant : ℝ, 0≤constant ∧
    ∀ state : RetainedInverseState parameters length compact,
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 15≤1 →
    ∀ (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤
        originalExhaustionPrimitiveRadius parameters length compact)
      (source : SmoothQuotient parameters) (flat : IsFlat source)
      (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat),
    (∀ order, family.nativeNorm index order≤cost order*(‖quotientEta parameters (order+8) source‖+
      physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (order+14)*‖quotientEta parameters 8 source‖)) →
    (∫⁻ radius in Icc (originalExhaustionRadius length index) 1, ENNReal.ofReal
      (‖(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)) •
        vectorEulerWithinIteratedDerivative (Icc (originalExhaustionRadius length index) 1) rank
          ((nativeSevenCurves family index).curve (power+1)) radius‖^2)) ≤
      ENNReal.ofReal ((constant*(‖quotientEta parameters (total+10) source‖+
        (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (total+16))*‖quotientEta parameters 9 source‖))^2) := by
  let lower := originalExhaustionRadius length index
  let positive := originalExhaustionRadius_positive length lengthPositive index
  let bounded : lower<1 := (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)
  let unknownResult := nativeBalancedInput_originalSourceEnergy parameters length compact lengthPositive widthHalf widthLength
    index total extra power rank paid cost cost0
  let unknownConstant := unknownResult.choose
  have unknown0 : 0≤unknownConstant := unknownResult.choose_spec.1
  have unknownBound := unknownResult.choose_spec.2
  obtain ⟨knownConstant,known0,knownBound⟩ := actualKnownSeven_jointEulerEnergy parameters length compact lower positive bounded
    (total+1) extra (power+1) rank (by omega)
  refine ⟨2*(unknownConstant+knownConstant),mul_nonneg (by norm_num) (add_nonneg unknown0 known0),?_⟩
  intro state low small source flat family native
  let weight := 1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)
  let payment := ‖quotientEta parameters (total+10) source‖+
    (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (total+16))*‖quotientEta parameters 9 source‖
  let unknown := fun point => balancedSevenInput parameters point (nativeBalancedCurve family index (power+1) point)
  let known := actualCartesianKnownSevenCurve parameters length lower positive bounded source (power+1)
  have budget0 (order : ℕ) : 0≤1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon order :=
    add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)
  have payment0 : 0≤payment := add_nonneg (norm_nonneg _) (mul_nonneg (budget0 _) (norm_nonneg _))
  have unit := (physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon (by norm_num : 10≤15)).trans low
  have high := unknownBound state low small source flat family native
  have sourceEnergy := knownBound state unit source
  have sourcePayment : ‖quotientEta parameters (4+(total+1)) source‖+
      (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+(total+1)))*‖quotientEta parameters 4 source‖ ≤ payment :=
    add_le_add (originalSourceGrade_mono parameters source (by omega))
      (mul_le_mul (add_le_add (le_refl _) (physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon (by omega)))
        (originalSourceGrade_mono parameters source (by omega)) (norm_nonneg _) (budget0 _))
  have sourcePaid : (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank known radius‖^2)) ≤
      ENNReal.ofReal ((knownConstant*payment)^2) := by
    apply sourceEnergy.trans
    apply ENNReal.ofReal_le_ofReal
    apply (sq_le_sq₀ (mul_nonneg known0 (add_nonneg (norm_nonneg _) (mul_nonneg (budget0 _) (norm_nonneg _))))
      (mul_nonneg known0 payment0)).mpr
    exact mul_le_mul_of_nonneg_left sourcePayment known0
  have realSmooth := ((ContinuousLinearMap.restrictScalarsIsometry ℂ PhysicalHilbertPair (CellL2 7) ℝ ℝ).toContinuousLinearMap.contDiff).comp_contDiffOn
    ((balancedSevenInput_smooth parameters).contDiffOn (s:=Icc lower 1))
  have unknownSmooth : ContDiffOn ℝ ∞ unknown (Icc lower 1) := realSmooth.clm_apply (nativeBalancedCurve_smooth family index (power+1))
  have knownSmooth : ContDiffOn ℝ ∞ known (Icc lower 1) := actualCartesianKnownSevenCurve_smooth parameters length lower positive bounded source (power+1)
  have added := eulerCurve_squareEnergy_add lower bounded unknown known rank
    (contDiffOn_infty.mp unknownSmooth rank) (contDiffOn_infty.mp knownSmooth rank) weight
    (unknownConstant*payment) (knownConstant*payment) (mul_nonneg unknown0 payment0) (mul_nonneg known0 payment0) high sourcePaid
  have same := eulerCurve_squareEnergy_congr lower ((nativeSevenCurves family index).curve (power+1))
    (fun point => unknown point+known point) (fun radius inside => nativeSevenCurves_fullFormula family index power radius inside) rank weight
  exact same.le.trans (added.trans_eq (by congr 1; ring))

end Grad.OriginalCartesianTameEstimate
