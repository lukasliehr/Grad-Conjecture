import AKDN71ClosedCollarSevenFidelity

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
open scoped ENNReal BigOperators ContDiff
attribute [local irreducible] originalWeightedDatum

variable {parameters : PhaseParameters} {length compact : ℝ} {lengthPositive : 0 < length}
    {widthHalf : parameters.gamma ≤ 1 / 2} {widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)}
    {state : RetainedInverseState parameters length compact}
    {small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact}
    {source : SmoothQuotient parameters} {flat : IsFlat source}

open Grad.AnnularGeneralSourceRegularity

/-- Actual prescribed source curves for the SAME native family. -/
def nativeSourceCurves
    (_family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (index : ℕ) :
    ActualSourceRadialCurves parameters (originalExhaustionRadius length index)
      (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
      (originalStrongWeightEquivalence parameters (originalExhaustionRadius length index) length
        (originalExhaustionRadius_positive length lengthPositive index)
        ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive 0 0
        (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0)) :=
  actualCartesianSourceCurves_of_sourceBlocks parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
    (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index)
    ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) lengthPositive source flat
    (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0) rfl

theorem nativeSourceCurves_seven
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (index grade : ℕ) (radius : ℝ) :
    (nativeSourceCurves family index).seven grade radius =
      actualCartesianKnownSevenCurve parameters length (originalExhaustionRadius length index)
        (originalExhaustionRadius_positive length lengthPositive index)
        ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) source grade radius := rfl

/-- The exact native seven-slot identity on the whole original collar. -/
theorem nativeSevenCurves_fullFormula
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (index grade : ℕ) (radius : ℝ) (inside : radius∈Icc (originalExhaustionRadius length index) 1) :
    (nativeSevenCurves family index).curve (grade+1) radius =
      balancedSevenInput parameters radius (nativeBalancedCurve family index (grade+1) radius)+
        actualCartesianKnownSevenCurve parameters length (originalExhaustionRadius length index)
          (originalExhaustionRadius_positive length lengthPositive index)
          ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) source (grade+1) radius := by
  let lower := originalExhaustionRadius length index
  let positive := originalExhaustionRadius_positive length lengthPositive index
  let bounded : lower<1 := (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)
  let data := originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0
    (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0)
  let field := originalWeightedRetainedObservation parameters lower length positive bounded.le lengthPositive (family.limit index)
  have allGrades (power : ℕ) : ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive power field weighted :=
    ⟨family.graded index power,family.inserted index power⟩
  have actual := sameSevenCurve_fullFormula parameters lower length positive bounded lengthPositive data field
    (nativeSourceCurves family index) allGrades (nativeSevenCurves_full family index) grade radius inside
  exact (nativeSevenCurves_full_curve family index (grade+1) radius).symm.trans
    (actual.trans (congrArg₂ (fun first second => balancedSevenInput parameters radius first+second)
      (nativeBalancedCurve_formula family index (grade+1) radius).symm
      (nativeSourceCurves_seven family index (grade+1) radius)))

/-- Smoothness of the SAME balanced family from its fixed stored-seven projection. -/
theorem nativeBalancedCurve_smooth
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (index grade : ℕ) :
    ContDiffOn ℝ ∞ (nativeBalancedCurve family index grade) (Icc (originalExhaustionRadius length index) 1) := by
  let lower := originalExhaustionRadius length index
  let positive := originalExhaustionRadius_positive length lengthPositive index
  let bounded : lower<1 := (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)
  let data := originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0
    (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0)
  let field := originalWeightedRetainedObservation parameters lower length positive bounded.le lengthPositive (family.limit index)
  have allGrades (power : ℕ) : ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive power field weighted :=
    ⟨family.graded index power,family.inserted index power⟩
  have zero (power : ℕ) (radius : ℝ) : nativeBalancedSevenProjection parameters ((nativeSourceCurves family index).seven power radius)=0 := by
    rw [nativeSourceCurves_seven]
    exact nativeBalancedSevenProjection_known parameters length lower positive bounded source power radius
  have actual := sameSevenCurve_balancedSmooth parameters lower length positive bounded lengthPositive data field
    (nativeSourceCurves family index) allGrades (nativeSevenCurves_full family index) zero grade
  exact actual.congr (fun radius _ => nativeBalancedCurve_formula family index grade radius)

end Grad.OriginalCartesianTameEstimate
