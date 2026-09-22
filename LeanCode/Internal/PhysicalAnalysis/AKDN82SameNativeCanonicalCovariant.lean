import AKDN81CanonicalWeightedCurveFidelity
import AKCA23ActualScalarCartesianPolynomial

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ActualCartesianWeakEquations
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

open Grad.AnnularWeightedSmoothness Grad.BoundaryKernelAction Grad.AnnularKernelL2

open Grad.NonlinearRange Grad.OriginalKernelGraphRestriction Grad.OriginalCoreRealization
open Grad.ActualCartesianFlux Grad.ActualPuncturedReconstruction

/-- The canonical weighted core curve is exactly the already estimated
SAME native covariant on the full closed collar. -/
theorem nativeCovariant_canonicalCurve
    {parameters : PhaseParameters} {length compact : ℝ} {lengthPositive : 0<length}
    {widthHalf : parameters.gamma≤1/2} {widthLength : parameters.gamma≤Real.sqrt 5/(6*length)}
    {state : RetainedInverseState parameters length compact}
    {small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤
      originalExhaustionPrimitiveRadius parameters length compact}
    {source : SmoothQuotient parameters} {flat : IsFlat source}
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (core : ACore parameters 3)
    (same : ∀ (point : ClosedDisk), 0<‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters core).value (point,(axial : CellCircle))=
        actualCartesianCovariantFamilyField parameters length compact lengthPositive widthHalf widthLength state small source flat
          family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
          (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) (point.val,axial))
    (index power : ℕ) (radius : ℝ) (inside : radius∈Icc (originalExhaustionRadius length index) 1) :
    cartesianWeightedRadialCurve parameters (originalExhaustionRadius length index)
      (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) core power 0 radius=
        (nativeCovariantCurves family index).curve power radius := by
  let lower := originalExhaustionRadius length index
  let positive := originalExhaustionRadius_positive length lengthPositive index
  let bounded : lower<1 := (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)
  apply canonicalWeightedCurve_sameNative parameters lower positive bounded (nativeCovariantCurves family index) core ?_ power radius inside
  intro current member angles
  have radiusPositive : 0<current := positive.trans_le member.1
  have pointNorm : ‖(Grad.SourceCollarDivision.polarClosedPoint current angles.1 radiusPositive.le member.2).val‖=current :=
    (polarPlane_norm current angles.1).trans (abs_of_pos radiusPositive)
  change coreValue core (Grad.SourceCollarDivision.polarClosedPoint current angles.1 (positive.le.trans member.1) member.2) angles.2=_
  rw [coreValue_originalPhysical,same _ (by rw [pointNorm]; exact radiusPositive)]
  have actual := actualNativeCovariantField_polar parameters length compact lengthPositive widthHalf widthLength state small source flat
    family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
    (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) family.compatible index current member angles.1 angles.2
  exact actual.trans (SmoothLowPhysicalRow.fullField_cartesianCovariant bounded _ current member angles).symm

end Grad.OriginalCartesianTameEstimate
