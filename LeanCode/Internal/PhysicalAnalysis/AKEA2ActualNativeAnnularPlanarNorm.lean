import AKDN84ActualCanonicalCollarEulerConsumer
import AKEA1CanonicalAnnularPlanarEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.OriginalCollarNorm
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

open Grad.NonlinearRange Grad.ActualCartesianFlux Grad.ActualPuncturedReconstruction

open Grad.OriginalCartesianTameEstimate Grad.CartesianStartup Grad.ActualOriginalSourceMoments

/-- Actual native source energy reaches the SAME original annular planar norm. -/
theorem nativeCovariant_annularPlanarNorm
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0<length)
    (widthHalf : parameters.gamma≤1/2) (widthLength : parameters.gamma≤Real.sqrt 5/(6*length))
    (index total : ℕ) (collarSmall : originalExhaustionRadius length index≤(1/8:ℝ))
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
    ∀ core : ACore parameters 3,
    (∀ (point : ClosedDisk), 0<‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters core).value (point,(axial : CellCircle))=
        actualCartesianCovariantFamilyField parameters length compact lengthPositive widthHalf widthLength state small source flat
          family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
          (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) (point.val,axial)) →
    ∀ image : ACore parameters 3,
    (originalSourceMoments parameters image).field=
      startupCutoffL2 actualNativeAnnularCutoff actualNativeAnnularCutoff_smooth
        actualNativeAnnularCutoff_compact (originalSourceMoments parameters core).field →
    originalPlanarNorm parameters total image≤constant*(‖quotientEta parameters (total+10) source‖+
      (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (total+16))*
        ‖quotientEta parameters 9 source‖) := by
  let euler := nativeCanonicalCovariant_uniformEulerEnergy parameters length compact lengthPositive
    widthHalf widthLength index total cost cost0
  let norm := canonicalAnnular_planarEnergy (originalExhaustionRadius length index)
    (originalExhaustionRadius_positive length lengthPositive index)
    ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) collarSmall total
  refine ⟨norm.choose*euler.choose,mul_nonneg norm.choose_spec.1 euler.choose_spec.1,?_⟩
  intro state low small source flat family native core sameCore image sameImage
  let payment := ‖quotientEta parameters (total+10) source‖+
    (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (total+16))*
      ‖quotientEta parameters 9 source‖
  have payment0 : 0≤payment := add_nonneg (norm_nonneg _)
    (mul_nonneg (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)) (norm_nonneg _))
  have paid := norm.choose_spec.2 parameters core image sameImage (euler.choose*payment)
    (mul_nonneg euler.choose_spec.1 payment0)
    (euler.choose_spec.2 state low small source flat family native core sameCore)
  exact paid.trans_eq (mul_assoc _ _ _).symm

end Grad.OriginalCollarNorm
