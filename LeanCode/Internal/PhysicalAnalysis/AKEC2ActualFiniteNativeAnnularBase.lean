import AKEC1ActualFiniteNativeAnnularNorm

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

open Grad.Constraints Grad.Q24Realization Grad.AxisSplit Grad.ChartAxisLift Grad.ConstrainedTransfer Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct

/-- Independent annular base norm of the same actual finite covariant. -/
theorem actualFiniteCovariant_annularBaseNorm
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0<length)
    (widthHalf : parameters.gamma≤1/2) (widthLength : parameters.gamma≤Real.sqrt 5/(6*length))
    (cost : ℕ → ℝ) (cost0 : ∀ order,0≤cost order) :
    ∃ constant : ℝ, 0≤constant ∧
    ∀ (reference : Seed.Parameters) (insideR : reference∈Seed.parameterDomain)
      (seed : Seed.Parameters) (insideS : seed∈Seed.parameterDomain) (base : RealJointCore parameters reference insideR)
      (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
      (compactNonnegative : 0≤compact) (alphaSmall : |seed 1|≤compact)
      (deltaSmall : |seed 2|≤compact) (parameterSmall : |seed 3|≤compact)
      (small : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
        (seed 0) base.1 8≤actualJetExhaustionRadius parameters length compact),
      physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base) (seed 0) base.1 24≤1 →
      ∀ source : OriginalFlatSource parameters length,
      let low := actualJetExhaustion_cubicSmall parameters length compact reference insideR seed insideS base small
      let state := actualJetExhaustionState parameters length compact reference insideR seed insideS base small
        compactNonnegative alphaSmall deltaSmall parameterSmall
      let exSmall := actualJetExhaustion_exSmall parameters length compact reference insideR seed insideS base small
      let residual := actualFiniteSourceResidual parameters length (seed 0) reference insideR seed insideS base low source
      let flat := actualFiniteSourceResidual_isFlat parameters length (seed 0) lengthPositive reference insideR seed insideS base low axis source
      ∀ family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state exSmall residual flat,
      (∀ order, family.nativeNorm 3 order≤cost order*(‖quotientEta parameters (order+8) residual‖+
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (order+14)*‖quotientEta parameters 8 residual‖)) →
      ∀ core : ACore parameters 3,
      (∀ (point : ClosedDisk),0<‖point.val‖ → ∀ axial : ℝ,
        (originalPhysicalClosedJet parameters core).value (point,(axial : CellCircle))=
          actualCartesianCovariantFamilyField parameters length compact lengthPositive widthHalf widthLength state exSmall residual flat
            family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
            (fun index rank => ⟨family.graded index rank,family.inserted index rank⟩) (point.val,axial)) →
      ∀ image : ACore parameters 3,
      (originalSourceMoments parameters image).field=
        startupCutoffL2 actualNativeAnnularCutoff actualNativeAnnularCutoff_smooth actualNativeAnnularCutoff_compact
          (originalSourceMoments parameters core).field →
      originalPlanarNorm parameters 0 image≤constant*‖quotientEta parameters 24 source.val.val‖ := by
  let result := actualFiniteCovariant_annularPlanarNorm parameters length compact lengthPositive widthHalf widthLength 0 cost cost0
  let constant := result.choose
  have constant0 : 0≤constant := result.choose_spec.1
  have bound := result.choose_spec.2
  refine ⟨3*constant,mul_nonneg (by norm_num) constant0,?_⟩
  intro reference insideR seed insideS base axis compactNonnegative alphaSmall deltaSmall parameterSmall small bounded source
  dsimp only
  intro family native core sameCore image sameImage
  have actual := bound reference insideR seed insideS base axis compactNonnegative alphaSmall deltaSmall parameterSmall small bounded source
    family native core sameCore image sameImage
  have product := mul_le_mul_of_nonneg_right bounded (norm_nonneg (quotientEta parameters 24 source.val.val))
  have payment : ‖quotientEta parameters (0+24) source.val.val‖+
      (1+physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
        (seed 0) base.1 (0+24))*‖quotientEta parameters 24 source.val.val‖≤3*‖quotientEta parameters 24 source.val.val‖ := by
    norm_num only [Nat.zero_add]
    nlinarith only [product]
  exact actual.trans ((mul_le_mul_of_nonneg_left payment constant0).trans_eq (by ring))

end Grad.OriginalCollarNorm
