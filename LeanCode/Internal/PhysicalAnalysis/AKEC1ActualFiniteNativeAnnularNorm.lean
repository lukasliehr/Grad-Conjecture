import AKEA2ActualNativeAnnularPlanarNorm
import AKEB4ActualFiniteCollarLoss32

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

/-- Original-unit annular norm of the SAME finite residual covariant,
paid in the full original flat source before all finite data are chosen. -/
theorem actualFiniteCovariant_annularPlanarNorm
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0<length)
    (widthHalf : parameters.gamma≤1/2) (widthLength : parameters.gamma≤Real.sqrt 5/(6*length))
    (grade : ℕ) (cost : ℕ → ℝ) (cost0 : ∀ order,0≤cost order) :
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
      originalPlanarNorm parameters grade image≤constant*(‖quotientEta parameters (grade+24) source.val.val‖+
        (1+physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
          (seed 0) base.1 (grade+24))*‖quotientEta parameters 24 source.val.val‖) := by
  have collar : originalExhaustionRadius length 3≤(1/8:ℝ) := by
    unfold originalExhaustionRadius
    norm_num only [Nat.cast_ofNat]
    have numerator := min_le_left (1/2:ℝ) length
    linarith
  let annular := nativeCovariant_annularPlanarNorm parameters length compact lengthPositive widthHalf widthLength 3 grade collar cost cost0
  let normConstant := annular.choose
  have norm0 : 0≤normConstant := annular.choose_spec.1
  have normBound := annular.choose_spec.2
  let paymentCertificate := actualFiniteSourceResidual_collar_payment parameters length grade
  let paymentConstant := paymentCertificate.choose
  have payment0 : 0≤paymentConstant := paymentCertificate.choose_spec.1
  have paymentBound := paymentCertificate.choose_spec.2
  refine ⟨normConstant*paymentConstant,mul_nonneg norm0 payment0,?_⟩
  intro reference insideR seed insideS base axis compactNonnegative alphaSmall deltaSmall parameterSmall small bounded source
  dsimp only
  let field := actualFiniteCurrentField parameters reference insideR seed insideS base
  let low := actualJetExhaustion_cubicSmall parameters length compact reference insideR seed insideS base small
  let state := actualJetExhaustionState parameters length compact reference insideR seed insideS base small
    compactNonnegative alphaSmall deltaSmall parameterSmall
  let exSmall := actualJetExhaustion_exSmall parameters length compact reference insideR seed insideS base small
  let residual := actualFiniteSourceResidual parameters length (seed 0) reference insideR seed insideS base low source
  let flat := actualFiniteSourceResidual_isFlat parameters length (seed 0) lengthPositive reference insideR seed insideS base low axis source
  intro family native core sameCore image sameImage
  have unit : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 15≤1 :=
    (physicalBudget_monotone parameters field (seed 0) base.1 (by norm_num : 15≤24)).trans bounded
  have estimate := normBound state unit exSmall residual flat family native core sameCore image sameImage
  have payment := paymentBound reference insideR seed insideS base (seed 0) low bounded source
  exact estimate.trans ((mul_le_mul_of_nonneg_left payment norm0).trans_eq (mul_assoc _ _ _).symm)

end Grad.OriginalCollarNorm
