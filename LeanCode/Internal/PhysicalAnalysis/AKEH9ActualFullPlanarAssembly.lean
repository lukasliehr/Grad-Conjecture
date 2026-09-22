import AKEH7ActualPacketLowerPayment
import AKEH8ActualNormStateAndCutoff
import AKEH6OriginalPlanarPartition
import AKDV30ActualCompactAnnularNorm
import AKDV11ActualCompactHighRankAbsorption

noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 900000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology ContDiff
namespace Grad.OriginalMainConsumer
open Grad.ActualPuncturedFamily Grad.Constraints Grad.Q24Realization Grad.AxisSplit Grad.ChartAxisLift Grad.ConstrainedTransfer Grad.NonlinearQuotientBounds
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




open Grad.ActualScaledNativeCoefficients Grad.ActualCartesianDescent Grad.OriginalCartesianTameEstimate
open Grad.ActualCartesianWeakEquations Grad.ActualScalarWeakEquations Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.SourceBoundaryTrace Grad.ActualCartesianFlux Grad.ActualNativeCellMoments
open Grad.SourceCollarCoefficients Grad.CartesianStartup Grad.ActualSmoothPhysicalField Grad.ActualPuncturedReconstruction
open Grad.NonlinearProduct


open Grad.RealFixedRanges Grad.PhysicalCoordinates Grad.NashMoser.OriginalIteration
open Grad.NashMoser.OriginalLimit Grad.OriginalInverseNeighborhood Grad.FinitePhysicalJetLift

open Grad.PDEBootstrap Grad.GenericCarriers
open Grad.ActualOriginalSourceMoments
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.WeightedJets.ZeroExtension
variable (parameters : PhaseParameters) (positive : 0<parameters.length)
  (reference : Seed.Parameters) (inside : reference∈Seed.parameterDomain)
  (center : Seed.Parameters) (insideC : center∈Seed.parameterDomain) (zeroC : center 0=0)
  (widthHalf : parameters.gamma≤1/2) (widthLength : parameters.gamma≤Real.sqrt 5/(6*parameters.length))
  (higher : ℕ) (higherLarge : 24≤higher)

/-- The inner estimate on the actual bundled inputs, before selecting a
state or source. This private integration interface is discharged by the
literal compact equation in the next consumer. -/
def ActualPrincipalInsideEstimate : Prop :=
  ∀ rank (epsilon : ℝ),0<epsilon→∃ constant : ℝ,0≤constant ∧
    ∀ (datum : ActualPrincipalNormState parameters positive reference inside center insideC zeroC higher)
      (image : ACore parameters 3),
    let packet := ActualPrincipalNormState.packet parameters positive reference inside center insideC zeroC
      higher higherLarge widthHalf widthLength datum;
    originalSourceFieldLinear parameters image=
      startupCutoffL2 actualNativeInsideCutoff actualNativeInsideCutoff_smooth actualNativeInsideCutoff_compact
        (originalSourceFieldLinear parameters packet.core) →
    originalPlanarNorm parameters (rank+2) image≤epsilon*originalGradeNorm (rank+2) packet.core+
      constant*StartupOriginalUnitNormPacket.low parameters parameters.length (1+‖center‖) (rank+2) parameters.length⁻¹ packet

/-- Joining the SAME inside and annular pieces gives the exact full-core
planar estimate, with no rank shift or extra high factor. -/
def actualPrincipalPlanar_of_inside
    (insideEstimate : ActualPrincipalInsideEstimate parameters positive reference inside center insideC zeroC
      widthHalf widthLength higher higherLarge) :
    ActualProductCompactPlanarEstimate
      (actualPrincipalProduct parameters positive reference inside center insideC zeroC
        actualNativeOuterCutoff actualNativeOuterCutoff_smooth actualNativeOuterCutoff_compact)
      widthHalf widthLength higher higherLarge 0 := by
  let product := actualPrincipalProduct parameters positive reference inside center insideC zeroC
    actualNativeOuterCutoff actualNativeOuterCutoff_smooth actualNativeOuterCutoff_compact
  let epsilon := fun grade => 1/(4*apMassEndpointConstant 0 grade+2)
  have epsilonPositive (grade : ℕ) : 0<epsilon grade := by
    apply div_pos zero_lt_one
    have positive := apMassEndpointConstant_nonnegative 0 grade
    linarith
  let innerResult := fun grade => insideEstimate (grade-2) (epsilon grade) (epsilonPositive grade)
  let innerConstant : ℕ→ℝ := fun grade => (innerResult grade).choose
  let lowResult := fun grade => actualPrincipalNormPacket_low_payment parameters positive reference inside center insideC zeroC
    actualNativeOuterCutoff actualNativeOuterCutoff_smooth actualNativeOuterCutoff_compact
    widthHalf widthLength higher higherLarge grade
  let annularResult := fun grade => actualProduct_compactAnnularNorm product widthHalf widthLength higher higherLarge grade
  refine { constant := fun grade => innerConstant grade*(lowResult grade).choose+(annularResult grade).choose
           nonnegative := fun grade => add_nonneg (mul_nonneg (innerResult grade).choose_spec.1 (lowResult grade).choose_spec.1)
             (annularResult grade).choose_spec.1
           bounded := ?_ }
  intro finite member state low source grade gradeLarge
  let datum : ActualPrincipalNormState parameters positive reference inside center insideC zeroC higher :=
    ⟨(finite,state,source),member,low⟩
  let core := canonicalProductCompactCore product widthHalf widthLength higher higherLarge finite member state low source
  let field := actualFiniteCurrentField parameters reference inside finite.1
    (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)
  let packet := ActualPrincipalNormState.packet parameters positive reference inside center insideC zeroC higher higherLarge
    widthHalf widthLength datum
  let innerCut := startupOriginalCutoff_core_exists parameters actualNativeInsideCutoff
    actualNativeInsideCutoff_smooth actualNativeInsideCutoff_compact core
  let annularCut := startupOriginalCutoff_core_exists parameters actualNativeAnnularCutoff
    actualNativeAnnularCutoff_smooth actualNativeAnnularCutoff_compact core
  have joined := actualNativeCutoff_planar_partition parameters grade core innerCut.choose annularCut.choose
    innerCut.choose_spec annularCut.choose_spec
  have innerBound : originalPlanarNorm parameters (grade-2+2) innerCut.choose≤
      epsilon grade*originalGradeNorm (grade-2+2) packet.core+
      innerConstant grade*StartupOriginalUnitNormPacket.low parameters parameters.length (1+‖center‖) (grade-2+2) parameters.length⁻¹ packet :=
    (innerResult grade).choose_spec.2 datum innerCut.choose innerCut.choose_spec
  have gradeSame : grade-2+2=grade := by omega
  rw [gradeSame] at innerBound
  have lowBound := (lowResult grade).choose_spec.2 finite member state low source
  have annularBound := (annularResult grade).choose_spec.2 finite member state low source annularCut.choose annularCut.choose_spec
  let payment := originalCellNorm parameters grade core+
    (1+physicalBudget parameters field (finite.1 0) finite.2 (grade+32))*originalGradeNorm 0 core+
    ‖quotientEta parameters (grade+32) source.val.val‖+
    (1+physicalBudget parameters field (finite.1 0) finite.2 (grade+32))*‖quotientEta parameters 32 source.val.val‖
  have prefixNonnegative : 0≤originalCellNorm parameters grade core+
      (1+physicalBudget parameters field (finite.1 0) finite.2 (grade+32))*originalGradeNorm 0 core :=
    add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _))
      (originalGradeNorm_nonnegative 0 core))
  have sourceLe : ‖quotientEta parameters (grade+32) source.val.val‖+
      (1+physicalBudget parameters field (finite.1 0) finite.2 (grade+32))*‖quotientEta parameters 32 source.val.val‖≤payment := by
    dsimp only [payment]
    linarith only [prefixNonnegative]
  have annularPaid := annularBound.trans (mul_le_mul_of_nonneg_left sourceLe (annularResult grade).choose_spec.1)
  have innerPaid := mul_le_mul_of_nonneg_left lowBound (innerResult grade).choose_spec.1
  change originalPlanarNorm parameters grade core≤epsilon grade*originalGradeNorm grade core+
    (innerConstant grade*(lowResult grade).choose+(annularResult grade).choose)*payment
  calc
    originalPlanarNorm parameters grade core≤originalPlanarNorm parameters grade innerCut.choose+
      originalPlanarNorm parameters grade annularCut.choose := joined
    _≤epsilon grade*originalGradeNorm grade core+
      innerConstant grade*StartupOriginalUnitNormPacket.low parameters parameters.length (1+‖center‖) grade parameters.length⁻¹ packet+
      (annularResult grade).choose*payment := add_le_add innerBound annularPaid
    _≤epsilon grade*originalGradeNorm grade core+
      innerConstant grade*((lowResult grade).choose*payment)+(annularResult grade).choose*payment :=
      add_le_add (add_le_add (le_refl _) innerPaid) (le_refl _)
    _=epsilon grade*originalGradeNorm grade core+
      (innerConstant grade*(lowResult grade).choose+(annularResult grade).choose)*payment := by ring

end Grad.OriginalMainConsumer
