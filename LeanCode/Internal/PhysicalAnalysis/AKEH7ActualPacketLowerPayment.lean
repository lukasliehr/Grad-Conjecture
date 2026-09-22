import AKEH4ActualProductSourcePayment
import AKEH5ActualPrincipalNormPacket
import AKDW28PacketLowerGraphFactors

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
/-- A fixed source payment and a lower coefficient budget fit the exact
four-term payment used by the original compact absorption. -/
theorem packetLow_scalar_payment (cell base budget smallBudget sourcePayment sourceHigh sourceLow constant : ℝ)
    (cell0 : 0≤cell) (base0 : 0≤base) (budget0 : 0≤budget)
    (high0 : 0≤sourceHigh) (low0 : 0≤sourceLow) (constant0 : 0≤constant)
    (budgetBound : smallBudget≤budget)
    (sourceBound : sourcePayment≤constant*(sourceHigh+budget*sourceLow)) :
    cell+smallBudget*base+sourcePayment≤
      (1+constant)*(cell+budget*base+sourceHigh+budget*sourceLow) := by
  have first := mul_le_mul_of_nonneg_right budgetBound base0
  have leftover := mul_nonneg constant0 (add_nonneg cell0 (mul_nonneg budget0 base0))
  have source0 := add_nonneg high0 (mul_nonneg budget0 low0)
  nlinarith only [first,sourceBound,leftover,source0]

variable (parameters : PhaseParameters) (positive : 0<parameters.length)
  (reference : Seed.Parameters) (inside : reference∈Seed.parameterDomain)
  (center : Seed.Parameters) (insideC : center∈Seed.parameterDomain) (zeroC : center 0=0)
  (outer : Spatial→ℝ) (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)
  (widthHalf : parameters.gamma≤1/2) (widthLength : parameters.gamma≤Real.sqrt 5/(6*parameters.length))
  (higher : ℕ) (higherLarge : 24≤higher)

/-- All actual packet lower terms have the exact full-source base32 payment,
with constants fixed before the finite parameter, state, and source. -/
theorem actualPrincipalNormPacket_low_payment (grade : ℕ) :
    ∃ constant : ℝ,0≤constant ∧
    ∀ finite (member : finite∈(actualPrincipalProduct parameters positive reference inside center insideC zeroC outer smooth compact).neighborhood.parameterDomain)
      (state : stateSmoothRange parameters reference inside)
      (low : stateSize parameters reference inside higher 0 state≤2*(actualPrincipalProduct parameters positive reference inside center insideC zeroC outer smooth compact).neighborhood.radius)
      (source : OriginalFlatSource parameters parameters.length),
    let packet := actualPrincipalNormPacket parameters positive reference inside center insideC zeroC outer smooth compact
      widthHalf widthLength higher higherLarge finite member state low source;
    let field := actualFiniteCurrentField parameters reference inside finite.1
      ((actualPrincipalProduct parameters positive reference inside center insideC zeroC outer smooth compact).neighborhood.patchInside
        ((actualPrincipalProduct parameters positive reference inside center insideC zeroC outer smooth compact).neighborhood.seedInside finite member)) (finite.2,state);
    StartupOriginalUnitNormPacket.low parameters parameters.length (1+‖center‖) grade parameters.length⁻¹ packet≤
      constant*(originalCellNorm parameters grade packet.core+
        (1+physicalBudget parameters field (finite.1 0) finite.2 (grade+32))*originalGradeNorm 0 packet.core+
        ‖quotientEta parameters (grade+32) source.val.val‖+
        (1+physicalBudget parameters field (finite.1 0) finite.2 (grade+32))*‖quotientEta parameters 32 source.val.val‖) := by
  let product := actualPrincipalProduct parameters positive reference inside center insideC zeroC outer smooth compact
  let result := actualProductNormPacket_sourcePayment product widthHalf widthLength higher higherLarge grade
  refine ⟨1+result.choose,add_nonneg zero_le_one result.choose_spec.1,?_⟩
  intro finite member state low source
  let packet := actualPrincipalNormPacket parameters positive reference inside center insideC zeroC outer smooth compact
    widthHalf widthLength higher higherLarge finite member state low source
  let field := actualFiniteCurrentField parameters reference inside finite.1
    (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)
  have budgetBound : OriginalUnitRankState.budget grade packet.coefficient≤
      1+physicalBudget parameters field (finite.1 0) finite.2 (grade+32) := by
    change 1+physicalBudget parameters field (finite.1 0) finite.2 (12+grade)≤_
    exact add_le_add (le_refl 1) (physicalBudget_monotone parameters field (finite.1 0) finite.2 (by omega : 12+grade≤grade+32))
  exact packetLow_scalar_payment _ _ _ _ _ _ _ _ (Real.sqrt_nonneg _)
    (originalGradeNorm_nonnegative 0 packet.core)
    (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _))
    (norm_nonneg _) (norm_nonneg _) result.choose_spec.1 budgetBound
    (result.choose_spec.2 finite member state low source packet.coefficient)

end Grad.OriginalMainConsumer
