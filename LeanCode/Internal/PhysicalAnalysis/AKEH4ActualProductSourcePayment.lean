import AKEH2ActualProductNormPacket
import AKEH3KnownSourceNormPayment
import AKEB3ActualFiniteCollarPayment

noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 900000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
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

open Grad.ActualOriginalSourceMoments
variable {parameters : PhaseParameters} {positive : 0 < parameters.length}
  {reference : Seed.Parameters} {inside : reference ∈ Seed.parameterDomain} {center : Seed.Parameters}
  (product : OriginalPhysicalProduct parameters positive reference inside center)
  (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*parameters.length))
  (higher : ℕ) (higherLarge : 24 ≤ higher)

/-- The actual known tensor/flux payment is uniformly paid by the full
original source at fixed base32, before finite data or source are chosen. -/
theorem actualProductNormPacket_sourcePayment (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ finite (member : finite ∈ product.neighborhood.parameterDomain)
      (state : stateSmoothRange parameters reference inside)
      (low : stateSize parameters reference inside higher 0 state ≤ 2*product.neighborhood.radius)
      (source : OriginalFlatSource parameters parameters.length) {radius : ℝ}
      (coefficient : OriginalUnitRankState parameters parameters.length radius),
      StartupOriginalUnitNormPacket.sourcePayment grade parameters.length⁻¹
        (actualProductNormPacket product widthHalf widthLength higher higherLarge finite member state low source coefficient) ≤
      constant*(‖quotientEta parameters (grade+32) source.val.val‖+
        (1+physicalBudget parameters (actualFiniteCurrentField parameters reference inside finite.1
          (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state))
          (finite.1 0) finite.2 (grade+32))*‖quotientEta parameters 32 source.val.val‖) := by
  let sources := originalSourceNormPacket_sourcePayment parameters parameters.length parameters.length⁻¹ grade
  let residuals := actualFiniteSourceResidual_collar_payment parameters parameters.length grade
  have sources0 := sources.choose_spec.1
  have residuals0 := residuals.choose_spec.1
  refine ⟨sources.choose*residuals.choose,mul_nonneg sources0 residuals0,?_⟩
  intro finite member state low source radius coefficient
  let insideS := product.neighborhood.patchInside (product.neighborhood.seedInside finite member)
  let field := actualFiniteCurrentField parameters reference inside finite.1 insideS (finite.2,state)
  let residual := actualProductResidual product higher higherLarge finite member state low source
  let core := canonicalProductCompactCore product widthHalf widthLength higher higherLarge finite member state low source
  let cubic := actualJetExhaustion_cubicSmall parameters parameters.length product.coefficientBound reference inside finite.1
    insideS (finite.2,state) (actualProduct_recovery_smallness product higher higherLarge finite member state low).1
  have bounded : physicalBudget parameters field (finite.1 0) finite.2 24 ≤ 1 :=
    (product.budget finite member state (product.neighborhood.raiseBase_low higher higherLarge state low)).le.trans (min_le_left _ _)
  have residualBound := residuals.choose_spec.2 reference inside finite.1 insideS (finite.2,state) (finite.1 0) cubic bounded source
  have highSource : ‖quotientEta parameters (grade+1) residual‖ ≤
      ‖quotientEta parameters (grade+10) residual‖+
        (1+physicalBudget parameters field (finite.1 0) finite.2 (grade+16))*‖quotientEta parameters 9 residual‖ :=
    (referenceSource_norm_mono parameters (by omega : grade+1≤grade+10) residual).trans
      (le_add_of_nonneg_right (mul_nonneg (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)) (norm_nonneg _)))
  have paid := highSource.trans residualBound
  have promoted := paid.trans (mul_le_mul_of_nonneg_left (add_le_add
    (referenceSource_norm_mono parameters (by omega : grade+24≤grade+32) source.val.val)
    (mul_le_mul (add_le_add (le_refl _) (physicalBudget_monotone parameters field (finite.1 0) finite.2 (by omega : grade+24≤grade+32)))
      (referenceSource_norm_mono parameters (by norm_num : 24≤32) source.val.val) (norm_nonneg _)
      (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)))) residuals0)
  exact (sources.choose_spec.2 coefficient core residual).trans
    ((mul_le_mul_of_nonneg_left promoted sources0).trans_eq (mul_assoc _ _ _).symm)

end Grad.OriginalMainConsumer
