import AKEH2ActualProductNormPacket

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
variable (parameters : PhaseParameters) (positive : 0 < parameters.length)
  (reference : Seed.Parameters) (inside : reference ∈ Seed.parameterDomain)
  (center : Seed.Parameters) (insideC : center ∈ Seed.parameterDomain) (zeroC : center 0=0)
  (outer : Spatial → ℝ) (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)
  (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*parameters.length))
  (higher : ℕ) (higherLarge : 24 ≤ higher)

variable (finite : OriginalFiniteParameter) (member : finite ∈ ((actualPrincipalProduct parameters positive reference inside center insideC zeroC outer smooth compact)).neighborhood.parameterDomain)
  (state : stateSmoothRange parameters reference inside)
  (low : stateSize parameters reference inside higher 0 state ≤ 2*((actualPrincipalProduct parameters positive reference inside center insideC zeroC outer smooth compact)).neighborhood.radius)
  (source : OriginalFlatSource parameters parameters.length)

/-- Actual faithful physical-L coefficient and SAME canonical compact solution,
with the literal residual and source rows. This makes no new native choice. -/
def actualPrincipalNormPacket : StartupOriginalUnitNormPacket parameters parameters.length (1+‖center‖) :=
  actualProductNormPacket (actualPrincipalProduct parameters positive reference inside center insideC zeroC outer smooth compact) widthHalf widthLength higher higherLarge finite member state low source
    (actualPrincipalUnitState parameters positive reference inside center insideC zeroC outer smooth compact
      higher higherLarge finite member state low)

theorem actualPrincipalNormPacket_coefficient :
    ((actualPrincipalNormPacket parameters positive reference inside center insideC zeroC outer smooth compact widthHalf widthLength higher higherLarge finite member state low source)).coefficient=actualPrincipalUnitState parameters positive reference inside center insideC zeroC outer smooth compact
      higher higherLarge finite member state low := rfl

theorem actualPrincipalNormPacket_core :
    ((actualPrincipalNormPacket parameters positive reference inside center insideC zeroC outer smooth compact widthHalf widthLength higher higherLarge finite member state low source)).core=canonicalProductCompactCore (actualPrincipalProduct parameters positive reference inside center insideC zeroC outer smooth compact) widthHalf widthLength higher higherLarge finite member state low source := rfl

theorem actualPrincipalNormPacket_field_allSpatial (grade : ℕ) : ((actualPrincipalNormPacket parameters positive reference inside center insideC zeroC outer smooth compact widthHalf widthLength higher higherLarge finite member state low source)).field.HasSpatialGrade grade :=
  originalSourceNormPacket_field_allSpatial _ _ _ grade

theorem actualPrincipalNormPacket_force_allSpatial (grade : ℕ) : ((actualPrincipalNormPacket parameters positive reference inside center insideC zeroC outer smooth compact widthHalf widthLength higher higherLarge finite member state low source)).knownForce.toStartupSignedFamily.HasSpatialGrade grade :=
  originalSourceNormPacket_force_allSpatial _ _ _ grade

theorem actualPrincipalNormPacket_third_allSpatial (grade : ℕ) : ((actualPrincipalNormPacket parameters positive reference inside center insideC zeroC outer smooth compact widthHalf widthLength higher higherLarge finite member state low source)).knownThird.toStartupSignedFamily.HasSpatialGrade grade :=
  originalSourceNormPacket_third_allSpatial _ _ _ grade

theorem actualPrincipalNormPacket_determinant_allSpatial (grade : ℕ) : ((actualPrincipalNormPacket parameters positive reference inside center insideC zeroC outer smooth compact widthHalf widthLength higher higherLarge finite member state low source)).determinant.toStartupSignedFamily.HasSpatialGrade grade :=
  originalSourceNormPacket_determinant_allSpatial _ _ _ grade

end Grad.OriginalMainConsumer
