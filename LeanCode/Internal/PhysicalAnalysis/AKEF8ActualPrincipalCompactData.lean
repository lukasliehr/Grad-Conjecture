import AKEF7RecoveryPacketCompactData
import AKEH5ActualPrincipalNormPacket
import AKEH2ActualProductNormPacket

noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 900000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology ContDiff ContDiff
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

open Grad.WeightedJets.ZeroExtension Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
/-- The actual canonical product has the genuine compact equation at every
order; no native bound, PDE, phase, coefficient or source-identity input remains. -/
theorem actualPrincipal_compactData
    (cutoff : Spatial → ℝ) (cutSmooth : ContDiff ℝ ∞ cutoff) (cutCompact : HasCompactSupport cutoff) (order : ℕ) :
    let radiusNonnegative : 0≤1+‖center‖ := by positivity;
    let normPacket := actualPrincipalNormPacket parameters positive reference inside center insideC zeroC outer smooth compact
      widthHalf widthLength higher higherLarge finite member state low source;
    ∃ data : StartupCompactSpatialEquation order (tsupport cutoff),
      base 3 order openUnitDisk (fun _ => 0) data.field=startupCutoffL2 cutoff cutSmooth cutCompact normPacket.field.field ∧
      (∀ outer inner,base 3 order openUnitDisk (fun _ => 0) (data.tensor outer inner)=
        startupCutoffL2 cutoff cutSmooth cutCompact (normPacket.tensorFamily radiusNonnegative outer inner).field) ∧
      base 3 order openUnitDisk (fun _ => 0) data.zeroth=
        startupCutoffEquationZeroth cutoff cutSmooth cutCompact normPacket.field.field
          (startupSignedPhaseZeroth parameters one_ne_zero startupOriginalUnitScale normPacket.field
            (normPacket.tensorFamily radiusNonnegative) (normPacket.fluxFamily radiusNonnegative parameters.length⁻¹) 0)
          (fun outer inner => (normPacket.tensorFamily radiusNonnegative outer inner).field)
          (startupSignedPhaseFlux parameters one_ne_zero startupOriginalUnitScale normPacket.field
            (normPacket.tensorFamily radiusNonnegative) (normPacket.fluxFamily radiusNonnegative parameters.length⁻¹) 0) ∧
      ∀ direction,base 3 order openUnitDisk (fun _ => 0) (data.flux direction)=
        startupCutoffEquationFlux cutoff cutSmooth cutCompact normPacket.field.field
          (fun outer inner => (normPacket.tensorFamily radiusNonnegative outer inner).field)
          (startupSignedPhaseFlux parameters one_ne_zero startupOriginalUnitScale normPacket.field
            (normPacket.tensorFamily radiusNonnegative) (normPacket.fluxFamily radiusNonnegative parameters.length⁻¹) 0) direction := by
  let product := actualPrincipalProduct parameters positive reference inside center insideC zeroC outer smooth compact
  let packet := canonicalProductRecovery product widthHalf widthLength higher higherLarge finite member state low source
  let unit := actualPrincipalUnitState parameters positive reference inside center insideC zeroC outer smooth compact
    higher higherLarge finite member state low
  let circle := canonicalProductCompactCore product widthHalf widthLength higher higherLarge finite member state low source
  let insideS := product.neighborhood.patchInside (product.neighborhood.seedInside finite member)
  let cubic := actualJetExhaustion_cubicSmall parameters parameters.length product.coefficientBound reference inside finite.1
    insideS (finite.2,state) (actualProduct_recovery_smallness product higher higherLarge finite member state low).1
  have vanishing := actualFiniteSourceResidual_higherVanishing parameters parameters.length (finite.1 0) positive
    reference inside finite.1 insideS (finite.2,state) cubic ((product.neighborhood.raiseBase higher higherLarge).axis state low) source
  have bounded := (product.budget finite member state (product.neighborhood.raiseBase_low higher higherLarge state low)).le.trans (min_le_left _ _)
  have low14 : physicalBudget parameters unit.field unit.rho unit.epsilon 14≤1 :=
    (physicalBudget_monotone parameters unit.field unit.rho unit.epsilon (by norm_num : 14≤24)).trans bounded
  have radiusNonnegative : 0≤1+‖center‖ := by positivity
  exact packet.originalUnit_compactData (1+‖center‖) radiusNonnegative unit rfl circle
    (canonicalProductCompactCore_sameCircle product widthHalf widthLength higher higherLarge finite member state low source)
    (productRecoveryResidualNativeConstant_nonnegative parameters positive product.coefficientBound)
    low14 vanishing cutoff cutSmooth cutCompact order

end Grad.OriginalMainConsumer
