import AKDV2CanonicalSameProductRecovery
import AKDS42OriginalCompactCellRecovery

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




open Grad.GaugeCoefficients.Physical.RadialLedger
attribute [local irreducible] canonicalProductRecovery NativeRecoveryPacket.family
  NativeRecoveryPacket.covariant NativeRecoveryPacket.vector NativeRecoveryPacket.scalar actualFiniteCurrentField

variable {parameters : PhaseParameters} {positive : 0 < parameters.length}
  {reference : Seed.Parameters} {inside : reference ∈ Seed.parameterDomain} {center : Seed.Parameters}

/-- A fixed original core representing the literal circle projection. -/
def canonicalOriginalCompactCore (core : ACore parameters 3) : ACore parameters 3 :=
  (startupOriginalCircle_core_exists parameters core).choose

theorem canonicalOriginalCompactCore_sameCircle (core : ACore parameters 3) :
    originalSourceFieldLinear parameters (canonicalOriginalCompactCore core) =
      originalCircleKernel (originalSourceFieldLinear parameters core) :=
  (startupOriginalCircle_core_exists parameters core).choose_spec

/-- The compact core is chosen from the SAME canonical covariant solution. -/
def canonicalProductCompactCore
    (product : OriginalPhysicalProduct parameters positive reference inside center)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*parameters.length))
    (higher : ℕ) (higherLarge : 24 ≤ higher)
    (finite : OriginalFiniteParameter) (member : finite ∈ product.neighborhood.parameterDomain)
    (state : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside higher 0 state ≤ 2*product.neighborhood.radius)
    (source : OriginalFlatSource parameters parameters.length) : ACore parameters 3 :=
  canonicalOriginalCompactCore
    (canonicalProductRecovery product widthHalf widthLength higher higherLarge finite member state low source).covariant

/-- Fixed pure-cell constants are chosen before the state and source. -/
def productCompactCellConstant (parameters : PhaseParameters) (positive : 0 < parameters.length)
    (compact : ℝ) (grade : ℕ) : ℝ :=
  (originalCircle_sameCore_cell_bound parameters).choose grade *
    productRecoveryCellConstant parameters positive compact grade

theorem productCompactCellConstant_nonnegative (parameters : PhaseParameters)
    (positive : 0 < parameters.length) (compact : ℝ) (grade : ℕ) :
    0 ≤ productCompactCellConstant parameters positive compact grade :=
  mul_nonneg ((originalCircle_sameCore_cell_bound parameters).choose_spec.1 grade)
    (productRecoveryCellConstant_nonnegative parameters positive compact grade)

variable (product : OriginalPhysicalProduct parameters positive reference inside center)
  (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*parameters.length))
  (higher : ℕ) (higherLarge : 24 ≤ higher)
  (finite : OriginalFiniteParameter) (member : finite ∈ product.neighborhood.parameterDomain)
  (state : stateSmoothRange parameters reference inside)
  (low : stateSize parameters reference inside higher 0 state ≤ 2*product.neighborhood.radius)
  (source : OriginalFlatSource parameters parameters.length)

/-- Literal field identity, with no change to the original analytic carrier. -/
theorem canonicalProductCompactCore_sameCircle :
    originalSourceFieldLinear parameters
      (canonicalProductCompactCore product widthHalf widthLength higher higherLarge finite member state low source) =
    originalCircleKernel (originalSourceFieldLinear parameters
      (canonicalProductRecovery product widthHalf widthLength higher higherLarge finite member state low source).covariant) :=
  canonicalOriginalCompactCore_sameCircle _

/-- Every compact pure-cell norm is paid from the actual full source at
loss twenty; the unknown high compact or covariant norm never appears. -/
theorem canonicalProductCompactCore_cellBound (grade : ℕ) :
    originalCellNorm parameters grade
      (canonicalProductCompactCore product widthHalf widthLength higher higherLarge finite member state low source) ≤
    productCompactCellConstant parameters positive product.coefficientBound grade *
      (‖quotientEta parameters (grade+20) source.val.val‖+
        physicalBudget parameters
          (actualFiniteCurrentField parameters reference inside finite.1
            (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state))
          (finite.1 0) finite.2 (grade+20)*‖quotientEta parameters 20 source.val.val‖) := by
  let packet := canonicalProductRecovery product widthHalf widthLength higher higherLarge finite member state low source
  have circle := (originalCircle_sameCore_cell_bound parameters).choose_spec.2 packet.covariant
    (canonicalProductCompactCore product widthHalf widthLength higher higherLarge finite member state low source)
    (canonicalProductCompactCore_sameCircle product widthHalf widthLength higher higherLarge finite member state low source) grade
  have paid := circle.trans (mul_le_mul_of_nonneg_left (packet.cellBound grade)
    ((originalCircle_sameCore_cell_bound parameters).choose_spec.1 grade))
  exact paid.trans_eq (by rw [productCompactCellConstant, mul_assoc]; rfl)

end Grad.OriginalMainConsumer
