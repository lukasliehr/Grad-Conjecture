import AKEF6ActualNativeCompactData
import AKEG7ActualNativeRoughRowBounds
import AKEH1OriginalSourceNormPacket
import AKDV20NativeRecoveryPacket
import AKDW8SameOriginalCoreCurrent
import AKDS34OriginalUnitLedgerFidelity

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


variable (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
  (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
  (nativeState : RetainedInverseState parameters length compact)
  (nativeSmall : physicalBudget parameters nativeState.val.val.field nativeState.val.val.rho nativeState.val.val.epsilon 8 ≤
    originalExhaustionPrimitiveRadius parameters length compact)
  (residual : SmoothQuotient parameters) (residualFlat : IsFlat residual)
  (fullSource : SmoothQuotient parameters) (nativeConstant cellConstant : ℕ → ℝ) (baseConstant : ℝ) (residualNativeConstant : ℕ → ℝ)

open Grad.ActualGaugeSigmaPrimitives

namespace NativeRecoveryPacket
variable {parameters length compact lengthPositive widthHalf widthLength nativeState nativeSmall residual residualFlat
  fullSource nativeConstant cellConstant baseConstant residualNativeConstant}
  (packet : NativeRecoveryPacket parameters length compact lengthPositive widthHalf widthLength
    nativeState nativeSmall residual residualFlat fullSource nativeConstant cellConstant baseConstant residualNativeConstant)

open Grad.ActualOriginalSourceMoments Grad.WeightedJets.ZeroExtension Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
/-- Exact compact PDE data for the SAME recovery packet; all native weak,
source, matrix, phase and spatial regularity conditions are discharged. -/
theorem originalUnit_compactData (radius : ℝ) (radiusNonnegative : 0≤radius)
    (unit : OriginalUnitRankState parameters length radius)
    (sameData : unit.val=(nativeState.val.val.rho,nativeState.val.val.alpha,nativeState.val.val.delta,
      nativeState.val.val.parameter,nativeState.val.val.epsilon,nativeState.val.val.field))
    (circle : ACore parameters 3)
    (sameCircle : originalSourceFieldLinear parameters circle=originalCircleKernel (originalSourceFieldLinear parameters packet.covariant))
    (costNonnegative : ∀ grade,0≤residualNativeConstant grade)
    (low : physicalBudget parameters nativeState.val.val.field nativeState.val.val.rho nativeState.val.val.epsilon 14≤1)
    (vanishing : SourceHigherVanishing residual)
    (cutoff : Spatial → ℝ) (cutSmooth : ContDiff ℝ ∞ cutoff) (cutCompact : HasCompactSupport cutoff) (order : ℕ) :
    let normPacket := originalSourceNormPacket unit circle residual;
    ∃ data : StartupCompactSpatialEquation order (tsupport cutoff),
      base 3 order openUnitDisk (fun _ => 0) data.field=startupCutoffL2 cutoff cutSmooth cutCompact normPacket.field.field ∧
      (∀ outer inner,base 3 order openUnitDisk (fun _ => 0) (data.tensor outer inner)=
        startupCutoffL2 cutoff cutSmooth cutCompact (normPacket.tensorFamily radiusNonnegative outer inner).field) ∧
      base 3 order openUnitDisk (fun _ => 0) data.zeroth=
        startupCutoffEquationZeroth cutoff cutSmooth cutCompact normPacket.field.field
          (startupSignedPhaseZeroth parameters one_ne_zero startupOriginalUnitScale normPacket.field
            (normPacket.tensorFamily radiusNonnegative) (normPacket.fluxFamily radiusNonnegative length⁻¹) 0)
          (fun outer inner => (normPacket.tensorFamily radiusNonnegative outer inner).field)
          (startupSignedPhaseFlux parameters one_ne_zero startupOriginalUnitScale normPacket.field
            (normPacket.tensorFamily radiusNonnegative) (normPacket.fluxFamily radiusNonnegative length⁻¹) 0) ∧
      ∀ direction,base 3 order openUnitDisk (fun _ => 0) (data.flux direction)=
        startupCutoffEquationFlux cutoff cutSmooth cutCompact normPacket.field.field
          (fun outer inner => (normPacket.tensorFamily radiusNonnegative outer inner).field)
          (startupSignedPhaseFlux parameters one_ne_zero startupOriginalUnitScale normPacket.field
            (normPacket.tensorFamily radiusNonnegative) (normPacket.fluxFamily radiusNonnegative length⁻¹) 0) direction := by
  let rough := packet.family.roughRowBounds residualNativeConstant costNonnegative packet.residualNativeBound low
  let M := rough.choose
  have Mnonnegative := rough.choose_spec.1
  have stateBound := rough.choose_spec.2.1
  have retainedBound := rough.choose_spec.2.2.1
  let gradeCertificate := rough.choose_spec.2.2.2
  let constants := gradeCertificate.choose
  have estimate := gradeCertificate.choose_spec
  exact actualOriginalUnit_compactData parameters length compact lengthPositive widthHalf widthLength nativeState nativeSmall
    residual residualFlat packet.family.limit (fun index => (packet.family.equations index).1)
    (fun index => (packet.family.equations index).2.1)
    (fun index grade => ⟨packet.family.graded index grade,packet.family.inserted index grade⟩) packet.family.compatible
    M Mnonnegative stateBound vanishing retainedBound packet.family.graded packet.family.inserted constants estimate
    radiusNonnegative unit sameData packet.covariant circle packet.covariantSame sameCircle cutoff cutSmooth cutCompact order

end NativeRecoveryPacket
end Grad.OriginalMainConsumer
