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

/-- The native current theorem transported through literal unit-state data.
All native source, compatibility, phase and covariant fidelity come from
the SAME canonical packet; only the carrier equality is transported. -/
theorem originalUnit_current (radius : ℝ) (radiusNonnegative : 0≤radius)
    (unit : OriginalUnitRankState parameters length radius)
    (sameData : unit.val = (nativeState.val.val.rho,nativeState.val.val.alpha,nativeState.val.val.delta,
      nativeState.val.val.parameter,nativeState.val.val.epsilon,nativeState.val.val.field))
    (circle : ACore parameters 3)
    (sameCircle : originalSourceFieldLinear parameters circle =
      originalCircleKernel (originalSourceFieldLinear parameters packet.covariant)) :
    originalCurrentKernel (unitDiskAdmissible parameters) unit.data.gaugeDeviation
      (unit.coherent radiusNonnegative).2.2.2.1 (unit.inverseCoherent radiusNonnegative)
      (originalSourceFieldLinear parameters circle)=originalSourceFieldLinear parameters packet.covariant := by
  have budgetEq (grade : ℕ) : physicalBudget parameters unit.field unit.rho unit.epsilon grade=
      physicalBudget parameters nativeState.val.val.field nativeState.val.val.rho nativeState.val.val.epsilon grade :=
    congrArg (fun data : OriginalUnitRankData parameters => physicalBudget parameters data.field data.rho data.epsilon grade) sameData
  have gaugeSame (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :=
    (unit.gauge_matrix grade angle point).trans (congrArg
      (fun data : OriginalUnitRankData parameters => originalPhysicalGaugeMatrix parameters length data.rho data.alpha data.delta
        data.parameter data.epsilon data.field angle point) sameData)
  have bound (grade : ℕ) := (unit.rowBounds radiusNonnegative grade).1.trans_eq
    (congrArg (fun budget : ℝ => originalUnitFour parameters length radius grade*budget) (budgetEq (grade+4)))
  have low := (budgetEq 6).symm.trans_le
    ((physicalBudget_monotone parameters unit.field unit.rho unit.epsilon (by norm_num : 6≤12)).trans unit.unit)
  have small := (budgetEq 6).symm.trans_le unit.determinantLow
  exact actualOriginalUnit_core_current parameters length compact lengthPositive widthHalf widthLength nativeState nativeSmall
    residual residualFlat packet.family.limit (fun index => (packet.family.equations index).1)
    (fun index => (packet.family.equations index).2.1)
    (fun index grade => ⟨packet.family.graded index grade,packet.family.inserted index grade⟩) packet.family.compatible
    unit.data.gaugeDeviation (unit.coherent radiusNonnegative).2.2.2.1 (unit.inverseCoherent radiusNonnegative)
    gaugeSame (originalUnitFour parameters length radius) (originalUnitFour_nonnegative parameters length radius)
    low bound small packet.covariant circle packet.covariantSame sameCircle

end NativeRecoveryPacket
end Grad.OriginalMainConsumer
