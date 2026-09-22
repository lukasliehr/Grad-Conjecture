import AKDM5RecoveredCoreMomentFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.OriginalCartesianTameEstimate
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
open scoped ENNReal BigOperators

variable {parameters : PhaseParameters} {length compact : ℝ} {lengthPositive : 0 < length}
    {widthHalf : parameters.gamma ≤ 1 / 2} {widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)}
    {state : RetainedInverseState parameters length compact}
    {small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact}
    {source : SmoothQuotient parameters} {flat : IsFlat source}

open Grad.ActualPhysicalField Grad.ActualCartesianFlux Grad.ActualPuncturedReconstruction
open Grad.PuncturedRetainedEnergy Grad.AnnularPhysicalReconstruction

open Grad.CartesianStartup Grad.ActualCartesianDescent

/-- The SAME recovered original covariant core inherits the actual native
pure-cell endpoint, at the original width and with independent base payment. -/
theorem recoveredCovariant_originalCellEndpoint
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (small12 : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 12 ≤ 1)
    (core : ACore parameters 3)
    (coreSame : ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ cell : ℤ,
      (core.val cell).value point =
        actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat family.limit
          (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
          (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) cell point.val)
    (payment : ℕ → ℝ) (nonnegative : ∀ grade, 0≤payment grade)
    (bound : ∀ index grade, family.nativeNorm index grade ≤ payment grade)
    (basePayment : ℝ) (baseNonnegative : 0≤basePayment)
    (baseBound : ∀ index, family.nativeNorm index 0 ≤ basePayment) :
    ∀ grade, originalCellNorm parameters grade core ≤
      Real.sqrt (2*Real.pi)*nativeCovariantEndpointConstant parameters length compact grade *
        (payment grade+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+12)*basePayment) := by
  obtain ⟨moments,same,estimate⟩ := nativeCovariant_allCellEndpoint family small12
    payment nonnegative bound basePayment baseNonnegative baseBound
  intro grade
  rw [originalCellNorm_eq_recoveredMoment parameters core moments _ coreSame same grade]
  exact estimate grade

end Grad.OriginalCartesianTameEstimate
