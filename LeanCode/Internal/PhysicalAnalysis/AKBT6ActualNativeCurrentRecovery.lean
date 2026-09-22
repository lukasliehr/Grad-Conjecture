import AKBT5ActualNativeGaugeContinuity
import AKBQ8SameScaledNativeGluing
import AKBQ9ActualObservedNativeGauges
import AKBK5SameNativeGlobalForceFields

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace Grad.ActualScaledNativeCoefficients
open Grad.ActualCartesianWeakEquations Grad.CartesianStartup Grad.GenericCarriers
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





open Grad.AnnularKernelContinuity
open Grad.AnnularPhysicalReconstruction Grad.AnnularKernelL2 Grad.SourceCollarDivision


open Grad.ActualPuncturedReconstruction Grad.AnnularCurrentEnergy

open Grad.ActualPuncturedFamily Grad.ActualPhysicalField

variable (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (fields : ∀ index, OriginalFiveBlockAmbient parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index))


variable
    (member : ∀ index, fields index ∈ OriginalObservedEquationGraph parameters length compact
      (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index)
      (originalExhaustionRadius_half length lengthPositive index) lengthPositive widthHalf widthLength state)
    (sameSources : ∀ index, (fields index).ofLp.2 =
      (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0).val.ofLp.1)
    (allGrades : ∀ index grade : ℕ, ∃ weighted : CoupledSpace (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index) lengthPositive,
      CoupledInsertedGrade (originalExhaustionRadius length index) length
        (originalExhaustionRadius_positive length lengthPositive index) lengthPositive grade
        (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length
          (originalExhaustionRadius_positive length lengthPositive index)
          ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index)) weighted)


open Grad.ActualCartesianFlux
open Grad.ActualCartesianDescent Grad.ClosedJets Grad.DiskExtension.Operator Grad.BoundaryTrace Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularGeneralSourceRegularity Grad.ActualSmoothPhysicalField Grad.PuncturedRetainedEnergy
variable (compatible : ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)


open Grad.PDEBootstrap Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope Grad.Constraints Grad.Constraints.Gauges


include compatible in
/-- The actual original native gauges recover the SAME full weighted
covariant from its fixed Q0 quotient before any H1 regularity is known. -/
theorem actualNative_current_recovers {ell : ℝ}
    (admissible : Admissible length parameters.sigma0 parameters.gamma ell)
    (ledger : ActualLedger parameters admissible state.val.val.rho state.val.val.alpha state.val.val.delta
      state.val.val.parameter state.val.val.epsilon state.val.val.field)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation))
    (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖ledger.val.gaugeDeviation grade‖ ≤ constants grade *
      physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+4))
    (determinantSmall : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 6 ≤ determinantLowRadius constants)
    (weighted : StartupL2 3)
    (same : StartupWeightedRep parameters.sigma0 parameters.gamma ell weighted (actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades ell)) :
    originalCurrentKernel admissible ledger.val.gaugeDeviation ledger.property.1.2.2.2.1 inverseCoherent
      (originalCircleKernel weighted) = weighted := by
  apply startupSameRough_current_fromPolarGauges parameters admissible state.val.val.field state.val.val.rho state.val.val.epsilon
    ledger.val.gaugeDeviation ledger.property.1.2.2.2.1 inverseCoherent constants nonnegative low bound determinantSmall
    weighted (actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades ell) same
    (actualScaledCovariantRaw_regular parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible ell admissible.2.2.2.1 (admissible.2.2.2.2.trans (min_le_left _ _)))
    (actualScaledNativeMatrix_cell_continuous parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible admissible (fullGaugeFamily ledger.val.gaugeDeviation))
  exact actualScaledCovariantRaw_gaugeMeans parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible admissible ledger

end Grad.ActualScaledNativeCoefficients
