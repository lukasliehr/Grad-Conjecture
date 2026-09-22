import AKEG4NativeFourOperatorRealization
import AKDW5ActualOriginalUnitCurrentRecovery
import AKDW7OriginalUnitNativeSpatialEquation
import AKBT25ActualOriginalNativeH1

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace Grad.ActualScaledNativeCoefficients
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

open Grad.PhysicalFamily Grad.PDEBootstrap Grad.Constraints
open Grad.ActualScalarWeakEquations Grad.ActualForceMoments Grad.ActualCartesianEquations Grad.Constraints.Gauges

open Grad.ActualCurrentPrimitives

include compatible

variable (M : ℝ) (Mnonnegative : 0 ≤ M)
    (stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ M)
    (vanishing : SourceHigherVanishing source)
    (nativeBound : ∀ index, originalWeightedRetainedNorm parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index).ofLp.1 ≤
        2 * independentCoupledDataConstant parameters length compact *
          (originalSourceAllocationConstant parameters length 0 * (1 + M) * ‖quotientEta parameters 8 source‖))

open Grad.PhysicalAxisEquation
include Mnonnegative stateBound vanishing nativeBound

open Grad.CartesianStartup Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ActualNativeCellMoments Grad.ActualOriginalSourceMoments
variable (graded : ∀ index (_grade : ℕ), CoupledSpace (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index) lengthPositive)
    (sameGrade : ∀ index grade, CoupledInsertedGrade (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index) lengthPositive grade
      (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length
        (originalExhaustionRadius_positive length lengthPositive index)
        ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index)) (graded index grade))
    (constants : ℕ → ℝ) (estimate : ∀ index grade, ‖graded index grade‖ ≤ constants grade)
include sameGrade estimate



open Grad.SpatialDilation


open Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.ActualOriginalSourceFirst Grad.AnalyticWeights.Calculus
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.OriginalCoreRealization

/-- The same actual physical-length family supplies faithful unit-coordinate
weighted native ER rows, all four actual operators, and the unweighted 1/L equation. -/
theorem actualOriginalUnit_nativeRows {radius : ℝ}
    (radiusNonnegative : 0 ≤ radius)
    (coefficient : OriginalUnitRankState parameters length radius)
    (sameData : coefficient.val = (state.val.val.rho,state.val.val.alpha,state.val.val.delta,
      state.val.val.parameter,state.val.val.epsilon,state.val.val.field)) :
    ∃ weighted weightedForce weightedCofactor : StartupMoments 3,
      StartupWeightedRep parameters.sigma0 parameters.gamma 1 weighted.field
        (actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small source flat
          fields member sameSources allGrades 1) ∧
      let rows := nativeERRows weighted weightedForce weightedCofactor
        ((originalSourceMoments parameters (cartesianSourceVector source)).dilate startupOriginalUnitScale)
        (((originalSourceMoments parameters (source 3)).dilate startupOriginalUnitScale).smul (length : ℂ)⁻¹)
        (((originalSourceMoments parameters (source 2)).dilate startupOriginalUnitScale).smul ((1 : ℂ)/(length : ℂ)))
      ∃ rawRows : StartupNativeERRows, ∃ psi : StartupL2 1,
        StartupNativeERRowsRelated (physicalWeight parameters.sigma0 parameters.gamma 1) rows rawRows ∧
        StartupNativeWeakRows (1/length) psi rawRows ∧
        startupGenuineForceKernel (unitDiskAdmissible parameters) coefficient.data
          (coefficient.coherent radiusNonnegative) (coefficient.inverseCoherent radiusNonnegative)
          rows.circle.field=rows.forceCorrection.field ∧
        originalThirdCorrectionKernel (unitDiskAdmissible parameters) coefficient.data
          (coefficient.coherent radiusNonnegative) (coefficient.inverseCoherent radiusNonnegative)
          rows.circle.field=rows.thirdCorrection.field ∧
        startupGenuinePrincipalFluxKernel (unitDiskAdmissible parameters) coefficient.data
          (coefficient.coherent radiusNonnegative) (coefficient.inverseCoherent radiusNonnegative)
          rows.circle.field=rows.currentFlux.field ∧
        originalScalarFluxKernel (unitDiskAdmissible parameters) coefficient.data
          (coefficient.coherent radiusNonnegative) (coefficient.inverseCoherent radiusNonnegative)
          rows.circle.field=rows.scalarFlux.field := by
  have rhoSame : coefficient.rho=state.val.val.rho := congrArg OriginalUnitRankData.rho sameData
  have alphaSame : coefficient.val.alpha=state.val.val.alpha := congrArg OriginalUnitRankData.alpha sameData
  have deltaSame : coefficient.val.delta=state.val.val.delta := congrArg OriginalUnitRankData.delta sameData
  have parameterSame : coefficient.val.parameter=state.val.val.parameter := congrArg OriginalUnitRankData.parameter sameData
  have epsilonSame : coefficient.epsilon=state.val.val.epsilon := congrArg OriginalUnitRankData.epsilon sameData
  have fieldSame : coefficient.field=state.val.val.field := congrArg OriginalUnitRankData.field sameData
  let rawCertificate := actualNative_scaledERRows parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible
    M Mnonnegative stateBound vanishing nativeBound graded sameGrade constants estimate startupOriginalUnitScale
  let covariant := rawCertificate.choose
  let rawForceCertificate := rawCertificate.choose_spec
  let force := rawForceCertificate.choose
  let rawCofactorCertificate := rawForceCertificate.choose_spec
  let cofactor := rawCofactorCertificate.choose
  let xiCertificate := rawCofactorCertificate.choose_spec
  let xi := xiCertificate.choose
  have rawFacts := xiCertificate.choose_spec
  let weightedCertificate := actualNative_scaledMatrixRepresentatives parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible
    vanishing graded sameGrade constants estimate startupOriginalUnitScale
  let weighted := weightedCertificate.choose
  let weightedForceCertificate := weightedCertificate.choose_spec
  let weightedForce := weightedForceCertificate.choose
  let weightedCofactorCertificate := weightedForceCertificate.choose_spec
  let weightedCofactor := weightedCofactorCertificate.choose
  have weightedFacts := weightedCofactorCertificate.choose_spec
  have weightedSame := weightedFacts.1
  have weightedForceSame := weightedFacts.2.1
  have weightedCofactorSame := weightedFacts.2.2.1
  have covariantRep := weightedFacts.2.2.2.1
  have forceRep := weightedFacts.2.2.2.2.1
  have cofactorRep := weightedFacts.2.2.2.2.2.1
  have orbit := weightedFacts.2.2.2.2.2.2.1
  have forceContinuous := weightedFacts.2.2.2.2.2.2.2.1
  have cofactorContinuous := weightedFacts.2.2.2.2.2.2.2.2
  let knownForce := (originalSourceMoments parameters (cartesianSourceVector source)).dilate startupOriginalUnitScale
  let knownThird := ((originalSourceMoments parameters (source 3)).dilate startupOriginalUnitScale).smul (length : ℂ)⁻¹
  let determinant := ((originalSourceMoments parameters (source 2)).dilate startupOriginalUnitScale).smul ((1 : ℂ)/(length : ℂ))
  let rawKnownForce := (originalSourceRawMoments parameters (cartesianSourceVector source)).dilate startupOriginalUnitScale
  let rawKnownThird := ((originalSourceRawMoments parameters (source 3)).dilate startupOriginalUnitScale).smul (length : ℂ)⁻¹
  let rawDeterminant := ((originalSourceRawMoments parameters (source 2)).dilate startupOriginalUnitScale).smul ((1 : ℂ)/(length : ℂ))
  let rows := nativeERRows weighted weightedForce weightedCofactor knownForce knownThird determinant
  let rawRows := nativeERRows (covariant.dilate startupOriginalUnitScale) (force.dilate startupOriginalUnitScale)
    (cofactor.dilate startupOriginalUnitScale) rawKnownForce rawKnownThird rawDeterminant
  have phase : StartupNativeERRowsRelated (physicalWeight parameters.sigma0 parameters.gamma 1) rows rawRows := by
    apply nativeERRows_phase
    · intro cell first second same
      simp only [physicalWeight,same]
    · exact sameScaledNative_phase parameters startupOriginalUnitScale _ _ _ weightedSame rawFacts.1
    · exact sameScaledNative_phase parameters startupOriginalUnitScale _ _ _ weightedForceSame rawFacts.2.1
    · exact sameScaledNative_phase parameters startupOriginalUnitScale _ _ _ weightedCofactorSame rawFacts.2.2.1
    · exact originalKnownSource_scaledPhase parameters (cartesianSourceVector source) startupOriginalUnitScale
    · exact (originalKnownSource_scaledPhase parameters (source 3) startupOriginalUnitScale).smul (length : ℂ)⁻¹
    · exact (originalKnownSource_scaledPhase parameters (source 2) startupOriginalUnitScale).smul ((1 : ℂ)/(length : ℂ))
  have recovered := actualOriginalUnit_current_recovers parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible
    coefficient.data.gaugeDeviation (coefficient.coherent radiusNonnegative).2.2.2.1 (coefficient.inverseCoherent radiusNonnegative)
    (fun grade angle point => by simpa only [rhoSame,alphaSame,deltaSame,parameterSame,epsilonSame,fieldSame] using coefficient.gauge_matrix grade angle point)
    (originalUnitFour parameters length radius) (originalUnitFour_nonnegative parameters length radius)
    (by simpa only [rhoSame,epsilonSame,fieldSame] using
      (physicalBudget_monotone parameters coefficient.field coefficient.rho coefficient.epsilon (by norm_num : 6 ≤ 12)).trans coefficient.unit)
    (fun grade => by simpa only [rhoSame,epsilonSame,fieldSame] using (coefficient.rowBounds radiusNonnegative grade).1)
    (by simpa only [rhoSame,epsilonSame,fieldSame] using coefficient.determinantLow) weighted.field covariantRep
  have actions := OriginalUnitRankState.weighted_native_actions radiusNonnegative coefficient
    state.val.val.epsilon state.val.val.field epsilonSame fieldSame
    covariantRep orbit forceRep cofactorRep forceContinuous cofactorContinuous
  have operators := nativeERRows_actualFourOperators (unitDiskAdmissible parameters) coefficient.data
    (coefficient.coherent radiusNonnegative) (coefficient.inverseCoherent radiusNonnegative)
    weighted weightedForce weightedCofactor knownForce knownThird determinant recovered actions.1.1 actions.1.2 actions.2
  exact ⟨weighted,weightedForce,weightedCofactor,covariantRep,rawRows,
    ((startupOriginalUnitScale.val : ℂ)⁻¹ • startupMomentDilation startupOriginalUnitScale xi.field),
    phase,rawFacts.2.2.2.2,operators⟩

end Grad.ActualScaledNativeCoefficients
