import AKBT10SameWeightedNativeLedgerActions
import AKBN16ActualCofactorNativeMoments
import AKBT1NativeScaledWeightedRepresentative
import AKBN13ActualNativeForceL2
import AKBJ9ActualProjectedThirdForceIntegrability

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
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


open Grad.ActualCartesianDescent Grad.ClosedJets Grad.DiskExtension.Operator Grad.BoundaryTrace Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.PuncturedRetainedEnergy
variable (compatible : ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)

variable (vanishing : SourceHigherVanishing source)
    (graded : ∀ index (_grade : ℕ), CoupledSpace (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index) lengthPositive)
    (sameGrade : ∀ index grade, CoupledInsertedGrade (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index) lengthPositive grade
      (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length
        (originalExhaustionRadius_positive length lengthPositive index)
        ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index)) (graded index grade))
    (constants : ℕ → ℝ) (estimate : ∀ index grade, ‖graded index grade‖ ≤ constants grade)
include compatible vanishing sameGrade estimate

open Grad.ActualCartesianFlux

open Grad.ActualNativeCellMoments Grad.ActualCurrentPrimitives

open Grad.ActualForceMoments Grad.CartesianStartup Grad.BoundaryLift Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger


open Grad.SpatialDilation Grad.ActualCartesianWeakEquations
open Grad.ActualScalarWeakEquations
/-- All actual scaled native covariant/force/cofactor moments and full-family
representations, supplied by the original solution before H1 regularity. -/
theorem actualNative_scaledMatrixRepresentatives (scale : Scale) :
    ∃ covariant force cofactor : StartupMoments 3,
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
        covariant.field point cell = Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma scale.val cell point •
          actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell (scale.val • point)) ∧
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
        force.field point cell = Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma scale.val cell point •
          actualCartesianForceMatrixCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell (scale.val • point)) ∧
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
        cofactor.field point cell = Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma scale.val cell point •
          actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell (scale.val • point)) ∧
      StartupWeightedRep parameters.sigma0 parameters.gamma scale.val covariant.field (actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades scale.val) ∧
      StartupWeightedRep parameters.sigma0 parameters.gamma scale.val force.field
        (nativeScaledMatrixRaw scale.val (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field) (actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades scale.val)) ∧
      StartupWeightedRep parameters.sigma0 parameters.gamma scale.val cofactor.field
        (nativeScaledMatrixRaw scale.val (originalCofactorFamily parameters length state.val.val.epsilon state.val.val.field) (actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades scale.val)) ∧
      StartupOrbitContinuous (actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades scale.val) ∧
      (∀ᵐ point ∂volume.restrict openUnitDisk, Continuous (fun angle => nativeScaledMatrixRaw scale.val (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field) (actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades scale.val) (angle,point))) ∧
      (∀ᵐ point ∂volume.restrict openUnitDisk, Continuous (fun angle => nativeScaledMatrixRaw scale.val (originalCofactorFamily parameters length state.val.val.epsilon state.val.val.field) (actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades scale.val) (angle,point))) := by
  obtain ⟨covariant,covariantSame,covariantRep,regular⟩ := actualNative_scaledWeightedCovariant parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible vanishing graded sameGrade constants estimate scale
  obtain ⟨force,forceSame⟩ := actualCartesianForceMatrix_nativeMoments parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible vanishing graded sameGrade constants estimate
  obtain ⟨cofactor,_raw,cofactorSame,_rawSame⟩ := actualCartesianCofactor_nativeMoments parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible vanishing graded sameGrade constants estimate
  let rows := fun index => cartesianCovariantRow (originalExhaustionRadius length index)
    (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index)
  let curves := fun index => (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).cartesianCovariant
  have rowCompatible := cartesianCovariantRows_compatible (originalExhaustionRadius length) (originalExhaustionRadius_antitone length lengthPositive)
    (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields)
    (fun first second ordered => (cartesianSourcePolarAndXi_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).1)
  have low := originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small
  have forceCoherent := forceMatrixFamily_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field low
  have cofactorCoherent := (originalCofactorFamily_estimate parameters length state.val.val.rho state.val.val.epsilon state.val.val.field low).actualCoherent
  refine ⟨covariant,force.dilate scale,cofactor.dilate scale,covariantSame,?_,?_,covariantRep,?_,?_,regular,?_,?_⟩
  · exact startupMomentDilation_weighted_same parameters.sigma0 parameters.gamma scale _ force.field forceSame
  · exact startupMomentDilation_weighted_same parameters.sigma0 parameters.gamma scale _ cofactor.field cofactorSame
  · exact nativeMatrix_scaledWeightedRep parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive) (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive) rows curves rowCompatible (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field) forceCoherent scale force forceSame
  · exact nativeMatrix_scaledWeightedRep parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive) (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive) rows curves rowCompatible (originalCofactorFamily parameters length state.val.val.epsilon state.val.val.field) cofactorCoherent scale cofactor cofactorSame
  · exact nativeScaledMatrix_axial_continuous parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive) (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive) rows curves rowCompatible (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field) scale
  · exact nativeScaledMatrix_axial_continuous parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive) (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive) rows curves rowCompatible (originalCofactorFamily parameters length state.val.val.epsilon state.val.val.field) scale

end Grad.ActualScaledNativeCoefficients
