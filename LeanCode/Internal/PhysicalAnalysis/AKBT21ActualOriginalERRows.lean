import AKBT20ScaledNativeWeakAssembly
import AKBN24ActualScaledAllWeakRows

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

/-- The SAME actual original solution supplies all eight rough ER rows,
with exact source normalization, before any unknown H1 hypothesis. -/
theorem actualNative_scaledERRows (scale : Scale) :
    ∃ covariant force cofactor : StartupMoments 3, ∃ xi : StartupMoments 1,
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, covariant.field point cell =
        actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point) ∧
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, force.field point cell =
        actualCartesianForceMatrixCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point) ∧
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, cofactor.field point cell =
        actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point) ∧
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, xi.field point cell =
        actualCartesianXiCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point) ∧
      StartupNativeWeakRows (scale.val/length) ((scale.val : ℂ)⁻¹ • startupMomentDilation scale xi.field)
        (nativeERRows (covariant.dilate scale) (force.dilate scale) (cofactor.dilate scale)
          ((originalSourceRawMoments parameters (cartesianSourceVector source)).dilate scale)
          (((originalSourceRawMoments parameters (source 3)).dilate scale).smul (length : ℂ)⁻¹)
          (((originalSourceRawMoments parameters (source 2)).dilate scale).smul ((scale.val : ℂ)/(length : ℂ)))) := by
  obtain ⟨covariant,xi,correction,thirdCorrection,cofactor,covariantSame,xiSame,correctionSame,thirdSame,cofactorSame,
    mean,forceEquation,thirdEquation,determinantEquation⟩ :=
    Grad.ActualCartesianWeakEquations.actualOriginalFamily_scaledWeakRows parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible
      M Mnonnegative stateBound vanishing nativeBound graded sameGrade constants estimate scale
  obtain ⟨weightedForce,weightedForceSame⟩ := actualCartesianForceMatrix_nativeMoments parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible
    vanishing graded sameGrade constants estimate
  let one : Scale := ⟨1,by norm_num⟩
  let force := weightedForce.unweight parameters one
  have forceSame := weightedForce.unweight_same parameters one
    (actualCartesianForceMatrixCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) weightedForceSame
  have planar := actualNative_forceCorrectionKernel parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible
    force.field correction.field forceSame correctionSame
  have third := actualNative_projectedThirdKernel_eq parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible
    force.field thirdCorrection.field forceSame thirdSame
  rw [planar] at forceEquation
  rw [third] at thirdEquation
  rw [←startupZeroMean_realDim 1] at determinantEquation
  exact ⟨covariant,force,cofactor,xi,covariantSame,forceSame,cofactorSame,xiSame,
    nativeERRows_scaledWeak scale length lengthPositive.ne' covariant force cofactor xi
      (originalSourceRawMoments parameters (source 3)) (originalSourceRawMoments parameters (source 2))
      (originalSourceRawMoments parameters (cartesianSourceVector source)) mean forceEquation thirdEquation determinantEquation⟩

end Grad.ActualScaledNativeCoefficients
