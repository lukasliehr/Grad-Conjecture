import AKBN4ScaledProjectedForceEquation
import AKBN6ScaledDeterminantEquation
import AKBN22ActualNativeAllWeakRows
import AKBN20ActualDeterminantBalance
import AKBN21ActualNativeThirdL2
import AKBN12OriginalNativeRawFields
import AKBK24ActualOriginalPlanarWeakEquation

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace Grad.ActualCartesianWeakEquations
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
/-- The actual original solution obeys the same three rough equations on
any admissible smaller disk, with psi=Xi(ell Y)/ell and axial symbol i*n*ell/L.
All integer cells and the original analytic width are retained. -/
theorem actualOriginalFamily_scaledWeakRows (scale : Scale) :
    ∃ covariant : StartupMoments 3, ∃ xi : StartupMoments 1, ∃ correction : StartupMoments 3,
    ∃ thirdCorrection : StartupMoments 1, ∃ cofactor : StartupMoments 3,
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, covariant.field point cell =
        actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point) ∧
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, xi.field point cell =
        actualCartesianXiCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point) ∧
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, correction.field point cell =
        actualCartesianForceCorrectionCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point) ∧
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, thirdCorrection.field point cell =
        actualCartesianProjectedThirdForceCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point) ∧
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, cofactor.field point cell =
        actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point) ∧
      (∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test)
        ((scale.val : ℂ)⁻¹ • startupMomentDilation scale xi.field) = 0) ∧
      StartupWeakProjectedForceEquation ((scale.val : ℂ)⁻¹ • startupMomentDilation scale xi.field)
        (startupMomentDilation scale (originalValueKernel planarPartMap covariant.field))
        (startupMomentDilation scale (startupGenuineQradKernel
          ((originalSourceRawMoments parameters (cartesianSourceVector source)).field -
            originalValueKernel planarPartMap correction.field))) ∧
      StartupWeakThirdEquation (fun cell => (scale.val : ℂ) * ((Complex.I * (cell : ℂ)) / (length : ℂ)))
        ((scale.val : ℂ)⁻¹ • startupMomentDilation scale (startupTrueAngularInverse 1 0 xi.field))
        (startupMomentDilation scale (originalValueKernel toroidalPartMap covariant.field))
        (startupMomentDilation scale ((length : ℂ)⁻¹ •
          ((originalSourceRawMoments parameters (source 3)).field - thirdCorrection.field))) ∧
      StartupWeakDeterminantEquation (fun cell => (scale.val : ℂ) * ((Complex.I * (cell : ℂ)) / (length : ℂ)))
        (startupMomentDilation scale (originalValueKernel planarPartMap covariant.field))
        (startupMomentDilation scale (originalValueKernel toroidalPartMap covariant.field))
        ((scale.val : ℂ) • startupMomentDilation scale ((length : ℂ)⁻¹ • (originalSourceRawMoments parameters (source 2)).field))
        (startupMomentDilation scale ((originalValueKernel planarPartMap cofactor.field + originalValueKernel planarPartMap covariant.field) -
          originalAverageKernel (originalValueKernel planarPartMap cofactor.field + originalValueKernel planarPartMap covariant.field)))
        (startupMomentDilation scale ((originalValueKernel toroidalPartMap cofactor.field + originalValueKernel toroidalPartMap covariant.field) -
          startupRealAngularKernelDim 1 (fun _ => 1) contDiff_const
            (originalValueKernel toroidalPartMap cofactor.field + originalValueKernel toroidalPartMap covariant.field))) := by
  obtain ⟨covariant,xi,correction,thirdCorrection,cofactor,covariantSame,xiSame,correctionSame,
    thirdSame,cofactorSame,mean,forceEquation,thirdEquation,determinantEquation⟩ :=
    actualOriginalFamily_allWeakRows parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible M Mnonnegative stateBound vanishing nativeBound
      graded sameGrade constants estimate
  refine ⟨covariant,xi,correction,thirdCorrection,cofactor,covariantSame,xiSame,correctionSame,
    thirdSame,cofactorSame,?_,?_,?_,?_⟩
  · intro cell test
    rw [map_smul,startupCoordinateTestPairing_dilation,startupPulledTest_mean,mean,smul_zero,smul_zero]
  · exact startupProjectedForceEquation_dilation scale _ _ _ forceEquation
  · exact startupThirdEquation_dilation scale _ _ _ _ thirdEquation
  · exact startupDeterminantEquation_dilation scale _ _ _ _ _ _ determinantEquation

end Grad.ActualCartesianWeakEquations
