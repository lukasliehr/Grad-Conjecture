import AKBN17ActualThirdScalarCoordinate
import AKBN18ActualXiRoughMean
import AKBN15ScalarWeakCoordinate
import AKBJ17ActualThirdWeakThroughAxis

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace Grad.ActualScalarWeakEquations
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

open Grad.ActualCartesianWeakEquations Grad.PDEBootstrap Grad.PhysicalFamily
variable (M : ℝ) (Mnonnegative : 0 ≤ M)
    (stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ M)
    (nativeBound : ∀ index, originalWeightedRetainedNorm parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index).ofLp.1 ≤
        2 * independentCoupledDataConstant parameters length compact *
          (originalSourceAllocationConstant parameters length 0 * (1 + M) * ‖quotientEta parameters 8 source‖))

include Mnonnegative stateBound nativeBound

open Grad.WeightedJets
open Grad.CartesianStartup Grad.RepresentedKernel.SpatialProduct Grad.GenericCarriers Grad.GaugeCoefficients.Physical.Ledger

open Grad.GaugeCoefficients.Physical.RadialLedger Grad.Constraints.Gauges
open Grad.ActualOriginalSourceMoments Grad.ActualForceMoments
/-- The actual native scalar equation in joint L2, with both the original
projected correction and Xi mean derived from the constructed solution. -/
theorem actualOriginalFamily_thirdL2 (covariant : StartupMoments 3) (xi : StartupMoments 1)
    (covariantSame : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      covariant.field point cell = actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point)
    (xiSame : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      xi.field point cell = actualCartesianXiCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point) :
    ∃ correction : StartupMoments 1,
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, correction.field point cell =
        actualCartesianProjectedThirdForceCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point) ∧
      StartupWeakThirdEquation (fun cell => (Complex.I * (cell : ℂ)) / (length : ℂ))
        (startupTrueAngularInverse 1 0 xi.field) (originalValueKernel toroidalPartMap covariant.field)
        ((length : ℂ)⁻¹ • ((originalSourceRawMoments parameters (source 3)).field - correction.field)) := by
  obtain ⟨_weighted,correction,_weightedSame,correctionSame⟩ :=
    actualCartesianProjectedThirdForce_nativeMoments parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible vanishing graded sameGrade constants estimate
  refine ⟨correction,correctionSame,?_⟩
  have scalarSame := startupValueMap_same covariant toroidalPartMap _ covariantSame
  apply startupThirdEquation_of_raw length lengthPositive.ne' (fun cell => Complex.I * (cell : ℂ))
    xi.field (originalValueKernel toroidalPartMap covariant.field)
    (originalSourceRawMoments parameters (source 3)).field correction.field
    (actualCartesianXiCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades)
    (fun cell point => toroidalPartMap (actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point))
    (originalCoreCell parameters (source 3)) (actualCartesianProjectedThirdForceCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades)
    (fun cell => xiSame.mono (fun _ same => same cell))
    (fun cell => scalarSame.mono (fun _ same => same cell))
    (fun cell => (originalSourceRawMoments_same parameters (source 3)).mono (fun _ same => same cell))
    (fun cell => correctionSame.mono (fun _ same => same cell))
    (actualXi_roughWeakMean parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible xi.field xiSame)
  intro cell test
  exact actualOriginalThird_rawScalar parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible vanishing graded sameGrade constants estimate
    M Mnonnegative stateBound nativeBound cell test

end Grad.ActualScalarWeakEquations
