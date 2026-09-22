import AKBH5ActualFullForceNativeMoments
import AKBH6LiteralForceNormalization

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace Grad.ActualForceMoments
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

open Grad.CartesianStartup Grad.PDEBootstrap

/-- The literal planar two-force and negative third-force normalization. -/
def actualCartesianForceCorrectionCell (cell : ℤ) (point : Spatial) : ComplexEuclidean 3 :=
  forceCorrectionMap length (actualCartesianForceMatrixCell parameters length compact lengthPositive widthHalf widthLength state small
    source flat fields member sameSources allGrades cell point)

/-- Native all-grade energy supplies BOTH the original-width conjugated
force corrections and the SAME unweighted corrections, hence every-cell L1. -/
theorem actualCartesianForceCorrection_nativeMoments :
    ∃ weighted unweighted : StartupMoments 3,
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
        weighted.field point cell = cartesianWeight parameters cell point •
          actualCartesianForceCorrectionCell parameters length compact lengthPositive widthHalf widthLength state small
            source flat fields member sameSources allGrades cell point) ∧
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
        unweighted.field point cell = actualCartesianForceCorrectionCell parameters length compact lengthPositive widthHalf widthLength state small
          source flat fields member sameSources allGrades cell point) ∧
      (∀ cell : ℤ, IntegrableOn
        (actualCartesianForceCorrectionCell parameters length compact lengthPositive widthHalf widthLength state small
          source flat fields member sameSources allGrades cell) openUnitDisk) := by
  obtain ⟨matrixFamily,matrixSame⟩ := actualCartesianForceMatrix_nativeMoments parameters length compact lengthPositive
    widthHalf widthLength state small source flat fields member sameSources allGrades compatible vanishing graded sameGrade constants estimate
  let mapping := forceCorrectionMap length
  let weighted := matrixFamily.map (originalValueKernel mapping) (originalValueKernel_cellwise mapping)
  have weightedSame : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      weighted.field point cell = cartesianWeight parameters cell point •
        actualCartesianForceCorrectionCell parameters length compact lengthPositive widthHalf widthLength state small
          source flat fields member sameSources allGrades cell point := by
    have mapped := startupValueMap_same matrixFamily mapping
      (fun cell point => cartesianWeight parameters cell point • actualCartesianForceMatrixCell parameters length compact lengthPositive
        widthHalf widthLength state small source flat fields member sameSources allGrades cell point) matrixSame
    filter_upwards [mapped] with point same
    intro cell
    exact (same cell).trans ((mapping.restrictScalars ℝ).map_smul _ _)
  let scale : Grad.SpatialDilation.Scale := ⟨1,by constructor <;> norm_num⟩
  let unweighted := weighted.unweight parameters scale
  have unweightedSame := weighted.unweight_same parameters scale
    (actualCartesianForceCorrectionCell parameters length compact lengthPositive widthHalf widthLength state small
      source flat fields member sameSources allGrades) weightedSame
  exact ⟨weighted,unweighted,weightedSame,unweightedSame,
    fun cell => startupRaw_cell_integrable unweighted.field _ unweightedSame cell⟩

end Grad.ActualForceMoments
