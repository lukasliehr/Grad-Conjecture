import AKBK21ActualClosedProjectedForceEquation
import AKBK22ActualForceCorrectionIntegrability
import AKBK23NativeProjectedForceThroughAxis

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

/-- The genuine compatible observed solution satisfies the original planar
projected force equation on the entire disk, in every axial Fourier cell.
All differential identities, source fidelity and axis integrability are proved. -/
theorem actualOriginalPlanarForce_weak (cell : ℤ) :
    ∀ output (test : Spatial → ℝ), ContDiff ℝ ∞ test → HasCompactSupport test → tsupport test ⊆ openUnitDisk →
      (∑ coordinate : Fin 2, ∫ point in openUnitDisk,
        startupRawQradTest output test coordinate point • nativePlanarForceSource
          (originalCoreCell parameters (cartesianSourceVector source) cell)
          (actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell)
          (actualCartesianForceCorrectionCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) point coordinate) =
      -(∑ coordinate : Fin 2, ∑ direction : Fin 2, ∫ point in openUnitDisk,
        fderiv ℝ (startupRawQradTest output test coordinate) point (spatialDirection direction) •
          nativePlanarForceFlux (actualCartesianXiCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell)
            (actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) coordinate direction point) := by
  have smooth := actualCartesianForceCells_smooth parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell
  have xi := actualCartesianXiCell_integrable_pair parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades M stateBound vanishing nativeBound compatible cell
  have covariant := actualCartesianCovariantCell_integrable_pair parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades M Mnonnegative stateBound vanishing nativeBound compatible cell
  have correction := actualCartesianForceCorrection_integrable_pair parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible M Mnonnegative stateBound vanishing nativeBound cell
  exact nativePlanarForce_weak
    (actualCartesianXiCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell)
    (actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell)
    (actualCartesianForceCorrectionCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell)
    (originalCoreCell parameters (cartesianSourceVector source) cell)
    smooth.1 smooth.2.1 smooth.2.2.continuousOn
    (originalCoreCell_smooth parameters (cartesianSourceVector source) cell).continuous.continuousOn
    xi.1 xi.2 covariant.1 covariant.2 correction.1
    (originalCoreCell_integrable parameters (cartesianSourceVector source) cell)
    (actualCartesianPlanarForce_projectedFlux parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell)

end Grad.ActualCartesianWeakEquations
