import AKBN19RawDeterminantBalance
import AKBJ34ActualOriginalDeterminantWeakThroughAxis
import AKBJ33ActualCartesianDeterminantMean

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
include compatible vanishing

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


open Grad.CartesianStartup Grad.GaugeCoefficients.Physical.RadialLedger Grad.Constraints.Gauges
open Grad.ActualOriginalSourceMoments Grad.RepresentedKernel.SpatialProduct Grad.WeightedJets
/-- The actual original cofactor through-axis law on its SAME joint moment
carrier, with the original determinant source divided by L. -/
theorem actualOriginalFamily_determinantBalance (cofactor : StartupMoments 3)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      cofactor.field point cell = actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point) :
    ∀ cell test, startupCoordinateTestPairing cell 0 test
      ((length : ℂ)⁻¹ • (originalSourceRawMoments parameters (source 2)).field) =
      startupWeakDivergencePairing (originalValueKernel planarPartMap cofactor.field) cell (startupMeanFreeTest test) +
        ((Complex.I * (cell : ℂ)) / (length : ℂ)) * startupCoordinateTestPairing cell 0 (startupMeanFreeTest test)
          (originalValueKernel toroidalPartMap cofactor.field) := by
  apply startupDeterminantBalance_of_raw length lengthPositive.ne' (fun cell => Complex.I * (cell : ℂ))
    cofactor (originalSourceRawMoments parameters (source 2)).field
    (actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) (originalCoreCell parameters (source 2)) same
    (fun cell => (originalSourceRawMoments_same parameters (source 2)).mono (fun _ same => same cell))
  intro cell test
  have weak := actualOriginalDeterminant_weak parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible vanishing M Mnonnegative stateBound nativeBound
    cell test.toFun test.smooth test.compact test.supported
  have flux (direction : Fin 2) (point : Spatial) :
      determinantPlanarCellFlux length (actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) direction point =
        (length : ℂ) * actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point direction.castSucc := by
    fin_cases direction <;> rfl
  have testSame : scalarP0Test test.toFun = (startupMeanFreeTest test).toFun := rfl
  rw [testSame] at weak
  simpa only [flux,determinantAxialCellFlux,directionDerivative] using weak

end Grad.ActualScalarWeakEquations
