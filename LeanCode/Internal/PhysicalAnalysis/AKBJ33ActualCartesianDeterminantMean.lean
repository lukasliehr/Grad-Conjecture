import AKBJ32NormalizedDeterminantCellFlux
import AKBJ30ActualDeterminantCellDerivative
import AKBJ28DeterminantFourierAlgebra
import AKBJ26CompletedCofactorCartesianFidelity
import AKBK2SameLocalCellDerivatives

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

open Grad.ActualCartesianFlux

open Grad.ActualNativeCellMoments Grad.ActualCurrentPrimitives

open Grad.ActualForceMoments Grad.CartesianStartup Grad.BoundaryLift Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger

open Grad.ActualDeterminantEquations Grad.ActualCartesianWeakEquations Grad.PDEBootstrap Grad.PhysicalFamily
open Grad.GaugeCoefficients.Physical.RadialLedger
include compatible

/-- The original scalar determinant equation on every punctured Cartesian point, with the literal P0 and L,L,1 cofactor fluxes consumed by axis removal. -/
theorem actualOriginalDeterminant_cartesianMean (cell : ℤ) (point : ClosedDisk)
    (positive : 0 < ‖point.val‖) (inside : ‖point.val‖ < 1) :
    originalCoreCell parameters (source 2) cell point.val 0 =
      scalarDivergenceValue (determinantPlanarCellFlux length (actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell)) (determinantAxialCellFlux cell (actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell)) point.val 0 -
        closedAngularMean (fun closed : ClosedDisk =>
          scalarDivergenceValue (determinantPlanarCellFlux length (actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell)) (determinantAxialCellFlux cell (actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell)) closed.val) point 0 := by
  let field := (actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell)
  let raw := scalarDivergenceValue (determinantPlanarCellFlux length field) (determinantAxialCellFlux cell field)
  have smoothField := actualCofactorCell_smooth parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell
  have rawContinuous : ContinuousOn raw (openUnitDisk \ {(0 : Spatial)}) :=
    determinantCellFlux_rawContinuous length cell field smoothField
  have bounded : |‖point.val‖| ≤ 1 := by
    simpa only [abs_of_nonneg (norm_nonneg _)] using (show ‖point.val‖ ≤ 1 from point.property)
  obtain ⟨angle,polar⟩ := Grad.Constraints.closedPoint_has_polar_angle point
  have represented (theta : ℝ) : (Grad.Constraints.polarClosedPoint ‖point.val‖ bounded theta).val = polarPlane (‖point.val‖,theta) := by
    rw [Grad.Constraints.polarClosedPoint_coordinates]
    simp only [polarPlane,Grad.BoundaryTrace.collarPlane,sub_sub_cancel]
  have current : polarPlane (‖point.val‖,angle) = point.val := by
    rw [← represented angle]
    exact congrArg Subtype.val polar
  have circleInside (theta : ℝ) : polarPlane (‖point.val‖,theta) ∈ openUnitDisk \ {(0 : Spatial)} := by
    constructor
    · change ‖polarPlane (‖point.val‖,theta)‖ < 1
      simpa only [polarPlane_norm,abs_of_nonneg (norm_nonneg _)] using inside
    · have normPositive : 0 < ‖polarPlane (‖point.val‖,theta)‖ := by
        simpa only [polarPlane_norm,abs_of_nonneg (norm_nonneg _)] using positive
      simpa only [mem_singleton_iff] using (norm_pos_iff.mp normPositive)
  have circleContinuous : Continuous (fun theta => raw (polarPlane (‖point.val‖,theta))) :=
    rawContinuous.comp_continuous (polarPlane_smooth.continuous.comp (continuous_const.prodMk continuous_id)) circleInside
  have rawSame (theta : ℝ) : raw (polarPlane (‖point.val‖,theta)) 0 =
      sameCellDeterminantDivergence length cell field (polarPlane (‖point.val‖,theta)) :=
    determinantCellFlux_divergence length cell field _
      ((smoothField.contDiffAt ((openUnitDisk_isOpen.sdiff isClosed_singleton).mem_nhds (circleInside theta))).differentiableAt (by simp))
  have mean := scalarMean_polar (fun closed : ClosedDisk => raw closed.val) ‖point.val‖ bounded angle
  rw [polar] at mean
  have circleSame : (fun theta => raw (Grad.Constraints.polarClosedPoint ‖point.val‖ bounded theta).val) =
      fun theta => raw (polarPlane (‖point.val‖,theta)) := funext (fun theta => congrArg raw (represented theta))
  rw [circleSame] at mean
  have meanScalar := (congrArg (fun value : ComplexEuclidean 1 => value 0) mean).trans
    (angularCoefficient_component (fun theta => raw (polarPlane (‖point.val‖,theta))) circleContinuous 0 0)
  simp_rw [rawSame] at meanScalar
  let index := selectedInnerCollar (originalExhaustionRadius length) (originalExhaustionRadius_tendsto length) ‖point.val‖ positive
  have collarInside : ‖point.val‖ ∈ Ioo (originalExhaustionRadius length index) 1 :=
    ⟨selectedInnerCollar_lt _ _ _ positive,inside⟩
  have equation := actualOriginalDeterminant_cell_polar parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell index ‖point.val‖ collarInside angle
  change sameCellDeterminantDivergence length cell field (polarPlane (‖point.val‖,angle)) -
    angularCoefficient (fun theta => sameCellDeterminantDivergence length cell field (polarPlane (‖point.val‖,theta))) 0 = _ at equation
  have atCurrent := rawSame angle
  rw [current] at equation atCurrent
  change originalCoreCell parameters (source 2) cell point.val 0 = raw point.val 0 -
    closedAngularMean (fun closed : ClosedDisk => raw closed.val) point 0
  rw [atCurrent,meanScalar]
  exact equation.symm

end Grad.ActualScalarWeakEquations
