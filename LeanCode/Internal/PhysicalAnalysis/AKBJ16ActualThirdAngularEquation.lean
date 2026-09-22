import AKBJ14ActualOriginalThirdCell
import AKBJ15ThirdAngularFlux

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
open Grad.AnnularGeneralSourceRegularity Grad.ActualSmoothPhysicalField Grad.PuncturedRetainedEnergy
variable (compatible : ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)

open Grad.PDEBootstrap Grad.PhysicalFamily Grad.ActualCartesianFlux Grad.ActualCartesianWeakEquations
include compatible

theorem sameCovariantCell_punctured_smooth (cell : ℤ) :
    ContDiffOn ℝ ∞ (actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) (openUnitDisk \ {(0 : Spatial)}) := by
  intro point inside
  exact (gluedCartesianCellField_smoothAt parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive) (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive) (fun index => cartesianCovariantRow (originalExhaustionRadius length index) (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index)) (fun index => (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).cartesianCovariant) (cartesianCovariantRows_compatible (originalExhaustionRadius length) (originalExhaustionRadius_antitone length lengthPositive) (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (fun first second ordered => (cartesianSourcePolarAndXi_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).1)) cell point
    (by simpa only [mem_singleton_iff] using inside.2) inside.1).contDiffWithinAt

/-- Genuine original third equation as an angular transport law at every punctured Cartesian point. -/
theorem actualOriginalThird_rotation (cell : ℤ) (point : Spatial) (inside : point ∈ openUnitDisk \ {(0 : Spatial)}) :
    (Complex.I * (cell : ℂ)) • actualCartesianXiCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point -
      actualCartesianProjectedThirdForceCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point + originalCoreCell parameters (source 3) cell point =
      fderiv ℝ (thirdRotationField length (actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell)) point (planeQuarterTurn point) := by
  have nonzero : point ≠ 0 := by simpa only [mem_singleton_iff] using inside.2
  have positive : 0 < ‖point‖ := norm_pos_iff.mpr nonzero
  let closed : ClosedDisk := ⟨point,by change ‖point‖ ≤ 1; exact inside.1.le⟩
  obtain ⟨polar,coordinates⟩ := Grad.Constraints.closedPoint_has_polar_angle closed
  have represented : polarPlane (‖point‖,polar) = point := by
    have values := congrArg Subtype.val coordinates
    rw [Grad.Constraints.polarClosedPoint_coordinates] at values
    simpa only [polarPlane,Grad.BoundaryTrace.collarPlane,closed,sub_sub_cancel] using values
  let index := selectedInnerCollar (originalExhaustionRadius length) (originalExhaustionRadius_tendsto length) ‖point‖ positive
  have radiusInside : ‖point‖ ∈ Ioo (originalExhaustionRadius length index) 1 :=
    ⟨selectedInnerCollar_lt (originalExhaustionRadius length) (originalExhaustionRadius_tendsto length) ‖point‖ positive,inside.1⟩
  have third := actualOriginalThird_cell_polar parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell index ‖point‖ radiusInside polar
  rw [← quarterTurn_polarPlane,represented] at third
  have differentiable := ((sameCovariantCell_punctured_smooth parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell).contDiffAt
    ((openUnitDisk_isOpen.sdiff isClosed_singleton).mem_nhds inside)).differentiableAt (by simp)
  rw [thirdRotationField_fderiv length _ point _ differentiable,← third]
  unfold thirdRowValue
  abel

end Grad.ActualScalarWeakEquations
