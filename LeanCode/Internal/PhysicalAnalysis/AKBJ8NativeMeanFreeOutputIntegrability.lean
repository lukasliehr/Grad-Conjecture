import AKBH10ActualSourceForceCorrection
import AKBJ7SameOriginalXiAxialCell

noncomputable section
set_option autoImplicit false
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
include vanishing sameGrade estimate

open Grad.AnnularSmoothCore Grad.ActualNativeCellMoments Grad.CartesianStartup Grad.ActualForceMoments

/-- Scalar angular mean removal acts on the completed native output before cell selection; its same unweighted cells are integrable. -/
theorem actualCartesianFamily_meanFreeOutputMoments
    (rows : ∀ index, DivisionRow 1 (originalExhaustionRadius length index))
    (curves : ∀ index, SmoothLowPhysicalRow parameters (originalExhaustionRadius length index)
      (originalExhaustionRadius_positive length lengthPositive index) (rows index))
    (coherent : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction 1 (originalExhaustionRadius length second) (originalExhaustionRadius length first)
        (originalExhaustionRadius_antitone length lengthPositive ordered) (rows second) = rows first)
    (C : ℝ) (Cnonnegative : 0 ≤ C)
    (coefficientBound : ∀ index radius, ‖(curves index).curve 2 radius‖ ≤ C *
      ‖(actualCartesianSevenCurves parameters length compact (originalExhaustionRadius length index)
        (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index)
        lengthPositive widthHalf widthLength state
        (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
        (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
        source flat (fields index) (member index) (sameSources index) (allGrades index)).curve 2 radius‖) :
    ∃ weighted unweighted : StartupMoments 1,
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
        weighted.field point cell = cartesianWeight parameters cell point • gluedCartesianCellField parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive) (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (originalExhaustionRadius_tendsto length) (fun index => meanFreeRow (originalExhaustionRadius length index) (rows index)) (fun index => (curves index).meanFree) cell point) ∧
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
        unweighted.field point cell = gluedCartesianCellField parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive) (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (originalExhaustionRadius_tendsto length) (fun index => meanFreeRow (originalExhaustionRadius length index) (rows index)) (fun index => (curves index).meanFree) cell point) ∧
      (∀ cell : ℤ, IntegrableOn (gluedCartesianCellField parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive) (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (originalExhaustionRadius_tendsto length) (fun index => meanFreeRow (originalExhaustionRadius length index) (rows index)) (fun index => (curves index).meanFree) cell) openUnitDisk) := by
  have meanCoherent : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction 1 (originalExhaustionRadius length second) (originalExhaustionRadius length first)
        (originalExhaustionRadius_antitone length lengthPositive ordered)
        (meanFreeRow (originalExhaustionRadius length second) (rows second)) =
      meanFreeRow (originalExhaustionRadius length first) (rows first) := by
    intro first second ordered
    rw [originalBulkRestriction_meanFree,coherent first second ordered]
  obtain ⟨weighted,weightedSame⟩ := actualCartesianFamily_outputMoments parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades
    vanishing graded sameGrade constants estimate
    (fun index => meanFreeRow (originalExhaustionRadius length index) (rows index))
    (fun index => (curves index).meanFree) meanCoherent (‖hilbertMeanFree parameters‖*C)
    (mul_nonneg (norm_nonneg _) Cnonnegative) (fun index radius => by
      change ‖hilbertMeanFree parameters ((curves index).curve 2 radius)‖ ≤ _
      exact ((hilbertMeanFree parameters).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_left (coefficientBound index radius) (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm))
  let scale : Grad.SpatialDilation.Scale := ⟨1,by constructor <;> norm_num⟩
  let unweighted := weighted.unweight parameters scale
  have unweightedSame := weighted.unweight_same parameters scale
    (fun cell point => gluedCartesianCellField parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive) (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (originalExhaustionRadius_tendsto length) (fun index => meanFreeRow (originalExhaustionRadius length index) (rows index)) (fun index => (curves index).meanFree) cell point) weightedSame
  exact ⟨weighted,unweighted,weightedSame,unweightedSame,
    fun cell => startupRaw_cell_integrable unweighted.field _ unweightedSame cell⟩

end Grad.ActualScalarWeakEquations
