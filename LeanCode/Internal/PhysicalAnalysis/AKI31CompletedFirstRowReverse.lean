import AKI30ArbitraryHighStoredFirstRow
import AKG26OriginalFullPhysicalEquationConverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularKernelL2 Grad.AnnularKernelContinuity Grad.AnnularReconstruction
open Grad.AnnularPhysicalSolution Grad.AnnularStrongSolution Grad.BoundaryKernelAction
open Grad.GaugeCoefficients.Physical.Ledger Grad.AnnularCurrentLow Grad.ActualBoundaryPrimitives Grad.AnnularCurrentSource Grad.AnnularCurrentEnergy

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact)

/-- The retained operator is the actual projected first row on the independent
high X slot, including the original retained normalization. -/
theorem completedFirstRow_injected (x : DivisionRow 1 lower)
    (high : highRowProjection lower x = x) :
    highRowProjection lower (lowPhysicalRowAction parameters length compact lower positive bounded state 0
      (bulkMatrixUnit lower (0 : Fin 7) (0 : Fin 1) x)) =
      retainedAAction parameters 0 lower positive bounded length compact state x := by
  let row := radialNormalizedRetainedFirstRowKernel_regular parameters length compact state.val
  let injection := constantMatrixRadialKernel_regular parameters 1 7 (matrixUnit 0 0)
  let projection : RegularKernelFamily (fun radius => highAngularKernel (radialKernelParameters parameters radius) 1) :=
    scalarModeRadialKernel_regular parameters 1 highAngularMultiplier 1 highAngularMultiplier_norm_le
  have split := regularRadialBulkAction_comp parameters 0 lower positive bounded _ _ row (injection.comp projection)
  rw [regularRadialBulkAction_comp parameters 0 lower positive bounded _ _ injection projection,
    regularMatrixUnit_eq_bulk, completedProjectedFirstRow parameters length compact lower positive bounded state] at split
  have projectionSame := completedHighProjection_same parameters 0 lower positive bounded
  change regularRadialBulkAction parameters 0 lower positive bounded
    (fun radius => highAngularKernel (radialKernelParameters parameters radius) 1) projection = _ at projectionSame
  rw [projectionSame] at split
  have applied := congrArg (fun action : DivisionRow 1 lower →L[ℂ] DivisionRow 1 lower => action x) split
  change retainedAAction parameters 0 lower positive bounded length compact state x =
    highRowProjection lower (lowPhysicalRowAction parameters length compact lower positive bounded state 0
      (bulkMatrixUnit lower (0 : Fin 7) (0 : Fin 1) (highRowProjection lower x))) at applied
  exact (applied.trans (congrArg (fun y : DivisionRow 1 lower => highRowProjection lower
    (lowPhysicalRowAction parameters length compact lower positive bounded state 0
      (bulkMatrixUnit lower (0 : Fin 7) (0 : Fin 1) y))) high)).symm

/-- Exact additive assembly of the actual first row, before solving it. -/
theorem completedAssembledFirstRow (x : DivisionRow 1 lower) (input : DivisionRow 8 lower)
    (high : highRowProjection lower x = x) :
    highRowProjection lower (lowPhysicalRowAction parameters length compact lower positive bounded state 0
      (assembledSevenBulk parameters lower positive bounded 0 x input)) =
      retainedAAction parameters 0 lower positive bounded length compact state x +
      highRowProjection lower (lowPhysicalRowAction parameters length compact lower positive bounded state 0
        (knownSevenBulkAction parameters lower positive bounded 0 input)) := by
  rw [assembledSevenBulk,map_add,map_add,completedFirstRow_injected parameters length compact lower positive bounded state x high]

/-- The literal completed first row implies the SAME retained inverse
elimination; no solution equation is assumed in this reverse direction. -/
theorem eliminatedX_of_assembledFirstRow (x : DivisionRow 1 lower) (input : DivisionRow 8 lower)
    (high : ∀ mode : ℤ × ℤ, |mode.1| < 3 → x mode = 0)
    (first : highRowProjection lower (lowPhysicalRowAction parameters length compact lower positive bounded state 0
      (assembledSevenBulk parameters lower positive bounded 0 x input)) +
      highRowProjection lower (bulkMatrixUnit lower (0 : Fin 1) (7 : Fin 8) input) =
      highRowProjection lower (bulkMatrixUnit lower (0 : Fin 1) (0 : Fin 8) input)) :
    x = eliminatedXAction parameters length compact lower positive bounded state 0 input := by
  have highFixed : highRowProjection lower x = x :=
    (highRowProjection_fixed_iff lower x).mpr (fun mode outside => high mode (lt_of_not_ge outside))
  have solvedHigh : highRowProjection lower
      (eliminatedXAction parameters length compact lower positive bounded state 0 input) =
      eliminatedXAction parameters length compact lower positive bounded state 0 input := by
    apply (highRowProjection_fixed_iff lower _).mpr
    intro mode outside
    rw [eliminatedXAction_eq_inverse]
    exact retainedInverseAction_high parameters 0 lower positive bounded length compact state _ mode (lt_of_not_ge outside)
  have solved := completedEliminatedSeven_firstRow parameters length compact lower positive bounded state input
  rw [eliminatedSevenBulkAction_assembled,
    completedAssembledFirstRow parameters length compact lower positive bounded state _ input solvedHigh] at solved
  rw [completedAssembledFirstRow parameters length compact lower positive bounded state x input highFixed] at first
  have same := add_right_cancel (add_right_cancel (first.trans solved.symm))
  have equation := congrArg (fun action : DivisionRow 8 lower →L[ℂ] DivisionRow 1 lower => action input)
    (eliminatedXAction_solves parameters length compact lower positive bounded state 0)
  exact (completedFirstRow_iff_eliminated parameters length compact lower positive bounded state 0 x input high).mp
    (same.trans equation)

end Grad.AnnularOriginalSmoothCore
