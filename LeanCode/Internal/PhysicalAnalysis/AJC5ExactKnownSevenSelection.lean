import AJC4SameFullLowPhysicalRow
import AIQ9CompletedPhysicalFluxAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularKernelL2
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularPhysicalSolution
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger

theorem knownSevenBulkAction_ae (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (power : ℕ) (input : DivisionRow 8 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      knownSevenBulkAction parameters lower positive bounded power input mode radius =
        knownEightToSevenMap (input mode radius) := by
  unfold knownSevenBulkAction regularRadialBulkAction knownEightToSevenKernel constantMatrixKernel
  apply completedBulkKernel_diagonal_ae

private theorem knownSelection_basis (slot : Fin 7) (nonzero : slot ≠ 0) :
    knownEightToSevenMap (operatorBasis slot.castSucc) = operatorBasis slot := by
  apply PiLp.ext
  intro component
  rw [knownEightToSevenMap_apply]
  fin_cases slot <;> fin_cases component <;> simp_all [operatorBasis]

private theorem knownSelection_first :
    knownEightToSevenMap (operatorBasis (0 : Fin 8)) = 0 := by
  apply PiLp.ext
  intro component
  rw [knownEightToSevenMap_apply]
  fin_cases component <;> norm_num [operatorBasis]

private theorem knownSelection_last :
    knownEightToSevenMap (operatorBasis (7 : Fin 8)) = 0 := by
  apply PiLp.ext
  intro component
  rw [knownEightToSevenMap_apply]
  fin_cases component <;> norm_num [operatorBasis] <;> decide

/-- Completed selection keeps precisely the six shared physical positions,
and removes the radial-equation datum in position zero. -/
theorem knownSevenBulkAction_slot (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (power : ℕ)
    (slot : Fin 7) (field : DivisionRow 1 lower) :
    knownSevenBulkAction parameters lower positive bounded power
      (bulkMatrixUnit lower slot.castSucc 0 field) =
      if slot = 0 then 0 else bulkMatrixUnit lower slot 0 field := by
  by_cases zero : slot = 0
  · subst slot
    rw [if_pos rfl]
    change knownSevenBulkAction parameters lower positive bounded power
      (bulkMatrixUnit lower (0 : Fin 8) (0 : Fin 1) field) = (0 : DivisionRow 7 lower)
    apply lp.ext
    funext mode
    apply Lp.ext
    filter_upwards [knownSevenBulkAction_ae parameters lower positive bounded power
      (bulkMatrixUnit lower (0 : Fin 8) 0 field),
      bulkMatrixUnit_ae lower (0 : Fin 8) (0 : Fin 1) field,
      Lp.coeFn_zero (ComplexEuclidean 7) 2 (volume.restrict (Icc lower 1))] with radius actual slotValue zeroValue
    rw [actual mode, slotValue mode, map_smul, knownSelection_first, smul_zero]
    exact zeroValue.symm
  · rw [if_neg zero]
    apply lp.ext
    funext mode
    apply Lp.ext
    filter_upwards [knownSevenBulkAction_ae parameters lower positive bounded power
      (bulkMatrixUnit lower slot.castSucc 0 field),
      bulkMatrixUnit_ae lower slot.castSucc (0 : Fin 1) field,
      bulkMatrixUnit_ae lower slot (0 : Fin 1) field] with radius actual input output
    rw [actual mode, input mode, output mode, map_smul, knownSelection_basis slot zero]

/-- The f row is a first-equation datum, not a second copy of a physical
source in the seven-slot reconstruction. -/
theorem knownSevenBulkAction_last (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (power : ℕ) (field : DivisionRow 1 lower) :
    knownSevenBulkAction parameters lower positive bounded power
      (bulkMatrixUnit lower (7 : Fin 8) 0 field) = 0 := by
  apply lp.ext
  funext mode
  apply Lp.ext
  filter_upwards [knownSevenBulkAction_ae parameters lower positive bounded power
    (bulkMatrixUnit lower (7 : Fin 8) 0 field),
    bulkMatrixUnit_ae lower (7 : Fin 8) (0 : Fin 1) field,
    Lp.coeFn_zero (ComplexEuclidean 7) 2 (volume.restrict (Icc lower 1))] with radius actual slotValue zeroValue
  rw [actual mode, slotValue mode, map_smul, knownSelection_last, smul_zero]
  exact zeroValue.symm

end Grad.AnnularStrongSolution
