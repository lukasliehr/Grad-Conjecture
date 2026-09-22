import AKCK4ActualCartesianRestrictionEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.AnnularSmoothCore Grad.AnnularWeightedSystem Grad.BoundaryLift Grad.AnnularCurrentLow
open Grad.GaugeCoefficients.Physical.Allocation

/-- The known-source row part of the balanced original radial equation uses
the SAME high and base primitive source packet, before any norm allocation. -/
theorem actualBalancedKnownFlux_oneOrder (parameters : PhaseParameters) (length compact : ℝ)
    (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (state : RetainedInverseState parameters length compact),
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (radius : RadialPoint) (high low : CellL2 7),
    (∀ mode, high mode =
      (annularFrequency mode.1 mode.2 : ℂ)^(grade+1) • low mode) →
    let row := fun index : Fin 3 => bulkKernelAction parameters (grade+1) radius
      (lowPhysicalRowKernel parameters length compact state index radius) high
    ‖balancedFluxOutput parameters length radius (row 0,(row 1,row 2))‖ ≤
      constant * (‖high‖ +
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+11) * ‖low‖) := by
  choose constants nonnegative bounds using fun row : Fin 3 => actualPhysicalRow_oneHigh parameters length compact row (grade+1)
  obtain ⟨outputConstant,outputNonnegative,outputBound⟩ := balancedFluxOutput_uniformBound parameters length
  let total := ∑ row : Fin 3, constants row
  have totalNonnegative : 0 ≤ total := Finset.sum_nonneg (fun row _ => nonnegative row)
  refine ⟨outputConstant*total,mul_nonneg outputNonnegative totalNonnegative,?_⟩
  intro state small radius high low same
  dsimp only
  let row := fun index : Fin 3 => bulkKernelAction parameters (grade+1) radius
    (lowPhysicalRowKernel parameters length compact state index radius) high
  let payment := ‖high‖ + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+11)*‖low‖
  have paymentNonnegative : 0 ≤ payment := add_nonneg (norm_nonneg _)
    (mul_nonneg (physicalBudget_nonnegative _ _ _ _ _) (norm_nonneg _))
  have rowBound (index : Fin 3) : ‖row index‖ ≤ total*payment := by
    have indexLe : constants index ≤ total := Finset.single_le_sum (fun i _ => nonnegative i) (Finset.mem_univ index)
    have bound : ‖row index‖ ≤ constants index*payment := by
      simpa only [Nat.add_assoc] using bounds index state small radius high low same
    exact bound.trans (mul_le_mul_of_nonneg_right indexLe paymentNonnegative)
  have tripleBound : ‖(row 0,(row 1,row 2))‖ ≤ total*payment := by
    rw [Prod.norm_def,Prod.norm_def]
    exact max_le (rowBound 0) (max_le (rowBound 1) (rowBound 2))
  have result := ((balancedFluxOutput parameters length radius).le_opNorm (row 0,(row 1,row 2))).trans
    (mul_le_mul (outputBound radius) tripleBound (norm_nonneg _) outputNonnegative)
  exact result.trans_eq (by dsimp only [payment]; ring)


end Grad.OriginalCartesianTameEstimate
