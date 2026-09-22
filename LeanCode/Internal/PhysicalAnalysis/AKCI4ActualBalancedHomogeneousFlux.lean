import AKCI3ActualBalancedRowOneOrder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.AnnularSmoothCore Grad.AnnularWeightedSystem Grad.BoundaryLift Grad.AnnularCurrentLow
open Grad.GaugeCoefficients.Physical.Allocation

abbrev PhysicalHilbertTriple := CellL2 1 × (CellL2 1 × CellL2 1)

/-- SR15's actual homogeneous flux combination. Both differentiated fluxes
have their original negative signs; the first component keeps its gauge. -/
def balancedFluxOutput (parameters : PhaseParameters) (length radius : ℝ) :
    PhysicalHilbertTriple →L[ℂ] PhysicalHilbertPair :=
  let first := ContinuousLinearMap.fst ℂ (CellL2 1) (CellL2 1 × CellL2 1)
  let tail := ContinuousLinearMap.snd ℂ (CellL2 1) (CellL2 1 × CellL2 1)
  let second := (ContinuousLinearMap.fst ℂ (CellL2 1) (CellL2 1)).comp tail
  let third := (ContinuousLinearMap.snd ℂ (CellL2 1) (CellL2 1)).comp tail
  (ContinuousLinearMap.inl ℂ (CellL2 1) (CellL2 1)).comp ((hilbertMeanFree parameters).comp first) -
    ((radius : ℂ)*(length : ℂ)⁻¹) • (ContinuousLinearMap.inr ℂ (CellL2 1) (CellL2 1)).comp
      ((hilbertFrequencyOperator parameters 1 (some true)).comp second) -
    (ContinuousLinearMap.inr ℂ (CellL2 1) (CellL2 1)).comp
      ((hilbertFrequencyOperator parameters 1 (some false)).comp third)

theorem balancedFluxOutput_actual (parameters : PhaseParameters) (length radius : ℝ)
    (first second third : CellL2 1) :
    balancedFluxOutput parameters length radius (first,(second,third)) =
      (hilbertMeanFree parameters first,
        - ((radius : ℂ)*(length : ℂ)⁻¹) • hilbertFrequencyOperator parameters 1 (some true) second -
          hilbertFrequencyOperator parameters 1 (some false) third) := by
  change ((hilbertMeanFree parameters first,(0 : CellL2 1)) -
    ((radius : ℂ)*(length : ℂ)⁻¹) • ((0 : CellL2 1),hilbertFrequencyOperator parameters 1 (some true) second) -
    ((0 : CellL2 1),hilbertFrequencyOperator parameters 1 (some false) third)) = _
  ext <;> simp

theorem balancedFluxOutput_uniformBound (parameters : PhaseParameters) (length : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ radius : RadialPoint,
      ‖balancedFluxOutput parameters length radius‖ ≤ constant := by
  have continuous : Continuous (balancedFluxOutput parameters length) := by
    unfold balancedFluxOutput
    exact (continuous_const.sub ((Complex.ofRealCLM.continuous.mul_const _).smul continuous_const)).sub continuous_const
  obtain ⟨constant,bounded⟩ := isCompact_Icc.exists_bound_of_continuousOn continuous.continuousOn
  exact ⟨max 0 constant,le_max_left _ _,fun radius =>
    (bounded radius.val ⟨radius.property.1,radius.property.2⟩).trans (le_max_right _ _)⟩

/-- Actual homogeneous flux part of the balanced original radial equation:
one next tangential grade, one high coefficient times the same base unknown. -/
theorem actualBalancedHomogeneousFlux_oneOrder (parameters : PhaseParameters) (length compact : ℝ)
    (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (state : RetainedInverseState parameters length compact),
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (radius : RadialPoint) (high low : PhysicalHilbertPair),
    (∀ mode, hilbertPairCoefficient mode high =
      (annularFrequency mode.1 mode.2 : ℂ)^(grade+1) • hilbertPairCoefficient mode low) →
    let row := fun index : Fin 3 => bulkKernelAction parameters (grade+1) radius
      (lowPhysicalRowKernel parameters length compact state index radius) (balancedSevenInput parameters radius high)
    ‖balancedFluxOutput parameters length radius (row 0,(row 1,row 2))‖ ≤
      constant * (‖high‖ +
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+11) * ‖low‖) := by
  choose constants nonnegative bounds using fun row : Fin 3 => actualBalancedRow_oneOrder parameters length compact row grade
  obtain ⟨outputConstant,outputNonnegative,outputBound⟩ := balancedFluxOutput_uniformBound parameters length
  let total := ∑ row : Fin 3, constants row
  have totalNonnegative : 0 ≤ total := Finset.sum_nonneg (fun row _ => nonnegative row)
  refine ⟨outputConstant*total,mul_nonneg outputNonnegative totalNonnegative,?_⟩
  intro state small radius high low same
  dsimp only
  let row := fun index : Fin 3 => bulkKernelAction parameters (grade+1) radius
    (lowPhysicalRowKernel parameters length compact state index radius) (balancedSevenInput parameters radius high)
  let payment := ‖high‖ + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+11)*‖low‖
  have paymentNonnegative : 0 ≤ payment := add_nonneg (norm_nonneg _)
    (mul_nonneg (physicalBudget_nonnegative _ _ _ _ _) (norm_nonneg _))
  have rowBound (index : Fin 3) : ‖row index‖ ≤ total*payment := by
    have indexLe : constants index ≤ total := Finset.single_le_sum (fun i _ => nonnegative i) (Finset.mem_univ index)
    exact (bounds index state small radius high low same).trans
      (mul_le_mul_of_nonneg_right indexLe paymentNonnegative)
  have tripleBound : ‖(row 0,(row 1,row 2))‖ ≤ total*payment := by
    rw [Prod.norm_def,Prod.norm_def]
    exact max_le (rowBound 0) (max_le (rowBound 1) (rowBound 2))
  have result := ((balancedFluxOutput parameters length radius).le_opNorm (row 0,(row 1,row 2))).trans
    (mul_le_mul (outputBound radius) tripleBound (norm_nonneg _) outputNonnegative)
  exact result.trans_eq (by dsimp only [payment]; ring)

end Grad.OriginalCartesianTameEstimate
