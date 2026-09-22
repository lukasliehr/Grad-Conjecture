import AKCI2LiteralBalancedSevenInput

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.AnnularSmoothCore Grad.AnnularWeightedSystem Grad.BoundaryLift Grad.AnnularCurrentLow
open Grad.GaugeCoefficients.Physical.Allocation

theorem balancedSevenInput_continuous (parameters : PhaseParameters) :
    Continuous (balancedSevenInput parameters) := by
  unfold balancedSevenInput
  exact ((continuous_const.add continuous_const).add
    (Complex.ofRealCLM.continuous.smul continuous_const)).add continuous_const

/-- The balanced packet is uniformly order zero, including at r=0. Its
constant depends only on the fixed spaces and is independent of the state. -/
theorem balancedSevenInput_uniformBound (parameters : PhaseParameters) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ radius : RadialPoint,
      ‖balancedSevenInput parameters radius‖ ≤ constant := by
  obtain ⟨constant,bounded⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (balancedSevenInput_continuous parameters).continuousOn
  refine ⟨max 0 constant,le_max_left _ _,?_⟩
  intro radius
  exact (bounded radius.val ⟨radius.property.1,radius.property.2⟩).trans (le_max_right _ _)

/-- Each literal SR15 flux row consumes precisely the next total tangential
grade of SR14's balanced unknown. The coefficient branch uses its base input. -/
theorem actualBalancedRow_oneOrder (parameters : PhaseParameters) (length compact : ℝ)
    (row : Fin 3) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (state : RetainedInverseState parameters length compact),
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (radius : RadialPoint) (high low : PhysicalHilbertPair),
    (∀ mode, hilbertPairCoefficient mode high =
      (annularFrequency mode.1 mode.2 : ℂ)^(grade+1) • hilbertPairCoefficient mode low) →
    ‖bulkKernelAction parameters (grade+1) radius (lowPhysicalRowKernel parameters length compact state row radius)
      (balancedSevenInput parameters radius high)‖ ≤
      constant * (‖high‖ +
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+11) * ‖low‖) := by
  obtain ⟨rowConstant,rowNonnegative,rowBound⟩ := actualPhysicalRow_oneHigh parameters length compact row (grade+1)
  obtain ⟨inputConstant,inputNonnegative,inputBound⟩ := balancedSevenInput_uniformBound parameters
  refine ⟨rowConstant*inputConstant,mul_nonneg rowNonnegative inputNonnegative,?_⟩
  intro state small radius high low same
  have rowEstimate := rowBound state small radius (balancedSevenInput parameters radius high)
    (balancedSevenInput parameters radius low)
    (balancedSevenInput_sameGrade parameters radius (grade+1) high low same)
  have inputEstimate (field : PhysicalHilbertPair) :
      ‖balancedSevenInput parameters radius field‖ ≤ inputConstant*‖field‖ :=
    ((balancedSevenInput parameters radius).le_opNorm field).trans
      (mul_le_mul_of_nonneg_right (inputBound radius) (norm_nonneg field))
  have budgetNonnegative := physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+11)
  have payment := add_le_add (inputEstimate high)
    (mul_le_mul_of_nonneg_left (inputEstimate low) budgetNonnegative)
  have index : grade+1+10 = grade+11 := by omega
  rw [index] at rowEstimate
  exact rowEstimate.trans ((mul_le_mul_of_nonneg_left payment rowNonnegative).trans_eq (by ring))

end Grad.OriginalCartesianTameEstimate
