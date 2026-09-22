import AKDK9PureFrequencyAllocation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace Grad.OriginalTerminalAllocation
open Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Physical.Allocation

theorem cellL2_componentwise_twoInput {dimension : ℕ} (output high low : CellL2 dimension)
    (constant budget : ℝ) (constant0 : 0≤constant) (budget0 : 0≤budget)
    (bound : ∀ mode, ‖output mode‖≤constant*(‖high mode‖+budget*‖low mode‖)) :
    ‖output‖≤2*constant*(‖high‖+budget*‖low‖) := by
  have each (mode : ℤ × ℤ) : ‖output mode‖^2≤
      (2*constant^2)*‖high mode‖^2+(2*constant^2*budget^2)*‖low mode‖^2 := by
    have square := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg constant0
      (add_nonneg (norm_nonneg _) (mul_nonneg budget0 (norm_nonneg _))))).mpr (bound mode)
    have positive := mul_nonneg (sq_nonneg constant) (sq_nonneg (‖high mode‖-budget*‖low mode‖))
    nlinarith only [square,positive]
  have highS := (cellL2_square_summable high).mul_left (2*constant^2)
  have lowS := (cellL2_square_summable low).mul_left (2*constant^2*budget^2)
  have total := (cellL2_square_summable output).tsum_le_tsum each (highS.add lowS)
  rw [highS.tsum_add lowS,tsum_mul_left,tsum_mul_left,← cellL2_norm_sq,← cellL2_norm_sq,← cellL2_norm_sq] at total
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) constant0)
    (add_nonneg (norm_nonneg _) (mul_nonneg budget0 (norm_nonneg _))))).mp
  have positive := mul_nonneg (sq_nonneg constant) (mul_nonneg (norm_nonneg high) (mul_nonneg budget0 (norm_nonneg low)))
  nlinarith only [total,positive,sq_nonneg (constant*‖high‖),sq_nonneg (constant*budget*‖low‖)]

/-- Joint coefficient/terminal ν allocation for the SAME native Fourier
field. No radial derivative or interpolation extension is assumed. -/
theorem pureCell_jointAllocation {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters 3) (rho epsilon : ℝ) (offset grade order power : ℕ)
    (gradePositive : 0<grade) (paid : order+power≤grade)
    (small : physicalBudget parameters field rho epsilon offset≤1)
    (base middle high : CellL2 dimension)
    (middleSame : ∀ mode : ℤ × ℤ, middle mode=(annularFrequency mode.1 mode.2 : ℂ)^power • base mode)
    (highSame : ∀ mode : ℤ × ℤ, high mode=(annularFrequency mode.1 mode.2 : ℂ)^grade • base mode) :
    ‖(1+physicalBudget parameters field rho epsilon (offset+order)) • middle‖≤
      2*(1+physicalInterpolationConstant offset grade)*
        (‖high‖+(1+physicalBudget parameters field rho epsilon (offset+grade))*‖base‖) := by
  have K0 := add_nonneg zero_le_one (physicalBudget_nonnegative parameters field rho epsilon (offset+order))
  have B0 := add_nonneg zero_le_one (physicalBudget_nonnegative parameters field rho epsilon (offset+grade))
  have C0 := add_nonneg zero_le_one (zero_le_one.trans (physicalInterpolationConstant_one_le offset grade))
  apply cellL2_componentwise_twoInput _ high base _ _ C0 B0
  intro mode
  have frequency0 := annularFrequency_pos mode
  have frequencyOne : 1≤annularFrequency mode.1 mode.2 := by
    exact Grad.BoundaryKernelAction.annularFrequency_one_le mode
  have scalar := pureFrequency_jointAllocation parameters field rho epsilon offset grade order power gradePositive paid small
    (annularFrequency mode.1 mode.2) frequencyOne
  have result := mul_le_mul_of_nonneg_right scalar (norm_nonneg (base mode))
  change ‖(1+physicalBudget parameters field rho epsilon (offset+order)) • middle mode‖≤_
  rw [norm_smul,Real.norm_of_nonneg K0,middleSame mode,highSame mode]
  simp only [norm_smul,norm_pow,Complex.norm_real,Real.norm_of_nonneg frequency0.le]
  nlinarith only [result]

end Grad.OriginalTerminalAllocation
