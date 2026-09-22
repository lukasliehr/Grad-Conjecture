import AKDM6RecoveredCovariantPureCellEndpoint
import AKBZ7OriginalMixedPureEndpointEstimate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- The original order-zero norm is exactly its pure-cell endpoint. -/
theorem originalGradeNorm_zero_eq_cell {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) :
    originalGradeNorm 0 core = originalCellNorm parameters 0 core := by
  apply (sq_eq_sq₀ (originalGradeNorm_nonnegative 0 core) (Real.sqrt_nonneg _)).mp
  have original : originalGradeNorm 0 core^2 =
      ∑' cell : ℤ, ‖cellGradeRowLinear (grade:=0) parameters cell (core.val cell)‖^2 :=
    originalGrade_norm_sq_eq_rows parameters core
  change originalGradeNorm 0 core^2 = originalCellNorm parameters 0 core^2
  rw [original,originalCellNorm_sq]
  apply tsum_congr
  intro cell
  rw [originalWeightedRow_mass]
  simp only [pow_zero,one_mul]

/-- Extract the independent base slot from a literal order-zero tame
endpoint on a fixed bounded coefficient ball. -/
theorem originalGradeNorm_zero_of_cellTame {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (cost source budget : ℝ)
    (costNonnegative : 0≤cost) (sourceNonnegative : 0≤source) (bounded : budget≤1)
    (cell : originalCellNorm parameters 0 core ≤ cost*(source+budget*source)) :
    originalGradeNorm 0 core ≤ (2*cost)*source := by
  rw [originalGradeNorm_zero_eq_cell parameters core]
  have product := mul_le_mul_of_nonneg_right bounded sourceNonnegative
  have paid := mul_le_mul_of_nonneg_left (add_le_add_left product source) costNonnegative
  nlinarith only [cell,paid]

/-- The second CT absorption is performed on the finite original norm,
using the proved pure-endpoint constant; its choice changes no state ball. -/
theorem originalMixedNorm_absorb_planar {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (positive : 0<grade) (core : ACore parameters dimension)
    (planarPayment cellPayment : ℝ)
    (planar : originalPlanarNorm parameters grade core ≤
      (1 / (4*apMassEndpointConstant 0 grade+2))*originalGradeNorm grade core+planarPayment)
    (cell : originalCellNorm parameters grade core ≤ cellPayment) :
    originalGradeNorm grade core ≤
      (4*apMassEndpointConstant 0 grade)*(planarPayment+cellPayment) := by
  let constant := apMassEndpointConstant 0 grade
  have constantNonnegative : 0≤constant := apMassEndpointConstant_nonnegative 0 grade
  have denominatorPositive : 0<4*constant+2 := by positivity
  have factor : (2*constant)*(1/(4*constant+2)) ≤ (1/2:ℝ) := by
    rw [mul_one_div,div_le_iff₀ denominatorPositive]
    linarith
  have endpoint := originalMixedNorm_pureEndpoints parameters grade positive core
  have paid := mul_le_mul_of_nonneg_left (add_le_add planar cell)
    (mul_nonneg (by norm_num : (0:ℝ)≤2) constantNonnegative)
  have absorbed := mul_le_mul_of_nonneg_right factor (originalGradeNorm_nonnegative grade core)
  change originalGradeNorm grade core ≤ (2*constant)*_ at endpoint
  change originalGradeNorm grade core ≤ (4*constant)*_
  nlinarith only [endpoint,paid,absorbed]

end Grad.OriginalCartesianTameEstimate
