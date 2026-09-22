import BL20DiskCollar

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

theorem collarIntegral_nonnegative (function : ℝ × ℝ → ℝ) (nonnegative : ∀ point, 0 ≤ function point) :
    0 ≤ collarIntegral function := by
  apply integral_nonneg
  intro angle
  exact intervalIntegral.integral_nonneg (by norm_num) (fun time _ => nonnegative (time, angle))

theorem collarIntegral_finsetSum {Index : Type*} (indices : Finset Index) (functions : Index → ℝ × ℝ → ℝ)
    (continuousFunctions : ∀ index ∈ indices, Continuous (functions index)) :
    collarIntegral (fun point => ∑ index ∈ indices, functions index point) =
      ∑ index ∈ indices, collarIntegral (functions index) := by
  unfold collarIntegral
  have inner (angle : ℝ) : (∫ time in (0 : ℝ)..(1 / 4 : ℝ),
      ∑ index ∈ indices, functions index (time, angle)) =
      ∑ index ∈ indices, ∫ time in (0 : ℝ)..(1 / 4 : ℝ), functions index (time, angle) := by
    apply intervalIntegral.integral_finsetSum
    intro index member
    have continuousSlice : Continuous (fun time : ℝ => functions index (time, angle)) :=
      (continuousFunctions index member).comp (continuous_id.prodMk continuous_const)
    exact continuousSlice.intervalIntegrable _ _
  simp_rw [inner]
  rw [integral_finsetSum]
  intro index member
  exact ((timeIntegral_continuous (functions index) (continuousFunctions index member) 0 (1 / 4)
    (by norm_num)).continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self

theorem polarJetSquaredDensity_continuous {dimension : ℕ} (field : ℝ × ℝ → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ field) (depth : ℕ) : Continuous (polarJetSquaredDensity field depth) := by
  apply continuous_finsetSum
  intro order _
  exact ((smooth.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm).pow 2

def polarDensityEnergyConstant (parameters : PhaseParameters) (depth : ℕ) : ℝ :=
  ∑ order ∈ Finset.range (depth + 1), polarEnergyConstant parameters order

theorem polarDensityEnergyConstant_nonnegative (parameters : PhaseParameters) (depth : ℕ) :
    0 ≤ polarDensityEnergyConstant parameters depth :=
  Finset.sum_nonneg (fun order _ => polarEnergyConstant_nonnegative parameters order)

theorem finitePolarField_weighted_density {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (modes : Finset ℤ) (values : ℤ → ComplexEuclidean dimension) (grade depth : ℕ)
    (gradePositive : 1 ≤ grade) (depthBound : depth ≤ grade) :
    cellFrequency cell ^ (2 * (grade - depth)) *
      collarIntegral (polarJetSquaredDensity (finitePolarField parameters cell modes values) depth) ≤
      polarDensityEnergyConstant parameters depth * ∑ mode ∈ modes,
        boundaryFrequency (mode, cell) ^ (2 * grade - 1) * ‖values mode‖ ^ 2 := by
  have derivativeContinuous (order : ℕ) : Continuous (fun point : ℝ × ℝ =>
      ‖iteratedFDeriv ℝ order (finitePolarField parameters cell modes values) point‖ ^ 2) :=
    (((finitePolarField_smooth parameters cell modes values).continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm).pow 2
  rw [show polarJetSquaredDensity (finitePolarField parameters cell modes values) depth =
      fun point => ∑ order ∈ Finset.range (depth + 1),
        ‖iteratedFDeriv ℝ order (finitePolarField parameters cell modes values) point‖ ^ 2 by rfl,
    collarIntegral_finsetSum _ _ (fun order _ => derivativeContinuous order), Finset.mul_sum,
    polarDensityEnergyConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro order orderIn
  have orderBound : order ≤ depth := by have := Finset.mem_range.mp orderIn; omega
  have frequencyBound : cellFrequency cell ^ (2 * (grade - depth)) ≤
      cellFrequency cell ^ (2 * (grade - order)) :=
    pow_le_pow_right₀ (cellFrequency_one_le cell) (by omega)
  have integralNonnegative := collarIntegral_nonnegative
    (fun point => ‖iteratedFDeriv ℝ order (finitePolarField parameters cell modes values) point‖ ^ 2)
    (fun _ => sq_nonneg _)
  exact (mul_le_mul_of_nonneg_right frequencyBound integralNonnegative).trans
    (finitePolarField_weighted_energy parameters cell modes values grade order gradePositive
      (orderBound.trans depthBound))

end Grad.BoundaryLift
