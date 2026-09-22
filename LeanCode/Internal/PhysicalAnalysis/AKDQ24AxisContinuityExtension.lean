import AKDQ23AmbientForceContinuity

noncomputable section
open Set Filter
open scoped Topology

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily Grad.NonlinearQuotient

variable {Value : Type} [NormedAddCommGroup Value]

/-- Continuity fills the single omitted axis point from an explicit sequence
inside the SAME closed unit disk. -/
theorem zero_at_axis_of_punctured_zero (field : Plane → Value) (continuous : ContinuousAt field 0)
    (zero : ∀ point : Plane, ‖point‖ ≤ 1 → point ≠ 0 → field point = 0) : field 0 = 0 := by
  let path : ℕ → Plane := fun index => ((1 / 2 : ℝ) ^ index) • diskBasis 0
  have basisNorm : ‖diskBasis 0‖ = 1 := by
    change ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ = 1
    simp
  have basisNonzero : diskBasis 0 ≠ 0 := by
    intro equal
    rw [equal, norm_zero] at basisNorm
    norm_num at basisNorm
  have pathTendsto : Tendsto path atTop (𝓝 0) := by
    have scalar := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    simpa [path] using scalar.smul_const (diskBasis 0)
  have pathZero : ∀ index, field (path index) = 0 := by
    intro index
    apply zero
    · dsimp only [path]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _), basisNorm, mul_one]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    · exact smul_ne_zero (pow_ne_zero _ (by norm_num : (1 / 2 : ℝ) ≠ 0)) basisNonzero
  have valueTendsto := continuous.tendsto.comp pathTendsto
  have identity : field ∘ path = fun _ : ℕ => (0 : Value) := funext pathZero
  rw [identity] at valueTendsto
  exact tendsto_nhds_unique valueTendsto tendsto_const_nhds

end Grad.PhysicalEquilibrium
