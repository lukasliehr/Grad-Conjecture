import ANR29RadialPrimitiveDerivative

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState

private theorem closedCollar_succ (dimension : ℕ) (lower : ℝ) (bounded : lower < 1) (order : ℕ)
    (field derivative : ℝ → ComplexEuclidean dimension)
    (law : ∀ radius ∈ Icc lower 1, HasDerivWithinAt field (derivative radius) (Icc lower 1) radius)
    (smooth : ContDiffOn ℝ order derivative (Icc lower 1)) :
    ContDiffOn ℝ (order + 1 : ℕ) field (Icc lower 1) := by
  have unique : UniqueDiffOn ℝ (Icc lower 1) := uniqueDiffOn_Icc bounded
  rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_derivWithin unique]
  refine ⟨fun radius inside => (law radius inside).differentiableWithinAt, by simp, ?_⟩
  have equality : EqOn (derivWithin field (Icc lower 1)) derivative (Icc lower 1) :=
    fun radius inside => (law radius inside).derivWithin (unique radius inside)
  exact (contDiffOn_congr equality).mpr smooth

/-- V4's all-order induction for the actual radial first-order system.
Only the continuous representatives and their proved classical first
derivative laws are used; no higher regularity premise is introduced. -/
theorem radialSystem_smooth (dimension : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (scalar : ℂ) (source : ℝ → ComplexEuclidean dimension) (sourceSmooth : ContDiff ℝ ∞ source)
    (value flux : C(ℝ, ComplexEuclidean dimension))
    (valueLaw : ∀ radius ∈ Icc lower 1,
      HasDerivWithinAt value (radius⁻¹ • flux radius) (Icc lower 1) radius)
    (fluxLaw : ∀ radius ∈ Icc lower 1,
      HasDerivWithinAt flux (((mode : ℝ) ^ 2 / radius) • value radius +
        radius • (scalar • value radius - source radius)) (Icc lower 1) radius) :
    ContDiffOn ℝ ∞ value (Icc lower 1) ∧ ContDiffOn ℝ ∞ flux (Icc lower 1) := by
  have everyOrder (order : ℕ) : ContDiffOn ℝ order value (Icc lower 1) ∧
      ContDiffOn ℝ order flux (Icc lower 1) := by
    induction order with
    | zero => exact ⟨contDiffOn_zero.mpr value.continuous.continuousOn,
        contDiffOn_zero.mpr flux.continuous.continuousOn⟩
    | succ order previous =>
      have reciprocal : ContDiffOn ℝ order (fun radius : ℝ => radius⁻¹) (Icc lower 1) :=
        contDiffOn_id.inv (fun radius inside => (positive.trans_le inside.1).ne')
      have potential : ContDiffOn ℝ order (fun radius : ℝ => (mode : ℝ) ^ 2 / radius) (Icc lower 1) := by
        simpa only [div_eq_mul_inv] using (contDiffOn_const.mul reciprocal :
          ContDiffOn ℝ order (fun radius : ℝ => (mode : ℝ) ^ 2 * radius⁻¹) (Icc lower 1))
      have first := reciprocal.smul previous.2
      have sourceOrder : ContDiffOn ℝ order source (Icc lower 1) :=
        (contDiffOn_infty.mp sourceSmooth.contDiffOn) order
      have second := (potential.smul previous.1).add
        (contDiffOn_id.smul ((previous.1.const_smul scalar).sub sourceOrder))
      exact ⟨closedCollar_succ dimension lower bounded order value _ valueLaw first,
        closedCollar_succ dimension lower bounded order flux _ fluxLaw second⟩
  exact ⟨contDiffOn_infty.mpr (fun order => (everyOrder order).1),
    contDiffOn_infty.mpr (fun order => (everyOrder order).2)⟩

end Grad.CircularHighRegularity
