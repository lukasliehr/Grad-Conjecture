import AW3Interface
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp

noncomputable section

open Grad.PDEBootstrap
open scoped ContDiff Topology BigOperators

namespace Grad.AnalyticWeights.Higher

def sqrtCoefficient (rank : ℕ) : ℝ :=
  ∏ index ∈ Finset.range rank, (1 / 2 - (index : ℝ))

theorem sqrt_iteratedDeriv_rpow (rank : ℕ) (argument : ℝ) (positive : 0 < argument) :
    iteratedDeriv rank Real.sqrt argument =
      sqrtCoefficient rank * argument ^ ((1 / 2 : ℝ) - (rank : ℝ)) := by
  induction rank generalizing argument with
  | zero => simp [sqrtCoefficient, Real.sqrt_eq_rpow]
  | succ rank inductionHypothesis =>
    rw [iteratedDeriv_succ]
    have localEquality : iteratedDeriv rank Real.sqrt =ᶠ[𝓝 argument]
        fun source => sqrtCoefficient rank * source ^ ((1 / 2 : ℝ) - (rank : ℝ)) := by
      filter_upwards [Ioi_mem_nhds positive] with source sourcePositive
      exact inductionHypothesis source sourcePositive
    rw [localEquality.deriv_eq]
    have derivative := (Real.hasDerivAt_rpow_const
      (x := argument) (p := (1 / 2 : ℝ) - (rank : ℝ)) (Or.inl positive.ne')).const_mul
        (sqrtCoefficient rank)
    rw [derivative.deriv]
    simp only [sqrtCoefficient, Nat.cast_add, Nat.cast_one]
    rw [show (1 / 2 : ℝ) - (rank : ℝ) - 1 = 1 / 2 - ((rank : ℝ) + 1) by ring]
    rw [Finset.prod_range_succ]
    ring

theorem sqrt_iteratedDeriv_rational (rank : ℕ) (argument : ℝ) (positive : 0 < argument) :
    iteratedDeriv rank Real.sqrt argument =
      sqrtCoefficient rank * Real.sqrt argument / argument ^ rank := by
  rw [sqrt_iteratedDeriv_rpow rank argument positive,
    Real.rpow_sub_natCast positive.ne', ← Real.sqrt_eq_rpow]
  ring

theorem sqrt_iteratedFDeriv_rational (rank : ℕ) (argument : ℝ) (positive : 0 < argument) :
    iteratedFDeriv ℝ rank Real.sqrt argument =
      ContinuousMultilinearMap.piFieldEquiv ℝ (Fin rank) ℝ
        (sqrtCoefficient rank * Real.sqrt argument / argument ^ rank) := by
  rw [iteratedFDeriv_eq_equiv_comp, Function.comp_apply, sqrt_iteratedDeriv_rational rank argument positive]

def profileQuadratic (point : Spatial) : ℝ := 1 + ‖point‖ ^ 2

theorem profileQuadratic_pos (point : Spatial) : 0 < profileQuadratic point := by
  unfold profileQuadratic
  positivity

theorem profileQuadratic_contDiff : ContDiff ℝ ∞ profileQuadratic :=
  contDiff_const.add (contDiff_norm_sq ℝ)

theorem profile_contDiff : ContDiff ℝ ∞ profile :=
  (profileQuadratic_contDiff.sqrt (fun point => (profileQuadratic_pos point).ne')).sub contDiff_const

theorem profile_rational_expansion (rank : ℕ) (positiveRank : 1 ≤ rank) (point : Spatial) :
    iteratedFDeriv ℝ rank profile point =
      ∑ partition : OrderedFinpartition rank,
        partition.compAlongOrderedFinpartition
          (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin partition.length) ℝ
            (sqrtCoefficient partition.length * Real.sqrt (profileQuadratic point) /
              profileQuadratic point ^ partition.length))
          (fun block => iteratedFDeriv ℝ (partition.partSize block) profileQuadratic point) := by
  have rootSmooth := profileQuadratic_contDiff.sqrt (fun source => (profileQuadratic_pos source).ne')
  change iteratedFDeriv ℝ rank ((fun source => Real.sqrt (profileQuadratic source)) - fun _ => (1 : ℝ)) point = _
  rw [iteratedFDeriv_sub_apply (rootSmooth.of_le (by exact_mod_cast le_top)).contDiffAt
    (contDiff_const (n := (rank : WithTop ℕ∞))).contDiffAt,
    iteratedFDeriv_const_of_ne (by omega)]
  simp only [Pi.zero_apply, sub_zero]
  rw [show (fun source => Real.sqrt (profileQuadratic source)) = Real.sqrt ∘ profileQuadratic from rfl,
    iteratedFDeriv_comp (Real.contDiffAt_sqrt (profileQuadratic_pos point).ne')
      profileQuadratic_contDiff.contDiffAt (by exact_mod_cast le_top)]
  simp only [FormalMultilinearSeries.taylorComp, FormalMultilinearSeries.compAlongOrderedFinpartition,
    ftaylorSeries]
  apply Finset.sum_congr rfl
  intro partition _
  rw [sqrt_iteratedFDeriv_rational partition.length (profileQuadratic point) (profileQuadratic_pos point)]

end Grad.AnalyticWeights.Higher
