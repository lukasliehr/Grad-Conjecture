import DE1Summability

noncomputable section

open Filter
open scoped BigOperators Topology

namespace Grad.DiskExtension.Seeley

theorem moment_tannery (order : ℕ) :
    Tendsto (fun cutoff => ∑' index,
      finiteCoefficient cutoff index * (-node index) ^ order) atTop
      (nhds (∑' index, coefficient index * (-node index) ^ order)) := by
  apply tendsto_tsum_of_dominated_convergence (momentMajorant_summable order)
  · intro index
    exact (coefficient_tendsto index).mul_const ((-node index) ^ order)
  · exact Filter.Eventually.of_forall (fun cutoff index => by
      simpa only [Real.norm_eq_abs] using finite_moment_bound cutoff order index)

theorem finite_moment_tsum (cutoff order : ℕ) (bounded : order ≤ cutoff) :
    ∑' index, finiteCoefficient cutoff index * (-node index) ^ order = 1 := by
  rw [tsum_eq_sum (s := Finset.range (cutoff + 1))]
  · exact finite_moment cutoff order bounded
  · intro index outside
    have beyond : cutoff + 1 ≤ index := by simpa only [Finset.mem_range, not_lt] using outside
    rw [finite_zero_padding cutoff index (by omega), zero_mul]

theorem finite_moment_tendsto_one (order : ℕ) :
    Tendsto (fun cutoff => ∑' index,
      finiteCoefficient cutoff index * (-node index) ^ order) atTop (nhds 1) := by
  apply (tendsto_congr' ?_).mpr tendsto_const_nhds
  filter_upwards [eventually_ge_atTop order] with cutoff bounded
  exact finite_moment_tsum cutoff order bounded

theorem infinite_moment_tsum (order : ℕ) :
    ∑' index, coefficient index * (-node index) ^ order = 1 :=
  tendsto_nhds_unique (moment_tannery order) (finite_moment_tendsto_one order)

theorem infinite_moment_hasSum (order : ℕ) :
    HasSum (fun index => coefficient index * (-(2 : ℝ) ^ index) ^ order) 1 := by
  have convergence := (coefficient_signed_moment_summable order).hasSum
  rw [infinite_moment_tsum order] at convergence
  simpa only [node] using convergence

theorem moment_goal : MomentGoal :=
  ⟨moment_tannery, infinite_moment_hasSum, infinite_moment_tsum⟩

end Grad.DiskExtension.Seeley
