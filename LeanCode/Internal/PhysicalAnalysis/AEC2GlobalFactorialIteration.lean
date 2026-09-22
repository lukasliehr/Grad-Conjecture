import AEC1ActualGlobalVolterraMap

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat
namespace Grad.AnnularLowVolterra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The factorial iteration estimate follows the argument of Mathlib's
ODE.FunSpace.dist_iterate_next_apply_le, now on the unrestricted complete
continuous-curve space. This removes the local state-ball hypothesis. -/
theorem volterra_iterate_point_bound (lower upper : ℝ) (ordered : lower ≤ upper)
    (coefficient : C(Icc lower upper, E →L[ℝ] E)) (source : C(Icc lower upper, E))
    (initial : E) (bound : ℝ≥0) (bounded : ∀ point, ‖coefficient point‖ ≤ bound)
    (first second : C(Icc lower upper, E)) (count : ℕ) (point : Icc lower upper) :
    dist ((volterraNext lower upper ordered coefficient source initial)^[count] first point)
      ((volterraNext lower upper ordered coefficient source initial)^[count] second point) ≤
      (bound * |point.val - lower|) ^ count / count ! * dist first second := by
  induction count generalizing point with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := first) (g := second) point
  | succ count previous =>
    let next := volterraNext lower upper ordered coefficient source initial
    have integrable (curve : C(Icc lower upper, E)) :
        IntervalIntegrable (volterraIntegrand lower upper ordered coefficient source curve) volume lower point.val :=
      (volterraIntegrand_continuous lower upper ordered coefficient source curve).intervalIntegrable _ _
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, volterraNext_apply,
      volterraNext_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (integrable _) (integrable _)]
    calc
      _ ≤ ∫ radius in uIoc lower point.val,
          bound ^ (count + 1) * |radius - lower| ^ count / count ! * dist first second := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
        apply ae_restrict_mem measurableSet_Ioc |>.mono
        intro radius member
        have member' : radius ∈ Icc lower upper :=
          subset_trans uIoc_subset_uIcc (uIcc_subset_Icc ⟨le_rfl, ordered⟩ point.property) member
        rw [← dist_eq_norm]
        have estimate := volterraIntegrand_dist_bound lower upper ordered coefficient source
          (next^[count] first) (next^[count] second) bound bounded radius
        rw [curveExtension_of_mem lower upper ordered _ radius member',
          curveExtension_of_mem lower upper ordered _ radius member'] at estimate
        refine estimate.trans ?_
        calc
          _ ≤ bound * ((bound * |radius - lower|) ^ count / count ! * dist first second) := by
            exact mul_le_mul_of_nonneg_left (previous ⟨radius, member'⟩) bound.coe_nonneg
          _ = _ := by rw [pow_succ']; ring
      _ ≤ (bound * |point.val - lower|) ^ (count + 1) / (count + 1) ! * dist first second := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

theorem volterra_iterate_bound (lower upper : ℝ) (ordered : lower ≤ upper)
    (coefficient : C(Icc lower upper, E →L[ℝ] E)) (source : C(Icc lower upper, E))
    (initial : E) (bound : ℝ≥0) (bounded : ∀ point, ‖coefficient point‖ ≤ bound)
    (first second : C(Icc lower upper, E)) (count : ℕ) :
    dist ((volterraNext lower upper ordered coefficient source initial)^[count] first)
      ((volterraNext lower upper ordered coefficient source initial)^[count] second) ≤
      (bound * (upper - lower)) ^ count / count ! * dist first second := by
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro point
  refine (volterra_iterate_point_bound lower upper ordered coefficient source initial bound bounded
    first second count point).trans ?_
  have radiusBound : |point.val - lower| ≤ upper - lower := by
    rw [abs_of_nonneg (sub_nonneg.mpr point.property.1)]
    exact sub_le_sub_right point.property.2 lower
  gcongr

/-- Factorial decay gives a contracting iterate on the WHOLE interval,
without any smallness requirement on coefficient norm or interval length. -/
theorem volterra_exists_contracting_iterate (lower upper : ℝ) (ordered : lower ≤ upper)
    (coefficient : C(Icc lower upper, E →L[ℝ] E)) (source : C(Icc lower upper, E))
    (initial : E) (bound : ℝ≥0) (bounded : ∀ point, ‖coefficient point‖ ≤ bound) :
    ∃ (count : ℕ) (constant : ℝ≥0),
      ContractingWith constant (volterraNext lower upper ordered coefficient source initial)^[count] := by
  obtain ⟨count, small⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (bound * (upper - lower))
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have nonnegative : (0 : ℝ) ≤ (bound * (upper - lower)) ^ count / count ! := by positivity
  refine ⟨count, ⟨_, nonnegative⟩, small, LipschitzWith.of_dist_le_mul ?_⟩
  intro first second
  exact volterra_iterate_bound lower upper ordered coefficient source initial bound bounded first second count

end Grad.AnnularLowVolterra
