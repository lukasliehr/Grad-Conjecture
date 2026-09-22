import AJB15CompleteLpGeneratorMembership

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOrbitGenerators

variable {ι κ : Type*} {V : ι → Type*} [∀ index, NormedAddCommGroup (V index)]

theorem lp_finite_norm_sq_le (field : lp V 2) (support : Finset ι) :
    (∑ index ∈ support, ‖field index‖ ^ 2) ≤ ‖field‖ ^ 2 := by
  have summable := (memℓp_gen_iff (p := 2) (by norm_num)).mp field.property
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at summable
  have normSquare := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at normSquare
  rw [normSquare]
  exact Summable.sum_le_tsum support (fun _ _ => sq_nonneg _) summable

/-- The actual Hilbert coefficient limit of uniformly norm-bounded vectors
belongs to the same lp carrier. This is the finite-approximation/Fatou passage. -/
theorem lp_of_bounded_coordinate_limit (source : Filter κ) [NeBot source]
    (approximation : κ → lp V 2) (limit : (index : ι) → V index)
    (converges : ∀ index, Tendsto (fun stage => approximation stage index) source (𝓝 (limit index)))
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (bounded : ∀ stage, ‖approximation stage‖ ≤ bound) :
    ∃ result : lp V 2, (∀ index, result index = limit index) ∧ ‖result‖ ≤ bound := by
  have finite (support : Finset ι) : (∑ index ∈ support, ‖limit index‖ ^ 2) ≤ bound ^ 2 := by
    apply le_of_tendsto (tendsto_finsetSum support (fun index _ => (converges index).norm.pow 2))
    exact Filter.Eventually.of_forall (fun stage => (lp_finite_norm_sq_le (approximation stage) support).trans
      (pow_le_pow_left₀ (norm_nonneg _) (bounded stage) 2))
  have summable : Summable (fun index => ‖limit index‖ ^ 2) := summable_of_sum_le (fun _ => sq_nonneg _) finite
  have membership : Memℓp limit 2 := by
    apply (memℓp_gen_iff (p := 2) (by norm_num)).mpr
    simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using summable
  let result : lp V 2 := ⟨limit, membership⟩
  refine ⟨result, fun _ => rfl, ?_⟩
  have normSquare := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) result
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at normSquare
  have upper := summable.tsum_le_of_sum_le finite
  change (∑' index, ‖result index‖ ^ 2) ≤ bound ^ 2 at upper
  rw [← normSquare] at upper
  nlinarith only [upper, boundNonnegative, norm_nonneg result]

end Grad.AnnularOrbitGenerators
