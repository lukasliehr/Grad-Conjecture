import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Two-sided geometric inverses in the Banach algebra of bounded endomorphisms.
No nontriviality assumption is imposed on the space, so the norm of the identity
is only bounded by one, rather than assumed equal to one. -/
noncomputable section
namespace Grad.Foundations
variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- The norm-convergent geometric series when `‖T‖ < 1`. -/
def neumannInverse (T : X →L[𝕜] X) : X →L[𝕜] X := ∑' n : ℕ, T ^ n

theorem neumannInverse_hasSum (T : X →L[𝕜] X) (hT : ‖T‖ < 1) :
    HasSum (fun n : ℕ => T ^ n) (neumannInverse T) :=
  (summable_geometric_of_norm_lt_one hT).hasSum

/-- The reference inverse at zero perturbation is the identity. -/
@[simp] theorem neumannInverse_zero : neumannInverse (0 : X →L[𝕜] X) = 1 := by
  simpa [neumannInverse] using geom_series_mul_neg (0 : X →L[𝕜] X) (by simp)

theorem neumannInverse_left (T : X →L[𝕜] X) (hT : ‖T‖ < 1) :
    (neumannInverse T).comp (1 - T) = 1 := geom_series_mul_neg T hT

theorem neumannInverse_right (T : X →L[𝕜] X) (hT : ‖T‖ < 1) :
    (1 - T).comp (neumannInverse T) = 1 := mul_neg_geom_series T hT

omit [CompleteSpace X] in
theorem neumannInverse_norm (T : X →L[𝕜] X) (hT : ‖T‖ < 1) :
    ‖neumannInverse T‖ ≤ (1 - ‖T‖)⁻¹ := by
  have h := tsum_geometric_le_of_norm_lt_one T hT
  have hi : ‖(1 : X →L[𝕜] X)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  change ‖neumannInverse T‖ ≤ _ at h
  linarith

omit [CompleteSpace X] in
theorem neumannInverse_norm_of_le (T : X →L[𝕜] X) {q : ℝ}
    (hT : ‖T‖ ≤ q) (hq : q < 1) : ‖neumannInverse T‖ ≤ (1 - q)⁻¹ := by
  apply (neumannInverse_norm T (hT.trans_lt hq)).trans
  simpa only [one_div] using one_div_le_one_div_of_le (sub_pos.mpr hq) (sub_le_sub_left hT 1)

end Grad.Foundations
