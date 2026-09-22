import AKAB4UniformWeightedShellError

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Grad.WeightedAxisRemoval
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularCurrentLow

theorem collarMode_shell_memLp {dimension : ℕ} (lower epsilon : ℝ)
    (included : lower ≤ epsilon) (bounded : 2 * epsilon ≤ 1)
    (field : DivisionRow dimension lower) (mode : ℤ × ℤ) :
    MemLp (fun radius => field mode radius) 2 (volume.restrict (Ioc epsilon (2 * epsilon))) := by
  have subset : Ioc epsilon (2 * epsilon) ⊆ Icc lower 1 :=
    fun _ inside => ⟨included.trans inside.1.le, inside.2.trans bounded⟩
  exact (Lp.memLp (field mode)).mono_measure (Measure.restrict_mono subset le_rfl)

theorem collarMode_shell_energy {dimension : ℕ} (lower epsilon : ℝ)
    (included : lower ≤ epsilon) (bounded : 2 * epsilon ≤ 1)
    (field : DivisionRow dimension lower) (mode : ℤ × ℤ)
    (K : ℝ) (estimate : ‖field‖ ≤ K) :
    (∫ radius in Ioc epsilon (2 * epsilon), ‖field mode radius‖ ^ 2) ≤ K ^ 2 := by
  have subset : Ioc epsilon (2 * epsilon) ⊆ Icc lower 1 :=
    fun _ inside => ⟨included.trans inside.1.le, inside.2.trans bounded⟩
  have modeBound := (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) field mode).trans estimate
  calc
    _ ≤ ∫ radius in Icc lower 1, ‖field mode radius‖ ^ 2 :=
      integral_mono_measure (Measure.restrict_mono subset le_rfl)
        (Eventually.of_forall (fun _ => sq_nonneg _)) (Lp.memLp (field mode)).norm.integrable_sq
    _ = ‖field mode‖ ^ 2 := (radialLp_norm_sq lower (field mode)).symm
    _ ≤ K ^ 2 := (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans modeBound)).mpr modeBound

/-- The actual original weighted collar coefficient supplies the ER2
error estimate. Uniform original bulk norms therefore give a bound
independent of the chosen inner collar and of epsilon. -/
theorem originalPhysicalCoefficient_shell_error {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {dimension : ℕ} (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (epsilon : ℝ) (included : lower ≤ epsilon) (bounded : 2 * epsilon ≤ 1)
    (field : DivisionRow dimension lower) (mode : ℤ × ℤ)
    (constant K : ℝ) (constantNonnegative : 0 ≤ constant) (estimate : ‖field‖ ≤ K)
    (error : ℝ → E)
    (measurable : AEStronglyMeasurable error (volume.restrict (Ioc epsilon (2 * epsilon))))
    (pointwise : ∀ᵐ radius ∂volume.restrict (Ioc epsilon (2 * epsilon)),
      ‖error radius‖ ≤ constant * ((epsilon⁻¹ * radius) *
        ‖lowRhoPhysicalCoefficient parameters lower positive field radius mode‖)) :
    ‖∫ radius in Ioc epsilon (2 * epsilon), error radius‖ ≤
      (constant * (2 * (2 : ℝ) ^ (7 / 4 : ℝ)) * K) * epsilon ^ (9 / 4 : ℝ) := by
  apply weightedAxisShellError_uniform_bound epsilon (positive.trans_le included) constant K
    constantNonnegative ((norm_nonneg _).trans estimate) (fun radius => field mode radius) error
    (collarMode_shell_memLp lower epsilon included bounded field mode)
    (collarMode_shell_energy lower epsilon included bounded field mode K estimate) measurable
  filter_upwards [pointwise,ae_restrict_mem measurableSet_Ioc] with radius bound inside
  have collar : radius ∈ Icc lower 1 := ⟨included.trans inside.1.le,inside.2.trans bounded⟩
  have coefficient := lowRhoPhysicalCoefficient_norm_bound parameters lower positive field radius collar mode
  exact bound.trans ((mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left coefficient (mul_nonneg (inv_nonneg.mpr (positive.trans_le included).le)
      (positive.trans_le collar.1).le)) constantNonnegative).trans_eq (by ring))

end Grad.WeightedAxisRemoval
