import AEM12UniformOriginalBoundaryCross
import ADW3LiteralClosedOmegaGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction

/-- Restriction of the complete full Fourier output to the original high set. -/
def crossHighRestrictionValue (lower : ℝ) (field : DivisionRow 1 lower) : AnnularBulk lower :=
  ⟨fun mode => field mode.val, by
    apply memℓp_gen
    exact (field.property.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).comp_injective Subtype.val_injective⟩

theorem crossHighRestrictionValue_bound (lower : ℝ) (field : DivisionRow 1 lower) :
    ‖crossHighRestrictionValue lower field‖ ≤ ‖field‖ := by
  have left := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (crossHighRestrictionValue lower field)
  have right := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at left right
  have summable : Summable (fun mode : ℤ × ℤ => ‖field mode‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using field.property.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
  have comparison := tsum_comp_le_tsum_of_inj summable (fun index => sq_nonneg ‖field index‖)
    (Subtype.val_injective : Function.Injective (fun mode : HighAnnularMode => mode.val))
  change (∑' mode : HighAnnularMode, ‖field mode.val‖ ^ 2) ≤ ∑' mode : ℤ × ℤ, ‖field mode‖ ^ 2 at comparison
  rw [← right] at comparison
  have firstSquare : ‖crossHighRestrictionValue lower field‖ ^ 2 = ∑' mode : HighAnnularMode, ‖field mode.val‖ ^ 2 := left
  rw [← firstSquare] at comparison
  nlinarith [norm_nonneg (crossHighRestrictionValue lower field), norm_nonneg field]

def crossHighRestriction (lower : ℝ) : DivisionRow 1 lower →L[ℂ] AnnularBulk lower :=
  LinearMap.mkContinuous
    { toFun := crossHighRestrictionValue lower
      map_add' := fun _ _ => by apply lp.ext; funext mode; rfl
      map_smul' := fun _ _ => by apply lp.ext; funext mode; rfl }
    1 (fun field => by
      change ‖crossHighRestrictionValue lower field‖ ≤ 1 * ‖field‖
      rw [one_mul]
      exact crossHighRestrictionValue_bound lower field)

theorem crossHighRestriction_apply (lower : ℝ) (field : DivisionRow 1 lower) (mode : HighAnnularMode) :
    crossHighRestriction lower field mode = field mode.val := rfl

end Grad.AnnularCrossMaps
