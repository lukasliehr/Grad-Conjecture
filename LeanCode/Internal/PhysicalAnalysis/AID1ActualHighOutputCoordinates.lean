import AIA14ActualCircleReferenceIdentity
import ADW6LiteralOmegaDenseConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentGreen
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularCircularForm

/-- Restriction of the complete full Fourier output to the original high set. -/
def highFullRestrictionValue (lower : ℝ) (field : DivisionRow 1 lower) : AnnularBulk lower :=
  ⟨fun mode => field mode.val, by
    apply memℓp_gen
    exact (field.property.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).comp_injective Subtype.val_injective⟩

theorem highFullRestrictionValue_bound (lower : ℝ) (field : DivisionRow 1 lower) :
    ‖highFullRestrictionValue lower field‖ ≤ ‖field‖ := by
  have left := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (highFullRestrictionValue lower field)
  have right := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at left right
  have summable : Summable (fun mode : ℤ × ℤ => ‖field mode‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using field.property.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
  have comparison := tsum_comp_le_tsum_of_inj summable (fun index => sq_nonneg ‖field index‖)
    (Subtype.val_injective : Function.Injective (fun mode : HighAnnularMode => mode.val))
  change (∑' mode : HighAnnularMode, ‖field mode.val‖ ^ 2) ≤ ∑' mode : ℤ × ℤ, ‖field mode‖ ^ 2 at comparison
  rw [← right] at comparison
  have firstSquare : ‖highFullRestrictionValue lower field‖ ^ 2 = ∑' mode : HighAnnularMode, ‖field mode.val‖ ^ 2 := left
  rw [← firstSquare] at comparison
  nlinarith [norm_nonneg (highFullRestrictionValue lower field), norm_nonneg field]

def highFullRestriction (lower : ℝ) : DivisionRow 1 lower →L[ℂ] AnnularBulk lower :=
  LinearMap.mkContinuous
    { toFun := highFullRestrictionValue lower
      map_add' := fun _ _ => by apply lp.ext; funext mode; rfl
      map_smul' := fun _ _ => by apply lp.ext; funext mode; rfl }
    1 (fun field => by
      change ‖highFullRestrictionValue lower field‖ ≤ 1 * ‖field‖
      rw [one_mul]
      exact highFullRestrictionValue_bound lower field)

theorem highFullRestriction_apply (lower : ℝ) (field : DivisionRow 1 lower) (mode : HighAnnularMode) :
    highFullRestriction lower field mode = field mode.val := rfl

/-- Literal scalar output of the actual completed vector packet. -/
def highPhysicalOutput {dimension : ℕ} (lower : ℝ) (slot : Fin dimension) :
    DivisionRow dimension lower →L[ℂ] AnnularBulk lower :=
  (highFullRestriction lower).comp (bulkMatrixUnit lower 0 slot)

theorem highPhysicalOutput_bound {dimension : ℕ} (lower : ℝ) (slot : Fin dimension)
    (field : DivisionRow dimension lower) : ‖highPhysicalOutput lower slot field‖ ≤ ‖field‖ :=
  (highFullRestrictionValue_bound lower (bulkMatrixUnit lower 0 slot field)).trans
    (bulkMatrixUnit_bound lower 0 slot field)

theorem highPhysicalOutput_ae {dimension : ℕ} (lower : ℝ) (slot : Fin dimension)
    (field : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : HighAnnularMode,
      highPhysicalOutput lower slot field mode radius =
        (field mode.val radius slot) • Grad.GaugeCoefficients.Physical.Ledger.operatorBasis 0 := by
  filter_upwards [bulkMatrixUnit_ae lower (0 : Fin 1) slot field] with radius actual
  intro mode
  exact actual mode.val

end Grad.AnnularCurrentGreen
