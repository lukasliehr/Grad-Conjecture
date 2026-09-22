import AEI6ExactLowInputCoefficientLaws

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction

/-- Restriction of the complete full Fourier output to the original low set. -/
def lowFullRestrictionValue (lower : ℝ) (field : DivisionRow 1 lower) : LowModeBulk lower :=
  ⟨fun mode => field mode.val, by
    apply memℓp_gen
    exact (field.property.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).comp_injective Subtype.val_injective⟩

theorem lowFullRestrictionValue_bound (lower : ℝ) (field : DivisionRow 1 lower) :
    ‖lowFullRestrictionValue lower field‖ ≤ ‖field‖ := by
  have left := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (lowFullRestrictionValue lower field)
  have right := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at left right
  have summable : Summable (fun mode : ℤ × ℤ => ‖field mode‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using field.property.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
  have comparison := tsum_comp_le_tsum_of_inj summable (fun index => sq_nonneg ‖field index‖)
    (Subtype.val_injective : Function.Injective (fun mode : LowAnnularMode => mode.val))
  change (∑' mode : LowAnnularMode, ‖field mode.val‖ ^ 2) ≤ ∑' mode : ℤ × ℤ, ‖field mode‖ ^ 2 at comparison
  rw [← right] at comparison
  have firstSquare : ‖lowFullRestrictionValue lower field‖ ^ 2 = ∑' mode : LowAnnularMode, ‖field mode.val‖ ^ 2 := left
  rw [← firstSquare] at comparison
  nlinarith [norm_nonneg (lowFullRestrictionValue lower field), norm_nonneg field]

def lowFullRestriction (lower : ℝ) : DivisionRow 1 lower →L[ℂ] LowModeBulk lower :=
  LinearMap.mkContinuous
    { toFun := lowFullRestrictionValue lower
      map_add' := fun _ _ => by apply lp.ext; funext mode; rfl
      map_smul' := fun _ _ => by apply lp.ext; funext mode; rfl }
    1 (fun field => by
      change ‖lowFullRestrictionValue lower field‖ ≤ 1 * ‖field‖
      rw [one_mul]
      exact lowFullRestrictionValue_bound lower field)

theorem lowFullRestriction_apply (lower : ℝ) (field : DivisionRow 1 lower) (mode : LowAnnularMode) :
    lowFullRestriction lower field mode = field mode.val := rfl

def lowRowExtensionValue (lower : ℝ) (row : Fin 2) (field : LowModeBulk lower) (index : LowAnnularIndex) : RadialL2 1 lower :=
  if index.1 = row then field index.2 else 0

theorem lowRowExtensionValue_same (lower : ℝ) (row : Fin 2) (field : LowModeBulk lower) (mode : LowAnnularMode) :
    lowRowExtensionValue lower row field (row, mode) = field mode := by simp [lowRowExtensionValue]

def lowRowExtension (lower : ℝ) (row : Fin 2) (field : LowModeBulk lower) : LowEnergyBulk lower :=
  ⟨lowRowExtensionValue lower row field, by
    apply memℓp_gen
    apply (Function.Injective.summable_iff (g := fun mode : LowAnnularMode => (row, mode))
      (fun _ _ same => (Prod.mk.inj same).2) ?_).mp
    · simpa only [Function.comp_def, lowRowExtensionValue_same] using
        field.property.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    · intro index outside
      have different : index.1 ≠ row := by
        intro same
        exact outside ⟨index.2, Prod.ext same.symm rfl⟩
      simp [lowRowExtensionValue, different]⟩

def lowRowIndexEquiv (row : Fin 2) : {index : LowAnnularIndex // index.1 = row} ≃ LowAnnularMode where
  toFun index := index.val.2
  invFun mode := ⟨(row, mode), rfl⟩
  left_inv index := by apply Subtype.ext; exact Prod.ext index.property.symm rfl
  right_inv _ := rfl

theorem lowRowExtension_norm (lower : ℝ) (row : Fin 2) (field : LowModeBulk lower) :
    ‖lowRowExtension lower row field‖ = ‖field‖ := by
  have left := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (lowRowExtension lower row field)
  have right := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at left right
  have support : Function.support (fun index => ‖lowRowExtension lower row field index‖ ^ 2) ⊆
      {index : LowAnnularIndex | index.1 = row} := by
    intro index member
    by_contra different
    apply member
    change ‖lowRowExtensionValue lower row field index‖ ^ 2 = 0
    change index.1 ≠ row at different
    rw [lowRowExtensionValue, if_neg different, norm_zero, zero_pow (by norm_num)]
  have sums : (∑' index : LowAnnularIndex, ‖lowRowExtension lower row field index‖ ^ 2) =
      ∑' mode : LowAnnularMode, ‖field mode‖ ^ 2 := by
    rw [← tsum_subtype_eq_of_support_subset support]
    calc
      _ = ∑' index : {index : LowAnnularIndex // index.1 = row}, ‖field index.val.2‖ ^ 2 := by
        apply tsum_congr
        intro index
        change ‖lowRowExtensionValue lower row field index.val‖ ^ 2 = _
        have same : index.val.1 = row := index.property
        rw [lowRowExtensionValue, if_pos same]
      _ = _ := (lowRowIndexEquiv row).tsum_eq (fun mode => ‖field mode‖ ^ 2)
  have square := left.trans (sums.trans right.symm)
  nlinarith [norm_nonneg (lowRowExtension lower row field), norm_nonneg field]

def lowRowIntoBulk (lower : ℝ) (row : Fin 2) : LowModeBulk lower →ₗᵢ[ℂ] LowEnergyBulk lower where
  toLinearMap :=
    { toFun := lowRowExtension lower row
      map_add' := by
        intro first second
        apply lp.ext
        funext index
        change lowRowExtensionValue lower row (first + second) index =
          lowRowExtensionValue lower row first index + lowRowExtensionValue lower row second index
        by_cases same : index.1 = row <;> simp [lowRowExtensionValue, same]
      map_smul' := by
        intro scalar field
        apply lp.ext
        funext index
        change lowRowExtensionValue lower row (scalar • field) index = scalar • lowRowExtensionValue lower row field index
        by_cases same : index.1 = row <;> simp [lowRowExtensionValue, same] }
  norm_map' := lowRowExtension_norm lower row

end Grad.AnnularCurrentLow
