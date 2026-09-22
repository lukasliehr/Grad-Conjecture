import AEI2OriginalLowComponentRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational Grad.AnnularLowEnergy

/-- Low Fourier coefficients inserted in the full physical mode space;
all complementary coefficients are exactly zero. -/
def lowBulkExtensionValue (lower : ℝ) (field : LowModeBulk lower)
    (mode : ℤ × ℤ) : RadialL2 1 lower :=
  if low : (|mode.1| = 1 ∨ |mode.1| = 2) then field ⟨mode, low⟩ else 0

theorem lowBulkExtensionValue_retained (lower : ℝ) (field : LowModeBulk lower)
    (mode : LowAnnularMode) : lowBulkExtensionValue lower field mode.val = field mode := by
  simp [lowBulkExtensionValue, mode.property]

theorem lowBulkExtensionValue_outside (lower : ℝ) (field : LowModeBulk lower)
    (mode : ℤ × ℤ) (low : ¬ (|mode.1| = 1 ∨ |mode.1| = 2)) : lowBulkExtensionValue lower field mode = 0 := by
  simp [lowBulkExtensionValue, low]

theorem lowBulkExtension_mem (lower : ℝ) (field : LowModeBulk lower) :
    Memℓp (lowBulkExtensionValue lower field) 2 := by
  apply memℓp_gen
  apply (Function.Injective.summable_iff (g := fun mode : LowAnnularMode => mode.val)
    Subtype.val_injective ?_).mp
  · simpa only [Function.comp_def, lowBulkExtensionValue_retained] using
      field.property.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
  · intro mode outside
    have low : ¬ (|mode.1| = 1 ∨ |mode.1| = 2) := by
      intro retained
      exact outside ⟨⟨mode, retained⟩, rfl⟩
    simp [lowBulkExtensionValue_outside lower field mode low]

def lowBulkExtension (lower : ℝ) (field : LowModeBulk lower) : DivisionRow 1 lower :=
  ⟨lowBulkExtensionValue lower field, lowBulkExtension_mem lower field⟩

theorem lowBulkExtension_norm (lower : ℝ) (field : LowModeBulk lower) :
    ‖lowBulkExtension lower field‖ = ‖field‖ := by
  have equality : ‖lowBulkExtension lower field‖ ^ 2 = ‖field‖ ^ 2 := by
    have left := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (lowBulkExtension lower field)
    have right := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at left right
    rw [left, right]
    symm
    have support : Function.support (fun mode => ‖lowBulkExtension lower field mode‖ ^ 2) ⊆
        {mode : ℤ × ℤ | (|mode.1| = 1 ∨ |mode.1| = 2)} := by
      intro mode inside
      by_contra low
      apply inside
      change ‖lowBulkExtensionValue lower field mode‖ ^ 2 = 0
      simp [lowBulkExtensionValue_outside lower field mode low]
    have result := tsum_subtype_eq_of_support_subset support
    change (∑' mode : LowAnnularMode, ‖lowBulkExtensionValue lower field mode.val‖ ^ 2) = _ at result
    simpa only [lowBulkExtensionValue_retained] using result
  nlinarith [norm_nonneg (lowBulkExtension lower field), norm_nonneg field]

def lowBulkIntoFull (lower : ℝ) : LowModeBulk lower →ₗᵢ[ℂ] DivisionRow 1 lower where
  toLinearMap :=
    { toFun := lowBulkExtension lower
      map_add' := by
        intro first second
        apply lp.ext
        funext mode
        change lowBulkExtensionValue lower (first + second) mode =
          lowBulkExtensionValue lower first mode + lowBulkExtensionValue lower second mode
        by_cases low : (|mode.1| = 1 ∨ |mode.1| = 2)
        · simp [lowBulkExtensionValue, low]
        · simp [lowBulkExtensionValue, low]
      map_smul' := by
        intro scalar field
        apply lp.ext
        funext mode
        by_cases low : (|mode.1| = 1 ∨ |mode.1| = 2)
        · simp [lowBulkExtension, lowBulkExtensionValue, low]
        · simp [lowBulkExtension, lowBulkExtensionValue, low] }
  norm_map' := lowBulkExtension_norm lower

theorem lowBulkIntoFull_retained (lower : ℝ) (field : LowModeBulk lower) (mode : LowAnnularMode) :
    lowBulkIntoFull lower field mode.val = field mode := lowBulkExtensionValue_retained lower field mode

theorem lowBulkIntoFull_outside (lower : ℝ) (field : LowModeBulk lower) (mode : ℤ × ℤ)
    (low : ¬ (|mode.1| = 1 ∨ |mode.1| = 2)) : lowBulkIntoFull lower field mode = 0 :=
  lowBulkExtensionValue_outside lower field mode low

end Grad.AnnularCurrentLow
