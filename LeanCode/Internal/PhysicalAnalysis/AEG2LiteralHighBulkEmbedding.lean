import AEG1UniformHighPhysicalCoordinates
import AHU13EvaluatedOneHighErrorConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentEnergy
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational

/-- High Fourier coefficients inserted in the full physical mode space;
all complementary coefficients are exactly zero. -/
def highBulkExtensionValue (lower : ℝ) (field : AnnularBulk lower)
    (mode : ℤ × ℤ) : RadialL2 1 lower :=
  if high : 3 ≤ |mode.1| then field ⟨mode, high⟩ else 0

theorem highBulkExtensionValue_high (lower : ℝ) (field : AnnularBulk lower)
    (mode : HighAnnularMode) : highBulkExtensionValue lower field mode.val = field mode := by
  simp [highBulkExtensionValue, mode.property]

theorem highBulkExtensionValue_low (lower : ℝ) (field : AnnularBulk lower)
    (mode : ℤ × ℤ) (low : ¬ 3 ≤ |mode.1|) : highBulkExtensionValue lower field mode = 0 := by
  simp [highBulkExtensionValue, low]

theorem highBulkExtension_mem (lower : ℝ) (field : AnnularBulk lower) :
    Memℓp (highBulkExtensionValue lower field) 2 := by
  apply memℓp_gen
  apply (Function.Injective.summable_iff (g := fun mode : HighAnnularMode => mode.val)
    Subtype.val_injective ?_).mp
  · simpa only [Function.comp_def, highBulkExtensionValue_high] using
      field.property.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
  · intro mode outside
    have low : ¬ 3 ≤ |mode.1| := by
      intro high
      exact outside ⟨⟨mode, high⟩, rfl⟩
    simp [highBulkExtensionValue_low lower field mode low]

def highBulkExtension (lower : ℝ) (field : AnnularBulk lower) : DivisionRow 1 lower :=
  ⟨highBulkExtensionValue lower field, highBulkExtension_mem lower field⟩

theorem highBulkExtension_norm (lower : ℝ) (field : AnnularBulk lower) :
    ‖highBulkExtension lower field‖ = ‖field‖ := by
  have equality : ‖highBulkExtension lower field‖ ^ 2 = ‖field‖ ^ 2 := by
    have left := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (highBulkExtension lower field)
    have right := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at left right
    rw [left, right]
    symm
    have support : Function.support (fun mode => ‖highBulkExtension lower field mode‖ ^ 2) ⊆
        {mode : ℤ × ℤ | 3 ≤ |mode.1|} := by
      intro mode inside
      by_contra low
      apply inside
      change ‖highBulkExtensionValue lower field mode‖ ^ 2 = 0
      simp [highBulkExtensionValue_low lower field mode low]
    have result := tsum_subtype_eq_of_support_subset support
    change (∑' mode : HighAnnularMode, ‖highBulkExtensionValue lower field mode.val‖ ^ 2) = _ at result
    simpa only [highBulkExtensionValue_high] using result
  nlinarith [norm_nonneg (highBulkExtension lower field), norm_nonneg field]

def highBulkIntoFull (lower : ℝ) : AnnularBulk lower →ₗᵢ[ℂ] DivisionRow 1 lower where
  toLinearMap :=
    { toFun := highBulkExtension lower
      map_add' := by
        intro first second
        apply lp.ext
        funext mode
        change highBulkExtensionValue lower (first + second) mode =
          highBulkExtensionValue lower first mode + highBulkExtensionValue lower second mode
        by_cases high : 3 ≤ |mode.1|
        · simp [highBulkExtensionValue, high]
        · simp [highBulkExtensionValue, high]
      map_smul' := by
        intro scalar field
        apply lp.ext
        funext mode
        by_cases high : 3 ≤ |mode.1|
        · simp [highBulkExtension, highBulkExtensionValue, high]
        · simp [highBulkExtension, highBulkExtensionValue, high] }
  norm_map' := highBulkExtension_norm lower

theorem highBulkIntoFull_high (lower : ℝ) (field : AnnularBulk lower) (mode : HighAnnularMode) :
    highBulkIntoFull lower field mode.val = field mode := highBulkExtensionValue_high lower field mode

theorem highBulkIntoFull_low (lower : ℝ) (field : AnnularBulk lower) (mode : ℤ × ℤ)
    (low : ¬ 3 ≤ |mode.1|) : highBulkIntoFull lower field mode = 0 :=
  highBulkExtensionValue_low lower field mode low

end Grad.AnnularCurrentEnergy
