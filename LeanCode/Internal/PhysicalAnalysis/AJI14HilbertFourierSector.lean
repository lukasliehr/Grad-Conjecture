import AJI13HilbertRadialDerivative
import AJF41LiteralInsertedDecode

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped ENNReal
namespace Grad.AnnularSmoothCore

variable {Index E : Type*} [NormedAddCommGroup E]
    (sector : Index → Prop) [DecidablePred sector]

def hilbertSectorExtensionValue (field : lp (fun _ : {index // sector index} => E) 2) (index : Index) : E :=
  if inside : sector index then field ⟨index, inside⟩ else 0

theorem hilbertSectorExtensionValue_inside (field : lp (fun _ : {index // sector index} => E) 2)
    (index : {index // sector index}) : hilbertSectorExtensionValue sector field index.val = field index := by
  simp [hilbertSectorExtensionValue, index.property]

def hilbertSectorExtension (field : lp (fun _ : {index // sector index} => E) 2) : lp (fun _ : Index => E) 2 :=
  ⟨hilbertSectorExtensionValue sector field, by
    apply memℓp_gen
    apply (Function.Injective.summable_iff (g := fun index : {index // sector index} => index.val)
      Subtype.val_injective ?_).mp
    · simpa only [Function.comp_def, hilbertSectorExtensionValue_inside] using
        field.property.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    · intro index outside
      have notInside : ¬ sector index := fun inside => outside ⟨⟨index, inside⟩, rfl⟩
      simp [hilbertSectorExtensionValue, notInside]⟩

theorem hilbertSectorExtension_norm (field : lp (fun _ : {index // sector index} => E) 2) :
    ‖hilbertSectorExtension sector field‖ = ‖field‖ := by
  have left := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (hilbertSectorExtension sector field)
  have right := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at left right
  have support : Function.support (fun index => ‖hilbertSectorExtension sector field index‖ ^ 2) ⊆ {index | sector index} := by
    intro index inside
    by_contra outside
    change ¬ sector index at outside
    apply inside
    change ‖hilbertSectorExtensionValue sector field index‖ ^ 2 = 0
    simp [hilbertSectorExtensionValue, outside]
  have sum := tsum_subtype_eq_of_support_subset support
  change (∑' index : {index // sector index}, ‖hilbertSectorExtensionValue sector field index.val‖ ^ 2) = _ at sum
  simp only [hilbertSectorExtensionValue_inside] at sum
  rw [← left, ← right] at sum
  nlinarith [norm_nonneg (hilbertSectorExtension sector field), norm_nonneg field]

variable [NormedSpace ℂ E]

def hilbertSectorIntoFull : lp (fun _ : {index // sector index} => E) 2 →ₗᵢ[ℂ] lp (fun _ : Index => E) 2 where
  toLinearMap :=
    { toFun := hilbertSectorExtension sector
      map_add' := by
        intro first second
        apply lp.ext
        funext index
        change hilbertSectorExtensionValue sector (first + second) index =
          hilbertSectorExtensionValue sector first index + hilbertSectorExtensionValue sector second index
        by_cases inside : sector index <;> simp [hilbertSectorExtensionValue, inside]
      map_smul' := by
        intro scalar field
        apply lp.ext
        funext index
        change hilbertSectorExtensionValue sector (scalar • field) index =
          scalar • hilbertSectorExtensionValue sector field index
        by_cases inside : sector index <;> simp [hilbertSectorExtensionValue, inside] }
  norm_map' := hilbertSectorExtension_norm sector

theorem hilbertSectorIntoFull_inside (field : lp (fun _ : {index // sector index} => E) 2)
    (index : {index // sector index}) : hilbertSectorIntoFull sector field index.val = field index :=
  hilbertSectorExtensionValue_inside sector field index

theorem hilbertSectorIntoFull_outside (field : lp (fun _ : {index // sector index} => E) 2)
    (index : Index) (outside : ¬ sector index) : hilbertSectorIntoFull sector field index = 0 := by
  change hilbertSectorExtensionValue sector field index = 0
  simp [hilbertSectorExtensionValue, outside]

end Grad.AnnularSmoothCore
