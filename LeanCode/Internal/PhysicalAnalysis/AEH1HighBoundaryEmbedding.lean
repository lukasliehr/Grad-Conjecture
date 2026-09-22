import AEF11UniformHighReferenceConsumer
import AHV10FrozenOriginalOuterInverseReuse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
open scoped BigOperators ENNReal

namespace Grad.AnnularCurrentBoundary

open Grad.ClosedJets Grad.AnnularVariational Grad.BoundaryKernelAction

/-- High Fourier boundary coefficients inserted in the complete physical
two-frequency trace space; every complementary coefficient is zero. -/
def highBoundaryExtensionValue (field : AnnularBoundary)
    (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  if high : 3 ≤ |mode.1| then field ⟨mode, high⟩ else 0

theorem highBoundaryExtensionValue_high (field : AnnularBoundary)
    (mode : HighAnnularMode) :
    highBoundaryExtensionValue field mode.val = field mode := by
  simp [highBoundaryExtensionValue, mode.property]

theorem highBoundaryExtensionValue_low (field : AnnularBoundary)
    (mode : ℤ × ℤ) (low : ¬ 3 ≤ |mode.1|) :
    highBoundaryExtensionValue field mode = 0 := by
  simp [highBoundaryExtensionValue, low]

theorem highBoundaryExtension_mem (field : AnnularBoundary) :
    Memℓp (highBoundaryExtensionValue field) 2 := by
  apply memℓp_gen
  apply (Function.Injective.summable_iff (g := fun mode : HighAnnularMode => mode.val)
    Subtype.val_injective ?_).mp
  · simpa only [Function.comp_def, highBoundaryExtensionValue_high] using
      field.property.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
  · intro mode outside
    have low : ¬ 3 ≤ |mode.1| := by
      intro high
      exact outside ⟨⟨mode, high⟩, rfl⟩
    simp [highBoundaryExtensionValue_low field mode low]

def highBoundaryExtension (parameters : Grad.CartesianState.PhaseParameters)
    (angular cell : ℕ) (field : AnnularBoundary) :
    PositiveTrace parameters angular cell 1 :=
  ⟨highBoundaryExtensionValue field, highBoundaryExtension_mem field⟩

theorem highBoundaryExtension_norm
    (parameters : Grad.CartesianState.PhaseParameters) (angular cell : ℕ)
    (field : AnnularBoundary) :
    ‖highBoundaryExtension parameters angular cell field‖ = ‖field‖ := by
  have equality : ‖highBoundaryExtension parameters angular cell field‖ ^ 2 =
      ‖field‖ ^ 2 := by
    have left := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
      (highBoundaryExtension parameters angular cell field)
    have right := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at left right
    rw [left, right]
    symm
    have support : Function.support
        (fun mode => ‖highBoundaryExtension parameters angular cell field mode‖ ^ 2) ⊆
        {mode : ℤ × ℤ | 3 ≤ |mode.1|} := by
      intro mode inside
      by_contra low
      apply inside
      change ‖highBoundaryExtensionValue field mode‖ ^ 2 = 0
      simp [highBoundaryExtensionValue_low field mode low]
    have result := tsum_subtype_eq_of_support_subset support
    change (∑' mode : HighAnnularMode,
      ‖highBoundaryExtensionValue field mode.val‖ ^ 2) = _ at result
    simpa only [highBoundaryExtensionValue_high] using result
  nlinarith [norm_nonneg (highBoundaryExtension parameters angular cell field),
    norm_nonneg field]

/-- Isometric zero extension from the actual high annular trace to the
complete AH16 positive-half trace coordinates. -/
def highBoundaryIntoPositive
    (parameters : Grad.CartesianState.PhaseParameters) (angular cell : ℕ) :
    AnnularBoundary →ₗᵢ[ℂ] PositiveTrace parameters angular cell 1 where
  toLinearMap :=
    { toFun := highBoundaryExtension parameters angular cell
      map_add' := by
        intro first second
        apply lp.ext
        funext mode
        change highBoundaryExtensionValue (first + second) mode =
          highBoundaryExtensionValue first mode + highBoundaryExtensionValue second mode
        by_cases high : 3 ≤ |mode.1|
        · simp [highBoundaryExtensionValue, high]
        · simp [highBoundaryExtensionValue, high]
      map_smul' := by
        intro scalar field
        apply lp.ext
        funext mode
        by_cases high : 3 ≤ |mode.1|
        · simp [highBoundaryExtension, highBoundaryExtensionValue, high]
        · simp [highBoundaryExtension, highBoundaryExtensionValue, high] }
  norm_map' := highBoundaryExtension_norm parameters angular cell

theorem highBoundaryIntoPositive_high
    (parameters : Grad.CartesianState.PhaseParameters) (angular cell : ℕ)
    (field : AnnularBoundary) (mode : HighAnnularMode) :
    highBoundaryIntoPositive parameters angular cell field mode.val = field mode :=
  highBoundaryExtensionValue_high field mode

theorem highBoundaryIntoPositive_low
    (parameters : Grad.CartesianState.PhaseParameters) (angular cell : ℕ)
    (field : AnnularBoundary) (mode : ℤ × ℤ) (low : ¬ 3 ≤ |mode.1|) :
    highBoundaryIntoPositive parameters angular cell field mode = 0 :=
  highBoundaryExtensionValue_low field mode low

end Grad.AnnularCurrentBoundary
