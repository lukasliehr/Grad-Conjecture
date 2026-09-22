import AEM6LiteralLowOuterHalfWeights

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction

abbrev LowModeBoundary := lp (fun _ : LowAnnularMode => ComplexEuclidean 1) 2

def lowBoundaryComponentValue (row : Fin 2) (field : LowEnergyBoundary) : LowModeBoundary :=
  ⟨fun mode => field (row, mode), by
    apply memℓp_gen
    exact (field.property.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).comp_injective
      (fun _ _ same => (Prod.mk.inj same).2)⟩

theorem lowBoundaryComponentValue_bound (row : Fin 2) (field : LowEnergyBoundary) :
    ‖lowBoundaryComponentValue row field‖ ≤ ‖field‖ := by
  have left := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (lowBoundaryComponentValue row field)
  have right := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at left right
  have squareSum := lowLp_summable_norm_sq field
  have comparison := tsum_comp_le_tsum_of_inj squareSum (fun index => sq_nonneg ‖field index‖)
    (fun _ _ same => (Prod.mk.inj same).2 : Function.Injective (fun mode : LowAnnularMode => (row, mode)))
  change (∑' mode : LowAnnularMode, ‖field (row, mode)‖ ^ 2) ≤ ∑' index : LowAnnularIndex, ‖field index‖ ^ 2 at comparison
  rw [← right] at comparison
  have firstSquare : ‖lowBoundaryComponentValue row field‖ ^ 2 = ∑' mode : LowAnnularMode, ‖field (row, mode)‖ ^ 2 := left
  rw [← firstSquare] at comparison
  nlinarith [norm_nonneg (lowBoundaryComponentValue row field), norm_nonneg field]

def lowBoundaryComponent (row : Fin 2) : LowEnergyBoundary →L[ℂ] LowModeBoundary :=
  LinearMap.mkContinuous
    { toFun := lowBoundaryComponentValue row
      map_add' := fun _ _ => by apply lp.ext; funext mode; rfl
      map_smul' := fun _ _ => by apply lp.ext; funext mode; rfl }
    1 (fun field => by
      change ‖lowBoundaryComponentValue row field‖ ≤ 1 * ‖field‖
      rw [one_mul]
      exact lowBoundaryComponentValue_bound row field)

theorem lowBoundaryComponent_apply (row : Fin 2) (field : LowEnergyBoundary) (mode : LowAnnularMode) :
    lowBoundaryComponent row field mode = field (row, mode) := rfl

theorem lowBoundaryComponent_bound (row : Fin 2) (field : LowEnergyBoundary) :
    ‖lowBoundaryComponent row field‖ ≤ ‖field‖ := lowBoundaryComponentValue_bound row field

/-- Low Fourier coefficients inserted in the full physical mode space;
all complementary coefficients are exactly zero. -/
def lowBoundaryExtensionValue (field : LowModeBoundary)
    (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  if low : (|mode.1| = 1 ∨ |mode.1| = 2) then field ⟨mode, low⟩ else 0

theorem lowBoundaryExtensionValue_retained (field : LowModeBoundary)
    (mode : LowAnnularMode) : lowBoundaryExtensionValue field mode.val = field mode := by
  simp [lowBoundaryExtensionValue, mode.property]

theorem lowBoundaryExtensionValue_outside (field : LowModeBoundary)
    (mode : ℤ × ℤ) (low : ¬ (|mode.1| = 1 ∨ |mode.1| = 2)) : lowBoundaryExtensionValue field mode = 0 := by
  simp [lowBoundaryExtensionValue, low]

theorem lowBoundaryExtension_mem (field : LowModeBoundary) :
    Memℓp (lowBoundaryExtensionValue field) 2 := by
  apply memℓp_gen
  apply (Function.Injective.summable_iff (g := fun mode : LowAnnularMode => mode.val)
    Subtype.val_injective ?_).mp
  · simpa only [Function.comp_def, lowBoundaryExtensionValue_retained] using
      field.property.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
  · intro mode outside
    have low : ¬ (|mode.1| = 1 ∨ |mode.1| = 2) := by
      intro retained
      exact outside ⟨⟨mode, retained⟩, rfl⟩
    simp [lowBoundaryExtensionValue_outside field mode low]

def lowBoundaryExtension (field : LowModeBoundary) : lp (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 :=
  ⟨lowBoundaryExtensionValue field, lowBoundaryExtension_mem field⟩

theorem lowBoundaryExtension_norm (field : LowModeBoundary) :
    ‖lowBoundaryExtension field‖ = ‖field‖ := by
  have equality : ‖lowBoundaryExtension field‖ ^ 2 = ‖field‖ ^ 2 := by
    have left := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (lowBoundaryExtension field)
    have right := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at left right
    rw [left, right]
    symm
    have support : Function.support (fun mode => ‖lowBoundaryExtension field mode‖ ^ 2) ⊆
        {mode : ℤ × ℤ | (|mode.1| = 1 ∨ |mode.1| = 2)} := by
      intro mode inside
      by_contra low
      apply inside
      change ‖lowBoundaryExtensionValue field mode‖ ^ 2 = 0
      simp [lowBoundaryExtensionValue_outside field mode low]
    have result := tsum_subtype_eq_of_support_subset support
    change (∑' mode : LowAnnularMode, ‖lowBoundaryExtensionValue field mode.val‖ ^ 2) = _ at result
    simpa only [lowBoundaryExtensionValue_retained] using result
  nlinarith [norm_nonneg (lowBoundaryExtension field), norm_nonneg field]

def lowBoundaryIntoFull : LowModeBoundary →ₗᵢ[ℂ] lp (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 where
  toLinearMap :=
    { toFun := lowBoundaryExtension
      map_add' := by
        intro first second
        apply lp.ext
        funext mode
        change lowBoundaryExtensionValue (first + second) mode =
          lowBoundaryExtensionValue first mode + lowBoundaryExtensionValue second mode
        by_cases low : (|mode.1| = 1 ∨ |mode.1| = 2)
        · simp [lowBoundaryExtensionValue, low]
        · simp [lowBoundaryExtensionValue, low]
      map_smul' := by
        intro scalar field
        apply lp.ext
        funext mode
        by_cases low : (|mode.1| = 1 ∨ |mode.1| = 2)
        · simp [lowBoundaryExtension, lowBoundaryExtensionValue, low]
        · simp [lowBoundaryExtension, lowBoundaryExtensionValue, low] }
  norm_map' := lowBoundaryExtension_norm

theorem lowBoundaryIntoFull_retained (field : LowModeBoundary) (mode : LowAnnularMode) :
    lowBoundaryIntoFull field mode.val = field mode := lowBoundaryExtensionValue_retained field mode

theorem lowBoundaryIntoFull_outside (field : LowModeBoundary) (mode : ℤ × ℤ)
    (low : ¬ (|mode.1| = 1 ∨ |mode.1| = 2)) : lowBoundaryIntoFull field mode = 0 :=
  lowBoundaryExtensionValue_outside field mode low

end Grad.AnnularCrossMaps
