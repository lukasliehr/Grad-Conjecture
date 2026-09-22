import COR12Maps

noncomputable section

namespace Grad.COR12Extension

open Grad.ClosedJets
open Grad.CartesianState
open Grad.DiskExtension.Operator
open Grad.FourierGrade

def extensionEnergyConstant (grade : ℕ) : ℝ :=
  16 * (4 : ℝ) ^ grade * periodizedGradeEnergyFactor grade *
    (Nat.choose (grade + 3) 3 : ℝ)

def retractionEnergyConstant (grade : ℕ) : ℝ :=
  16 * originalDiskEnergyFactor grade * (Nat.choose (grade + 3) 3 : ℝ)

theorem extensionEnergyConstant_nonnegative (grade : ℕ) :
    0 ≤ extensionEnergyConstant grade := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
    (periodizedGradeEnergyFactor_nonnegative grade)) (Nat.cast_nonneg _)

theorem retractionEnergyConstant_nonnegative (grade : ℕ) :
    0 ≤ retractionEnergyConstant grade := by
  exact mul_nonneg (mul_nonneg (by norm_num)
    (originalDiskEnergyFactor_nonnegative grade)) (Nat.cast_nonneg _)

theorem weightedFourierExtension_norm_sq_le {dimension : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension) (grade : ℕ) :
    ‖coreToGrade grade (weightedFourierExtension parameters field)‖ ^ 2 ≤
      extensionEnergyConstant grade * ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2 := by
  let ordinary := weightedSmoothEquiv parameters field
  let extended := ordinaryExtensionRetraction.extension dimension ordinary
  have parseval := (torusSmoothFourierCore_energy_comparison extended grade).1
  have fourPositive : 0 < (4 : ℝ) ^ grade := by positivity
  have fourBound := (inv_mul_le_iff₀ fourPositive).mp parseval
  rw [torusDerivativeEnergy_normalization] at fourBound
  have extensionBound : torusDerivativeEnergy grade extended ≤
      periodizedGradeEnergyFactor grade * diskDerivativeEnergy grade ordinary :=
    torusDerivativeEnergy_periodizedExtension_le ordinary grade
  have diskBound := diskDerivativeEnergy_le_original parameters field grade
  calc
    ‖coreToGrade grade (weightedFourierExtension parameters field)‖ ^ 2 ≤
        (4 : ℝ) ^ grade * (torusMeasureFactor * torusDerivativeEnergy grade extended) := fourBound
    _ ≤ (4 : ℝ) ^ grade *
        (torusMeasureFactor * (periodizedGradeEnergyFactor grade *
          diskDerivativeEnergy grade ordinary)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left extensionBound torusMeasureFactor_pos.le) fourPositive.le
    _ = (16 * (4 : ℝ) ^ grade * periodizedGradeEnergyFactor grade) *
        ((2 * Real.pi) * diskDerivativeEnergy grade ordinary) := by
      unfold torusMeasureFactor
      ring
    _ ≤ (16 * (4 : ℝ) ^ grade * periodizedGradeEnergyFactor grade) *
        ((Nat.choose (grade + 3) 3 : ℝ) * ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left diskBound
        (mul_nonneg (mul_nonneg (by norm_num) fourPositive.le)
          (periodizedGradeEnergyFactor_nonnegative grade))
    _ = _ := by unfold extensionEnergyConstant; ring

theorem weightedFourierRetraction_norm_sq_le {dimension : ℕ}
    (parameters : PhaseParameters) (values : JCore (ComplexEuclidean dimension)) (grade : ℕ) :
    ‖GradeCore.ofCoreLinear (grade := grade) (weightedFourierRetraction parameters values)‖ ^ 2 ≤
      retractionEnergyConstant grade * ‖coreToGrade grade values‖ ^ 2 := by
  let reconstructed := reconstructedTorusSmoothField values
  let restricted := ordinaryExtensionRetraction.restriction dimension reconstructed
  have originalBound := original_norm_sq_le_diskDerivativeEnergy parameters
    (weightedFourierRetraction parameters values) grade
  have retractionWeighted : weightedSmoothEquiv parameters
      (weightedFourierRetraction parameters values) = restricted :=
    (weightedSmoothEquiv parameters).apply_symm_apply restricted
  rw [retractionWeighted] at originalBound
  have restrictionBound : diskDerivativeEnergy grade restricted ≤
      256 * torusDerivativeEnergy grade reconstructed :=
    diskDerivativeEnergy_restriction_le grade reconstructed
  have parseval := (torusSmoothFourierCore_energy_comparison reconstructed grade).2
  rw [torusDerivativeEnergy_normalization, torusSmoothFourierCore_reconstructed] at parseval
  calc
    ‖GradeCore.ofCoreLinear (grade := grade) (weightedFourierRetraction parameters values)‖ ^ 2 ≤
        originalDiskEnergyFactor grade * ((2 * Real.pi) * diskDerivativeEnergy grade restricted) :=
      originalBound
    _ ≤ originalDiskEnergyFactor grade *
        ((2 * Real.pi) * (256 * torusDerivativeEnergy grade reconstructed)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left restrictionBound (by positivity))
        (originalDiskEnergyFactor_nonnegative grade)
    _ = (16 * originalDiskEnergyFactor grade) *
        (torusMeasureFactor * torusDerivativeEnergy grade reconstructed) := by
      unfold torusMeasureFactor
      ring
    _ ≤ (16 * originalDiskEnergyFactor grade) *
        ((Nat.choose (grade + 3) 3 : ℝ) * ‖coreToGrade grade values‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left parseval
        (mul_nonneg (by norm_num) (originalDiskEnergyFactor_nonnegative grade))
    _ = _ := by unfold retractionEnergyConstant; ring

def extensionNormConstant (grade : ℕ) : ℝ := Real.sqrt (extensionEnergyConstant grade)

def retractionNormConstant (grade : ℕ) : ℝ := Real.sqrt (retractionEnergyConstant grade)

def sameGradeConstant (grade : ℕ) : ℝ :=
  max (extensionNormConstant grade) (retractionNormConstant grade)

theorem sameGradeConstant_nonnegative (grade : ℕ) : 0 ≤ sameGradeConstant grade :=
  (Real.sqrt_nonneg _).trans (le_max_left _ _)

theorem weightedFourierExtension_norm_le {dimension : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension) (grade : ℕ) :
    ‖coreToGrade grade (weightedFourierExtension parameters field)‖ ≤
      sameGradeConstant grade * ‖GradeCore.ofCoreLinear (grade := grade) field‖ := by
  have squared := weightedFourierExtension_norm_sq_le parameters field grade
  have root := Real.sqrt_le_sqrt squared
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (extensionEnergyConstant_nonnegative grade),
    Real.sqrt_sq (norm_nonneg _)] at root
  exact root.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

theorem weightedFourierRetraction_norm_le {dimension : ℕ}
    (parameters : PhaseParameters) (values : JCore (ComplexEuclidean dimension)) (grade : ℕ) :
    ‖GradeCore.ofCoreLinear (grade := grade) (weightedFourierRetraction parameters values)‖ ≤
      sameGradeConstant grade * ‖coreToGrade grade values‖ := by
  have squared := weightedFourierRetraction_norm_sq_le parameters values grade
  have root := Real.sqrt_le_sqrt squared
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (retractionEnergyConstant_nonnegative grade),
    Real.sqrt_sq (norm_nonneg _)] at root
  exact root.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

end Grad.COR12Extension
