import TRM6GraphValueMap

noncomputable section

namespace Grad.SourceCollarAngular

open Grad.SourceCollarDivision Grad.ClosedJets
open Grad.Constraints.Gauges

def annularPlanarComponent {radial : ℕ} (lower : ℝ) (positive : 0 < lower)
    (coordinate : Fin 2) :
    annularDerivativeGraph 2 lower positive radial →L[ℂ]
      annularDerivativeGraph 1 lower positive radial :=
  annularGraphValueMap lower positive (planarComponentMap coordinate)

@[simp] theorem annularPlanarComponent_apply {radial : ℕ} (lower : ℝ)
    (positive : 0 < lower) (coordinate : Fin 2)
    (field : annularDerivativeGraph 2 lower positive radial)
    (index : Fin (radial + 1)) (mode : ℤ × ℤ) :
    (annularPlanarComponent lower positive coordinate field).val index mode =
      radialValueMap lower (planarComponentMap coordinate) (field.val index mode) := rfl

theorem annularPlanarComponent_apply_norm_le {radial : ℕ} (lower : ℝ)
    (positive : 0 < lower) (coordinate : Fin 2)
    (field : annularDerivativeGraph 2 lower positive radial) :
    ‖annularPlanarComponent lower positive coordinate field‖ ≤ ‖field‖ := by
  calc
    _ ≤ ‖planarComponentMap coordinate‖ * ‖field‖ :=
      annularGraphValueMap_apply_norm_le lower positive (planarComponentMap coordinate) field
    _ ≤ 1 * ‖field‖ :=
      mul_le_mul_of_nonneg_right (planarComponentMap_norm_le coordinate) (norm_nonneg _)
    _ = _ := one_mul _

theorem annularPlanarComponent_norm_le {radial : ℕ} (lower : ℝ)
    (positive : 0 < lower) (coordinate : Fin 2) :
    ‖annularPlanarComponent (radial := radial) lower positive coordinate‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro field
  simpa only [one_mul] using annularPlanarComponent_apply_norm_le lower positive coordinate field

/-- Exact polar radial contraction `e_r · f = cos(θ) f₁ + sin(θ) f₂`. -/
def annularRadialContraction {radial : ℕ} (lower : ℝ) (positive : 0 < lower)
    (power : ℕ) :
    annularDerivativeGraph 2 lower positive radial →L[ℂ]
      annularDerivativeGraph 1 lower positive radial :=
  (annularPlanarComponent lower positive 0).comp
      (annularCosine lower positive power) +
    (annularPlanarComponent lower positive 1).comp
      (annularSine lower positive power)

/-- Exact polar tangential contraction `e_θ · f = -sin(θ) f₁ + cos(θ) f₂`. -/
def annularTangentialContraction {radial : ℕ} (lower : ℝ) (positive : 0 < lower)
    (power : ℕ) :
    annularDerivativeGraph 2 lower positive radial →L[ℂ]
      annularDerivativeGraph 1 lower positive radial :=
  (annularPlanarComponent lower positive 1).comp
      (annularCosine lower positive power) -
    (annularPlanarComponent lower positive 0).comp
      (annularSine lower positive power)

@[simp] theorem annularRadialContraction_apply {radial : ℕ} (lower : ℝ)
    (positive : 0 < lower) (power : ℕ)
    (field : annularDerivativeGraph 2 lower positive radial)
    (index : Fin (radial + 1)) (mode : ℤ × ℤ) :
    (annularRadialContraction lower positive power field).val index mode =
      radialValueMap lower (planarComponentMap 0)
          ((annularCosine lower positive power field).val index mode) +
        radialValueMap lower (planarComponentMap 1)
          ((annularSine lower positive power field).val index mode) := rfl

@[simp] theorem annularTangentialContraction_apply {radial : ℕ} (lower : ℝ)
    (positive : 0 < lower) (power : ℕ)
    (field : annularDerivativeGraph 2 lower positive radial)
    (index : Fin (radial + 1)) (mode : ℤ × ℤ) :
    (annularTangentialContraction lower positive power field).val index mode =
      radialValueMap lower (planarComponentMap 1)
          ((annularCosine lower positive power field).val index mode) -
        radialValueMap lower (planarComponentMap 0)
          ((annularSine lower positive power field).val index mode) := rfl

theorem annularRadialContraction_apply_norm_le {radial : ℕ} (lower : ℝ)
    (positive : 0 < lower) (power : ℕ)
    (field : annularDerivativeGraph 2 lower positive radial) :
    ‖annularRadialContraction lower positive power field‖ ≤
      2 * (2 : ℝ) ^ power * ‖field‖ := by
  have cosineComponent := annularPlanarComponent_apply_norm_le lower positive (0 : Fin 2)
    (annularCosine lower positive power field)
  have sineComponent := annularPlanarComponent_apply_norm_le lower positive (1 : Fin 2)
    (annularSine lower positive power field)
  have cosine := annularCosine_apply_norm_le lower positive power field
  have sine := annularSine_apply_norm_le lower positive power field
  have firstBound :
      ‖((annularPlanarComponent lower positive (0 : Fin 2)).comp
        (annularCosine lower positive power)) field‖ ≤ (2 : ℝ) ^ power * ‖field‖ :=
    cosineComponent.trans cosine
  have secondBound :
      ‖((annularPlanarComponent lower positive (1 : Fin 2)).comp
        (annularSine lower positive power)) field‖ ≤ (2 : ℝ) ^ power * ‖field‖ :=
    sineComponent.trans sine
  rw [annularRadialContraction, add_apply]
  exact (norm_add_le _ _).trans (by linarith [firstBound, secondBound])

theorem annularTangentialContraction_apply_norm_le {radial : ℕ} (lower : ℝ)
    (positive : 0 < lower) (power : ℕ)
    (field : annularDerivativeGraph 2 lower positive radial) :
    ‖annularTangentialContraction lower positive power field‖ ≤
      2 * (2 : ℝ) ^ power * ‖field‖ := by
  have cosineComponent := annularPlanarComponent_apply_norm_le lower positive (1 : Fin 2)
    (annularCosine lower positive power field)
  have sineComponent := annularPlanarComponent_apply_norm_le lower positive (0 : Fin 2)
    (annularSine lower positive power field)
  have cosine := annularCosine_apply_norm_le lower positive power field
  have sine := annularSine_apply_norm_le lower positive power field
  have firstBound :
      ‖((annularPlanarComponent lower positive (1 : Fin 2)).comp
        (annularCosine lower positive power)) field‖ ≤ (2 : ℝ) ^ power * ‖field‖ :=
    cosineComponent.trans cosine
  have secondBound :
      ‖((annularPlanarComponent lower positive (0 : Fin 2)).comp
        (annularSine lower positive power)) field‖ ≤ (2 : ℝ) ^ power * ‖field‖ :=
    sineComponent.trans sine
  rw [annularTangentialContraction, sub_apply]
  exact (norm_sub_le _ _).trans (by linarith [firstBound, secondBound])

theorem annularRadialContraction_norm_le {radial : ℕ} (lower : ℝ)
    (positive : 0 < lower) (power : ℕ) :
    ‖annularRadialContraction (radial := radial) lower positive power‖ ≤
      2 * (2 : ℝ) ^ power := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro field
  simpa only [mul_assoc] using annularRadialContraction_apply_norm_le lower positive power field

theorem annularTangentialContraction_norm_le {radial : ℕ} (lower : ℝ)
    (positive : 0 < lower) (power : ℕ) :
    ‖annularTangentialContraction (radial := radial) lower positive power‖ ≤
      2 * (2 : ℝ) ^ power := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro field
  simpa only [mul_assoc] using annularTangentialContraction_apply_norm_le lower positive power field

end Grad.SourceCollarAngular
