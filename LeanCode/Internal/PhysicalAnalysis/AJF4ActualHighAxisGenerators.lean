import AJF3TwoGeneratorLpGrade
import AJB23ActualAxisDerivativeRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularOmegaGraph Grad.AnnularCoupledOrbit
open Grad.AnnularKernelOrbit Grad.AnnularInverseCalculus Grad.AnnularOrbitGenerators Grad.CartesianState

def axisFrequency (axis : Bool) (mode : ℤ × ℤ) : ℤ := if axis then mode.2 else mode.1

theorem orbitCharacter_axis (axis : Bool) (time : ℝ) (mode : ℤ × ℤ) :
    orbitCharacter (time • axisVector axis) mode = cellExponential (axisFrequency axis mode) time := by
  cases axis <;> simp [axisVector, axisFrequency, orbitCharacter, orbitAngle, cellExponential, mul_assoc]

def energyAxisGenerator (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) (axis : Bool) (order : ℕ) :
    annularEnergySpace lower length positive :=
  iteratedDeriv order (fun time : ℝ => energyTranslation lower length positive (time • axisVector axis) field) 0

/-- The complete energy norm derivative supplies the actual generator in
all stored coordinates of W; isometry alone is not a smoothness premise. -/
theorem energyAxisGenerator_coefficients (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) (axis : Bool)
    (smooth : ContDiff ℝ ∞ (fun time : ℝ => energyTranslation lower length positive (time • axisVector axis) field))
    (order : ℕ) (index : HighAnnularMode) :
    (energyAxisGenerator lower length positive field axis order).val index =
      (Complex.I * (axisFrequency axis index.val : ℂ)) ^ order • field.val index :=
  smoothLpCharacterOrbit_coordinates (annularEnergySpace lower length positive).subtypeL
    (fun time : ℝ => energyTranslation lower length positive (time • axisVector axis) field) smooth
    (fun mode : HighAnnularMode => axisFrequency axis mode.val) field.val
    (fun time mode => by rw [Submodule.subtypeL_apply, energyTranslation_apply, orbitCharacter_axis]) order index

def fluxAxisGenerator (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : annularOmegaGraph lower length positive lengthPositive) (axis : Bool) (order : ℕ) :
    annularOmegaGraph lower length positive lengthPositive :=
  iteratedDeriv order (fun time : ℝ => fluxTranslation lower length positive lengthPositive (time • axisVector axis) field) 0

/-- Both genuine value and Domega derivative are the coefficients of the
same complete graph derivative. -/
theorem fluxAxisGenerator_coefficients (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : annularOmegaGraph lower length positive lengthPositive) (axis : Bool)
    (smooth : ContDiff ℝ ∞ (fun time : ℝ => fluxTranslation lower length positive lengthPositive (time • axisVector axis) field))
    (order : ℕ) (coordinate : Fin 2) (index : HighAnnularMode) :
    (fluxAxisGenerator lower length positive lengthPositive field axis order).val coordinate index =
      (Complex.I * (axisFrequency axis index.val : ℂ)) ^ order • field.val coordinate index :=
  smoothLpCharacterOrbit_coordinates (fluxStoredCoordinate lower length positive lengthPositive coordinate)
    (fun time : ℝ => fluxTranslation lower length positive lengthPositive (time • axisVector axis) field) smooth
    (fun mode : HighAnnularMode => axisFrequency axis mode.val) (field.val coordinate)
    (fun time mode => by
      change (fluxTranslation lower length positive lengthPositive (time • axisVector axis) field).val coordinate mode = _
      rw [fluxTranslation_apply, orbitCharacter_axis]) order index

end Grad.AnnularHighGenerators
