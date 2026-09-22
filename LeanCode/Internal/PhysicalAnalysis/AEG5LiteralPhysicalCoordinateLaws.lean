import AEG4ActualHighEnergyPackets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularTiltedReference Grad.AnnularGrades Grad.AnnularFluxTrace
open Grad.CircularHighWeak Grad.AnnularSourceGraph Grad.CircularHighRegularity

/-- The actual 1/r scalar, extended continuously only outside the collar. -/
def highReciprocalRadius (lower : ℝ) (positive : 0 < lower) : C(ℝ, ℝ) :=
  ⟨fun radius => (max lower radius)⁻¹,
    (continuous_const.max continuous_id).inv₀ (fun _ => (positive.trans_le (le_max_left _ _)).ne')⟩

theorem highEnergyRadius_mode (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    highEnergyRadius lower length positive field mode =
      collarScalar 1 lower (highReciprocalRadius lower positive)
        (annularEnergyValue lower length positive field mode) := by
  change (1 / 2 : ℂ) • annularEnergyRadial lower length positive field mode = _
  rw [annularEnergyRadial_mode]
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ)
    (collarScalar 1 lower (annularRadialCurve lower positive) (annularEnergyValue lower length positive field mode)),
    collarScalar_ae 1 lower (annularRadialCurve lower positive) (annularEnergyValue lower length positive field mode),
    collarScalar_ae 1 lower (highReciprocalRadius lower positive) (annularEnergyValue lower length positive field mode)]
      with radius scaled radial reciprocal
  rw [scaled, Pi.smul_apply, radial, reciprocal]
  change (1 / 2 : ℂ) • ((2 / max lower radius : ℝ) • _) = (max lower radius)⁻¹ • _
  apply PiLp.ext
  intro component
  change (1 / 2 : ℂ) * (((2 / max lower radius : ℝ) : ℂ) * _) =
    (((max lower radius)⁻¹ : ℝ) : ℂ) * _
  push_cast
  ring

theorem highEnergyAngularRadius_mode (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    highEnergyAngularRadius lower length positive field mode =
      (Complex.I * (mode.val.1 : ℂ)) • highEnergyRadius lower length positive field mode := by
  rw [highEnergyRadius_mode]
  let mass := annularEnergyMass lower length positive field mode
  change Complex.I • scalarRadialMap lower (highAngularRadiusRatio lower length positive mode) 1
      (highAngularRadiusRatio_bound lower length positive mode) mass =
    (Complex.I * (mode.val.1 : ℂ)) • collarScalar 1 lower (highReciprocalRadius lower positive)
      (scalarRadialMap lower (annularValueMassRatio lower length positive mode) (1 / 3)
        (annularValueMassRatio_bound lower length positive mode) mass)
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul Complex.I
      (scalarRadialMap lower (highAngularRadiusRatio lower length positive mode) 1
        (highAngularRadiusRatio_bound lower length positive mode) mass),
    scalarRadialMap_ae lower (highAngularRadiusRatio lower length positive mode) 1
      (highAngularRadiusRatio_bound lower length positive mode) mass,
    Lp.coeFn_smul (Complex.I * (mode.val.1 : ℂ))
      (collarScalar 1 lower (highReciprocalRadius lower positive)
        (scalarRadialMap lower (annularValueMassRatio lower length positive mode) (1 / 3)
          (annularValueMassRatio_bound lower length positive mode) mass)),
    collarScalar_ae 1 lower (highReciprocalRadius lower positive)
      (scalarRadialMap lower (annularValueMassRatio lower length positive mode) (1 / 3)
        (annularValueMassRatio_bound lower length positive mode) mass),
    scalarRadialMap_ae lower (annularValueMassRatio lower length positive mode) (1 / 3)
      (annularValueMassRatio_bound lower length positive mode) mass]
    with radius leftScaled left rightScaled right value
  rw [leftScaled, rightScaled]
  simp only [Pi.smul_apply]
  rw [left, right, value]
  change Complex.I • ((((mode.val.1 : ℝ) / max lower radius) /
      annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius) • mass radius) =
    (Complex.I * (mode.val.1 : ℂ)) • ((max lower radius)⁻¹ •
      ((annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius)⁻¹ • mass radius))
  apply PiLp.ext
  intro component
  change Complex.I * (((((mode.val.1 : ℝ) / max lower radius) /
    annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius : ℝ) : ℂ) * mass radius component) =
    (Complex.I * (mode.val.1 : ℂ)) *
      ((((max lower radius)⁻¹ : ℝ) : ℂ) *
        ((((annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius)⁻¹ : ℝ) : ℂ) * mass radius component))
  push_cast
  ring

theorem highEnergyCell_mode (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    highEnergyCell lower length positive field mode =
      (Complex.I * ((mode.val.2 : ℝ) / length : ℝ)) • annularEnergyValue lower length positive field mode := by
  change (((highMultiplier mode.val.1)⁻¹ : ℝ) : ℂ) • annularEnergyCell lower length positive field mode = _
  rw [annularEnergyCell_mode, smul_smul]
  congr 1
  unfold annularCellSymbol
  have nonzero : (highMultiplier mode.val.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (highMultiplier_positive mode).ne'
  push_cast
  field_simp

/-- Exact completed scalar value, R/r and cell derivative coordinates; no
Fourier differentiability premise is substituted for a missing identity. -/
theorem highPhysicalCoordinates_literal (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    highEnergyRadius lower length positive (bEnergyDecode lower length positive field) mode =
      collarScalar 1 lower (highReciprocalRadius lower positive)
        (annularEnergyValue lower length positive (bEnergyDecode lower length positive field) mode) ∧
    highEnergyAngularRadius lower length positive (bEnergyDecode lower length positive field) mode =
      (Complex.I * (mode.val.1 : ℂ)) • highEnergyRadius lower length positive (bEnergyDecode lower length positive field) mode ∧
    highEnergyCell lower length positive (bEnergyDecode lower length positive field) mode =
      (Complex.I * ((mode.val.2 : ℝ) / length : ℝ)) •
        annularEnergyValue lower length positive (bEnergyDecode lower length positive field) mode :=
  ⟨highEnergyRadius_mode lower length positive _ mode,
    highEnergyAngularRadius_mode lower length positive _ mode,
    highEnergyCell_mode lower length positive _ mode⟩

end Grad.AnnularCurrentEnergy
