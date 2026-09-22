import AJF7OriginalHighWeightedFatou
import AIZ4CompleteCoupledUnitary
import AJB32LiteralLowInsertedGraphGrade

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularOmegaGraph Grad.AnnularCoupledOrbit Grad.AnnularLowEnergy
open Grad.AnnularKernelOrbit Grad.AnnularInverseCalculus Grad.AnnularOrbitGenerators Grad.AnnularLowOrbit
open Grad.AnnularCoupledInverse Grad.AnnularCrossMaps Grad.AnnularLowCompletion

local instance coupledRealNormed (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    NormedSpace ℝ (CoupledSpace lower length positive lengthPositive) :=
  NormedSpace.restrictScalars ℝ ℂ (CoupledSpace lower length positive lengthPositive)

def coupledEnergy (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    CoupledSpace lower length positive lengthPositive →L[ℂ] annularEnergySpace lower length positive :=
  (crossHighW lower length positive lengthPositive).comp (coupledHigh lower length positive lengthPositive)

def coupledFlux (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    CoupledSpace lower length positive lengthPositive →L[ℂ] annularOmegaGraph lower length positive lengthPositive :=
  (crossHighFlux lower length positive lengthPositive).comp (coupledHigh lower length positive lengthPositive)

theorem coupledEnergy_bound (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive) :
    ‖field.ofLp.1.ofLp.1‖ ≤ ‖field‖ :=
  (crossHighW_bound lower length positive lengthPositive field.ofLp.1).trans
    (coupledHigh_bound lower length positive lengthPositive field)

theorem coupledFlux_bound (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive) :
    ‖field.ofLp.1.ofLp.2‖ ≤ ‖field‖ := by
  have square := WithLp.prod_norm_sq_eq_of_L2 field.ofLp.1
  change ‖field.ofLp.1‖ ^ 2 = ‖field.ofLp.1.ofLp.1‖ ^ 2 + ‖field.ofLp.1.ofLp.2‖ ^ 2 at square
  have first : ‖field.ofLp.1.ofLp.2‖ ≤ ‖field.ofLp.1‖ := by
    nlinarith only [square, norm_nonneg field.ofLp.1, norm_nonneg field.ofLp.1.ofLp.2,
      sq_nonneg ‖field.ofLp.1.ofLp.1‖]
  exact first.trans (coupledHigh_bound lower length positive lengthPositive field)

/-- A single actual derivative vector lies in the original complete coupled
carrier, which simultaneously stores W, Domega and rho-normalized Y. -/
def coupledAxisGenerator (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive) (axis : Bool) (order : ℕ) :
    CoupledSpace lower length positive lengthPositive :=
  iteratedDeriv order (fun time : ℝ => coupledTranslationEquivalence lower length positive lengthPositive
    (time • axisVector axis) field) 0

theorem coupledAxisGenerator_energy (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive) (axis : Bool)
    (smooth : ContDiff ℝ ∞ (fun time : ℝ => coupledTranslationEquivalence lower length positive lengthPositive
      (time • axisVector axis) field)) (order : ℕ) (index : HighAnnularMode) :
    (coupledAxisGenerator lower length positive lengthPositive field axis order).ofLp.1.ofLp.1.val index =
      (Complex.I * (axisFrequency axis index.val : ℂ)) ^ order • field.ofLp.1.ofLp.1.val index :=
  smoothLpCharacterOrbit_coordinates ((annularEnergySpace lower length positive).subtypeL.comp
    (coupledEnergy lower length positive lengthPositive))
    (fun time : ℝ => coupledTranslationEquivalence lower length positive lengthPositive (time • axisVector axis) field)
    smooth (fun index : HighAnnularMode => axisFrequency axis index.val) field.ofLp.1.ofLp.1.val
    (fun time index => by
      change (energyTranslation lower length positive (time • axisVector axis) field.ofLp.1.ofLp.1).val index = _
      rw [energyTranslation_apply, orbitCharacter_axis]) order index

theorem coupledAxisGenerator_flux (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive) (axis : Bool)
    (smooth : ContDiff ℝ ∞ (fun time : ℝ => coupledTranslationEquivalence lower length positive lengthPositive
      (time • axisVector axis) field)) (order : ℕ) (coordinate : Fin 2) (index : HighAnnularMode) :
    (coupledAxisGenerator lower length positive lengthPositive field axis order).ofLp.1.ofLp.2.val coordinate index =
      (Complex.I * (axisFrequency axis index.val : ℂ)) ^ order • field.ofLp.1.ofLp.2.val coordinate index :=
  smoothLpCharacterOrbit_coordinates ((fluxStoredCoordinate lower length positive lengthPositive coordinate).comp
    (coupledFlux lower length positive lengthPositive))
    (fun time : ℝ => coupledTranslationEquivalence lower length positive lengthPositive (time • axisVector axis) field)
    smooth (fun index : HighAnnularMode => axisFrequency axis index.val) (field.ofLp.1.ofLp.2.val coordinate)
    (fun time index => by
      change (fluxTranslation lower length positive lengthPositive (time • axisVector axis) field.ofLp.1.ofLp.2).val coordinate index = _
      rw [fluxTranslation_apply, orbitCharacter_axis]) order index

theorem coupledAxisGenerator_low (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive) (axis : Bool)
    (smooth : ContDiff ℝ ∞ (fun time : ℝ => coupledTranslationEquivalence lower length positive lengthPositive
      (time • axisVector axis) field)) (order : ℕ) (coordinate : Fin 2) (index : LowAnnularIndex) :
    (coupledAxisGenerator lower length positive lengthPositive field axis order).ofLp.2.val coordinate index =
      (Complex.I * (axisFrequency axis index.2.val : ℂ)) ^ order • field.ofLp.2.val coordinate index :=
  smoothLpCharacterOrbit_coordinates ((lowStoredCoordinate lower length positive coordinate).comp
    (coupledLow lower length positive lengthPositive))
    (fun time : ℝ => coupledTranslationEquivalence lower length positive lengthPositive (time • axisVector axis) field)
    smooth (fun index : LowAnnularIndex => axisFrequency axis index.2.val) (field.ofLp.2.val coordinate)
    (fun time index => by
      change (lowTranslation lower length positive (time • axisVector axis) field.ofLp.2).val coordinate index = _
      rw [lowTranslation_apply, orbitCharacter_axis]) order index

end Grad.AnnularHighGenerators
