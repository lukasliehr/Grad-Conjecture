import AEI1ActualLowNormalizedSymbols

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction

abbrev LowModeBulk (lower : ℝ) := lp (fun _ : LowAnnularMode => RadialL2 1 lower) 2

def lowComponentValue (lower : ℝ) (row : Fin 2) (field : LowEnergyBulk lower) : LowModeBulk lower :=
  ⟨fun mode => field (row, mode), by
    apply memℓp_gen
    exact (field.property.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).comp_injective
      (fun _ _ same => (Prod.mk.inj same).2)⟩

theorem lowComponentValue_bound (lower : ℝ) (row : Fin 2) (field : LowEnergyBulk lower) :
    ‖lowComponentValue lower row field‖ ≤ ‖field‖ := by
  have left := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (lowComponentValue lower row field)
  have right := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at left right
  have squareSum := lowLp_summable_norm_sq field
  have comparison := tsum_comp_le_tsum_of_inj squareSum (fun index => sq_nonneg ‖field index‖)
    (fun _ _ same => (Prod.mk.inj same).2 : Function.Injective (fun mode : LowAnnularMode => (row, mode)))
  change (∑' mode : LowAnnularMode, ‖field (row, mode)‖ ^ 2) ≤ ∑' index : LowAnnularIndex, ‖field index‖ ^ 2 at comparison
  rw [← right] at comparison
  have firstSquare : ‖lowComponentValue lower row field‖ ^ 2 = ∑' mode : LowAnnularMode, ‖field (row, mode)‖ ^ 2 := left
  rw [← firstSquare] at comparison
  nlinarith [norm_nonneg (lowComponentValue lower row field), norm_nonneg field]

def lowComponent (lower : ℝ) (row : Fin 2) : LowEnergyBulk lower →L[ℂ] LowModeBulk lower :=
  LinearMap.mkContinuous
    { toFun := lowComponentValue lower row
      map_add' := fun _ _ => by apply lp.ext; funext mode; rfl
      map_smul' := fun _ _ => by apply lp.ext; funext mode; rfl }
    1 (fun field => by
      change ‖lowComponentValue lower row field‖ ≤ 1 * ‖field‖
      rw [one_mul]
      exact lowComponentValue_bound lower row field)

theorem lowComponent_apply (lower : ℝ) (row : Fin 2) (field : LowEnergyBulk lower) (mode : LowAnnularMode) :
    lowComponent lower row field mode = field (row, mode) := rfl

theorem lowComponent_bound (lower : ℝ) (row : Fin 2) (field : LowEnergyBulk lower) :
    ‖lowComponent lower row field‖ ≤ ‖field‖ := lowComponentValue_bound lower row field

end Grad.AnnularCurrentLow
