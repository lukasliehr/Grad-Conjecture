import AKAQ1SpatialFourierDecay

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open scoped BigOperators ENNReal
namespace Grad.OriginalFlatAxisDecay
open Grad.FourierGrade Grad.CartesianState Grad.ClosedJets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Cauchy–Schwarz is used over spatial frequencies only. -/
theorem finite_smul_sum_sq {I : Type*} (support : Finset I) (factor : I → ℂ) (field : I → E) :
    ‖∑ index ∈ support, factor index • field index‖^2 ≤
      (∑ index ∈ support, ‖factor index‖^2) * ∑ index ∈ support, ‖field index‖^2 := by
  have triangle := norm_sum_le support (fun index => factor index • field index)
  simp_rw [norm_smul] at triangle
  exact (pow_le_pow_left₀ (norm_nonneg _) triangle 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq support (fun index => ‖factor index‖) (fun index => ‖field index‖))

def fibreMode (pair : ℤ × SpatialMode) : FourierMode := (pair.2.1,pair.2.2,pair.1)

theorem fibreMode_injective : Function.Injective fibreMode := by
  rintro ⟨cell,first,second⟩ ⟨other,a,b⟩ same
  have cells := congrArg (fun mode : FourierMode => mode.2.2) same
  have firsts := congrArg (fun mode : FourierMode => mode.1) same
  have seconds := congrArg (fun mode : FourierMode => mode.2.1) same
  change cell = other at cells
  change first = a at firsts
  change second = b at seconds
  cases cells
  cases firsts
  cases seconds
  rfl

omit [NormedSpace ℂ E] in
theorem fourierRectangle_energy_le (field : JGrade E 4) (cells : Finset ℤ) (support : Finset SpatialMode) :
    ∑ cell ∈ cells, ∑ mode ∈ support, ‖field.val (fibreMode (cell,mode))‖^2 ≤ ‖field‖^2 := by
  classical
  let rectangle := (cells.product support).image fibreMode
  have same : (∑ mode ∈ rectangle, ‖field.val mode‖^2) =
      ∑ cell ∈ cells, ∑ mode ∈ support, ‖field.val (fibreMode (cell,mode))‖^2 := by
    rw [Finset.sum_image (fun _ _ _ _ same => fibreMode_injective same)]
    exact Finset.sum_product _ _ _
  rw [← same]
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) field rectangle

/-- A bounded row-square factor controls all cells at once in the original
J4 Hilbert norm. No cell truncation constant enters. -/
theorem finiteFibreEnergy_bound (factor : SpatialMode → ℤ → ℂ)
    (payment : ℝ) (nonnegative : 0 ≤ payment)
    (bound : ∀ mode cell, ‖factor mode cell‖^2 ≤ payment * spatialDecay mode)
    (field : JGrade E 4) (cells : Finset ℤ) (support : Finset SpatialMode) :
    ∑ cell ∈ cells, ‖∑ mode ∈ support, factor mode cell • field.val (fibreMode (cell,mode))‖^2 ≤
      payment * spatialDecayConstant * ‖field‖^2 := by
  have rows (cell : ℤ) : (∑ mode ∈ support, ‖factor mode cell‖^2) ≤ payment * spatialDecayConstant := by
    calc
      _ ≤ ∑ mode ∈ support, payment * spatialDecay mode := Finset.sum_le_sum (fun mode _ => bound mode cell)
      _ = payment * ∑ mode ∈ support, spatialDecay mode := (Finset.mul_sum _ _ _).symm
      _ ≤ payment * spatialDecayConstant := mul_le_mul_of_nonneg_left (spatialDecay_sum_le support) nonnegative
  have each (cell : ℤ) : ‖∑ mode ∈ support, factor mode cell • field.val (fibreMode (cell,mode))‖^2 ≤
      payment * spatialDecayConstant * ∑ mode ∈ support, ‖field.val (fibreMode (cell,mode))‖^2 :=
    (finite_smul_sum_sq support (fun mode => factor mode cell) (fun mode => field (fibreMode (cell,mode)))).trans
      (mul_le_mul_of_nonneg_right (rows cell) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  calc
    _ ≤ ∑ cell ∈ cells, payment * spatialDecayConstant * ∑ mode ∈ support, ‖field.val (fibreMode (cell,mode))‖^2 :=
      Finset.sum_le_sum (fun cell _ => each cell)
    _ = payment * spatialDecayConstant * (∑ cell ∈ cells, ∑ mode ∈ support, ‖field.val (fibreMode (cell,mode))‖^2) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (fourierRectangle_energy_le field cells support)
      (mul_nonneg nonnegative spatialDecayConstant_nonnegative)

end Grad.OriginalFlatAxisDecay
