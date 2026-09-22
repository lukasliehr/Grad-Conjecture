import CE1Interface

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Grad.CellEnergy

open Grad.PDEBootstrap (Spatial)
open Grad.GenericCarriers (PhysicalValue CellValues FieldL2 fieldCellProjection cellProjection)

theorem coordinate_ae (dimension : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) :
    ∀ᵐ point ∂volume.restrict domain, ∀ cell : ℤ,
      fieldCellProjection dimension domain cell field point = field point cell :=
  Grad.GenericCarriers.fieldCellProjection_ae dimension domain field

theorem coordinate_integrable_sq (dimension : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) (cell : ℤ) :
    Integrable (fun point : Spatial => ‖field point cell‖ ^ 2) (volume.restrict domain) :=
  ((cellProjection (PhysicalValue dimension) cell).comp_memLp field).norm.integrable_sq

theorem cellEnergy_nonneg (dimension : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) (cell : ℤ) :
    0 ≤ cellEnergy dimension domain field cell := sq_nonneg _

theorem cellEnergy_eq_integral (dimension : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) (cell : ℤ) :
    cellEnergy dimension domain field cell =
      ∫ point : Spatial, ‖field point cell‖ ^ 2 ∂volume.restrict domain := by
  unfold cellEnergy
  rw [Grad.GenericCarriers.domainL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [coordinate_ae dimension domain field] with point coordinates
  rw [coordinates cell]

theorem cellEnergy_ofReal_eq_lintegral (dimension : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) (cell : ℤ) :
    ENNReal.ofReal (cellEnergy dimension domain field cell) =
      ∫⁻ point : Spatial, ENNReal.ofReal (‖field point cell‖ ^ 2) ∂volume.restrict domain := by
  rw [cellEnergy_eq_integral]
  exact ofReal_integral_eq_lintegral_ofReal (coordinate_integrable_sq dimension domain field cell)
    (Filter.Eventually.of_forall fun point => sq_nonneg ‖field point cell‖)

theorem field_norm_sq_eq_integral (dimension : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) :
    ‖field‖ ^ 2 = ∫ point : Spatial, ‖field point‖ ^ 2 ∂volume.restrict domain :=
  Grad.GenericCarriers.domainL2_norm_sq domain field

theorem field_norm_sq_ofReal_eq_lintegral (dimension : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) :
    ENNReal.ofReal (‖field‖ ^ 2) =
      ∫⁻ point : Spatial, ENNReal.ofReal (‖field point‖ ^ 2) ∂volume.restrict domain := by
  rw [field_norm_sq_eq_integral]
  exact ofReal_integral_eq_lintegral_ofReal (Lp.memLp field).norm.integrable_sq
    (Filter.Eventually.of_forall fun point => sq_nonneg ‖field point‖)

theorem pointwise_tsum_ofReal (dimension : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) (point : Spatial) :
    (∑' cell : ℤ, ENNReal.ofReal (‖field point cell‖ ^ 2)) =
      ENNReal.ofReal (‖field point‖ ^ 2) := by
  rw [Grad.GenericCarriers.cells_norm_sq]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun cell => sq_nonneg ‖field point cell‖)
    (Grad.TensorCellExchange.lp_summable_sq (field point))).symm

theorem tsum_cellEnergy_ofReal (dimension : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) :
    (∑' cell : ℤ, ENNReal.ofReal (cellEnergy dimension domain field cell)) =
      ENNReal.ofReal (‖field‖ ^ 2) := by
  calc
    (∑' cell : ℤ, ENNReal.ofReal (cellEnergy dimension domain field cell)) =
        ∑' cell : ℤ, ∫⁻ point : Spatial, ENNReal.ofReal (‖field point cell‖ ^ 2)
          ∂volume.restrict domain :=
      tsum_congr (cellEnergy_ofReal_eq_lintegral dimension domain field)
    _ = ∫⁻ point : Spatial, ∑' cell : ℤ, ENNReal.ofReal (‖field point cell‖ ^ 2)
        ∂volume.restrict domain :=
      (lintegral_tsum fun cell =>
        (coordinate_integrable_sq dimension domain field cell).aestronglyMeasurable.aemeasurable.ennreal_ofReal).symm
    _ = ∫⁻ point : Spatial, ENNReal.ofReal (‖field point‖ ^ 2) ∂volume.restrict domain :=
      lintegral_congr_ae (Filter.Eventually.of_forall (pointwise_tsum_ofReal dimension domain field))
    _ = ENNReal.ofReal (‖field‖ ^ 2) := (field_norm_sq_ofReal_eq_lintegral dimension domain field).symm

theorem tsum_cellEnergy_ofReal_lt_top (dimension : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) :
    (∑' cell : ℤ, ENNReal.ofReal (cellEnergy dimension domain field cell)) < ⊤ := by
  rw [tsum_cellEnergy_ofReal]
  exact ENNReal.ofReal_lt_top

theorem cellEnergy_summable (dimension : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) :
    Summable (fun cell : ℤ => ‖fieldCellProjection dimension domain cell field‖ ^ 2) := by
  have finiteTotal := ENNReal.summable_toReal
    (tsum_cellEnergy_ofReal_lt_top dimension domain field).ne
  simpa only [cellEnergy, ENNReal.toReal_ofReal (sq_nonneg _)] using finiteTotal

theorem field_norm_sq_eq_tsum (dimension : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) :
    ‖field‖ ^ 2 = ∑' cell : ℤ, ‖fieldCellProjection dimension domain cell field‖ ^ 2 := by
  have equality := congrArg ENNReal.toReal (tsum_cellEnergy_ofReal dimension domain field)
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)] at equality
  simpa only [cellEnergy, ENNReal.toReal_ofReal (sq_nonneg _)] using equality.symm

theorem weightedColumnBound (dimension : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) (weight : ℤ → ℝ) (bound : ℝ)
    (_boundNonnegative : 0 ≤ bound) (weightNonnegative : ∀ cell : ℤ, 0 ≤ weight cell)
    (weightBound : ∀ cell : ℤ, weight cell ≤ bound) :
    Summable (fun cell : ℤ => weight cell * ‖fieldCellProjection dimension domain cell field‖ ^ 2) ∧
    (∑' cell : ℤ, weight cell * ‖fieldCellProjection dimension domain cell field‖ ^ 2) ≤
      bound * ‖field‖ ^ 2 := by
  have majorantSummable := (cellEnergy_summable dimension domain field).mul_left bound
  have domination (cell : ℤ) :
      weight cell * ‖fieldCellProjection dimension domain cell field‖ ^ 2 ≤
        bound * ‖fieldCellProjection dimension domain cell field‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (weightBound cell) (sq_nonneg _)
  have weightedSummable := Summable.of_nonneg_of_le
    (fun cell => mul_nonneg (weightNonnegative cell) (sq_nonneg _)) domination majorantSummable
  refine ⟨weightedSummable, ?_⟩
  calc
    _ ≤ ∑' cell : ℤ, bound * ‖fieldCellProjection dimension domain cell field‖ ^ 2 :=
      weightedSummable.tsum_le_tsum domination majorantSummable
    _ = bound * ‖field‖ ^ 2 := by rw [tsum_mul_left, ← field_norm_sq_eq_tsum]

theorem coordinateEnergy : CoordinateEnergyGoal := by
  intro dimension domain field
  exact ⟨coordinate_ae dimension domain field, coordinate_integrable_sq dimension domain field,
    cellEnergy_eq_integral dimension domain field, cellEnergy_ofReal_eq_lintegral dimension domain field,
    field_norm_sq_eq_integral dimension domain field, field_norm_sq_ofReal_eq_lintegral dimension domain field⟩

theorem tonelli : TonelliGoal := by
  intro dimension domain field
  exact ⟨tsum_cellEnergy_ofReal dimension domain field, tsum_cellEnergy_ofReal_lt_top dimension domain field⟩

theorem energy : EnergyGoal := by
  intro dimension domain field
  exact ⟨cellEnergy_nonneg dimension domain field, cellEnergy_summable dimension domain field,
    field_norm_sq_eq_tsum dimension domain field⟩

theorem weightedEnergy : WeightedEnergyGoal := weightedColumnBound

theorem literal : LiteralConsumerGoal := by
  intro dimension domain field
  exact ⟨cellEnergy_summable dimension domain field, field_norm_sq_eq_tsum dimension domain field,
    weightedColumnBound dimension domain field⟩

theorem block : BlockGoal := ⟨coordinateEnergy, tonelli, energy, weightedEnergy, literal⟩

end Grad.CellEnergy
