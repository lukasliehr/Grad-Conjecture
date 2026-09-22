import COR12TorusEnergy

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Grad.COR12Extension

open Grad.ClosedJets
open Grad.DiskExtension.Operator
open Grad.FourierGrade

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Fact (0 < (2 * Real.pi : ℝ)) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

theorem productTorus_integral_three (field : C(ProductTorus, ℝ)) :
    (∫ point : ProductTorus, field point) =
      ∫ cell : UnitAddCircle, ∫ second : UnitAddCircle, ∫ first : UnitAddCircle,
        field ![first, second, cell] := by
  let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => UnitAddCircle) 2
  have sourceIntegrable : Integrable field :=
    field.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have splitIntegrable : Integrable
      (fun pair : UnitAddCircle × (Fin 2 → UnitAddCircle) => field (split.symm pair)) :=
    (productTorus_piFinSuccAbove_measurePreserving 2).symm.integrable_comp_of_integrable
      sourceIntegrable
  calc
    (∫ point : ProductTorus, field point) =
        ∫ pair : UnitAddCircle × (Fin 2 → UnitAddCircle), field (split.symm pair) := by
      simpa [split, Fin.insertNthEquiv, Fin.insertNth_self_removeNth] using
        (productTorus_piFinSuccAbove_measurePreserving 2).integral_comp'
          (fun pair => field (split.symm pair))
    _ = ∫ cell : UnitAddCircle, ∫ rest : Fin 2 → UnitAddCircle,
        field (split.symm (cell, rest)) := integral_prod _ splitIntegrable
    _ = ∫ cell : UnitAddCircle, ∫ second : UnitAddCircle, ∫ first : UnitAddCircle,
        field ![first, second, cell] := by
      apply integral_congr_ae
      filter_upwards [] with cell
      let pairField : C(UnitAddCircle × UnitAddCircle, ℝ) :=
        ⟨fun pair => field ![pair.1, pair.2, cell], by fun_prop⟩
      have restEquality :
          (∫ rest : Fin 2 → UnitAddCircle, field (split.symm (cell, rest))) =
            ∫ pair : UnitAddCircle × UnitAddCircle, pairField pair := by
        have transformed :=
          (volume_preserving_piFinTwo (fun _ : Fin 2 => UnitAddCircle)).integral_comp'
            pairField
        rw [← transformed]
        apply integral_congr_ae
        filter_upwards [] with rest
        change field (split.symm (cell, rest)) = field ![rest 0, rest 1, cell]
        congr 1
        funext coordinate
        fin_cases coordinate <;> rfl
      rw [restEquality]
      exact integral_prod_symm pairField
        (pairField.continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))

theorem normalizedTorus_integral_physical (field : C(TorusCellDomain, ℝ)) :
    (∫ point : ProductTorus, field (torusCellToProduct.symm point)) =
      ∫ cell : CellCircle, ∫ second : SpatialCircle, ∫ first : SpatialCircle,
        field ((first, second), cell)
          ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
  let normalized : C(ProductTorus, ℝ) :=
    field.comp ⟨torusCellToProduct.symm, torusCellToProduct.symm.continuous⟩
  change (∫ point : ProductTorus, normalized point) = _
  rw [productTorus_integral_three]
  change (∫ cell : UnitAddCircle, ∫ second : UnitAddCircle, ∫ first : UnitAddCircle,
    field ((spatialCircleToUnit.symm first, spatialCircleToUnit.symm second),
      cellCircleToUnit.symm cell)) = _
  have spatialPreserving := MeasurePreserving.symm
    spatialCircleToUnit.toMeasurableEquiv spatialCircleToUnit_measurePreserving
  have cellPreserving := MeasurePreserving.symm
    cellCircleToUnit.toMeasurableEquiv cellCircleToUnit_measurePreserving
  calc
    (∫ cell : UnitAddCircle, ∫ second : UnitAddCircle, ∫ first : UnitAddCircle,
        field ((spatialCircleToUnit.symm first, spatialCircleToUnit.symm second),
          cellCircleToUnit.symm cell)) =
      ∫ cell : UnitAddCircle, ∫ second : UnitAddCircle, ∫ first : SpatialCircle,
        field ((first, spatialCircleToUnit.symm second), cellCircleToUnit.symm cell)
          ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        filter_upwards [] with cell
        apply integral_congr_ae
        filter_upwards [] with second
        exact spatialPreserving.integral_comp'
          (fun first => field ((first, spatialCircleToUnit.symm second), cellCircleToUnit.symm cell))
    _ = ∫ cell : UnitAddCircle, ∫ second : SpatialCircle, ∫ first : SpatialCircle,
        field ((first, second), cellCircleToUnit.symm cell)
          ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        filter_upwards [] with cell
        exact spatialPreserving.integral_comp'
          (fun second => ∫ first : SpatialCircle,
            field ((first, second), cellCircleToUnit.symm cell) ∂AddCircle.haarAddCircle)
    _ = _ := cellPreserving.integral_comp'
      (fun cell => ∫ second : SpatialCircle, ∫ first : SpatialCircle,
        field ((first, second), cell) ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle)

theorem diskCellMultiIndices_eq_fourierMultiIndices (grade : ℕ) :
    diskCellMultiIndices grade = fourierMultiIndices grade := by
  apply Finset.ext
  intro index
  constructor
  · intro member
    have filtered := Finset.mem_filter.mp member
    have triple := Finset.mem_product.mp filtered.1
    have pair := Finset.mem_product.mp triple.1
    apply mem_fourierMultiIndices.mpr
    exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp pair.1),
      Nat.le_of_lt_succ (Finset.mem_range.mp pair.2),
      Nat.le_of_lt_succ (Finset.mem_range.mp triple.2), filtered.2⟩
  · intro member
    rcases mem_fourierMultiIndices.mp member with ⟨first, second, cell, order⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le first),
        Finset.mem_range.mpr (Nat.lt_succ_of_le second)⟩,
      Finset.mem_range.mpr (Nat.lt_succ_of_le cell)⟩, order⟩

/-- The literal P09 measures multiply normalized Haar by `1/4`, `1/4`
and `1/(2π)`.  This fixed factor is retained in the COR12 constants. -/
def torusMeasureFactor : ℝ := 16 * (2 * Real.pi)

theorem torusMeasureFactor_pos : 0 < torusMeasureFactor := by
  unfold torusMeasureFactor
  positivity

theorem torusDerivativeEnergy_normalization {dimension : ℕ}
    (field : TorusSmoothField dimension) (grade : ℕ) :
    normalizedTorusDerivativeEnergy grade field =
      torusMeasureFactor * torusDerivativeEnergy grade field := by
  unfold normalizedTorusDerivativeEnergy torusDerivativeEnergy
  rw [diskCellMultiIndices_eq_fourierMultiIndices, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  let integrand : C(TorusCellDomain, ℝ) :=
    ⟨fun point => ‖torusDiskCellMultiDerivative field index point‖ ^ 2, by fun_prop⟩
  change (∫ point : ProductTorus, integrand (torusCellToProduct.symm point)) = _
  rw [normalizedTorus_integral_physical]
  simp only [spatialProbabilityMeasure, cellProbabilityMeasure, integral_smul_measure,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4),
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    smul_eq_mul, integral_const_mul, torusMeasureFactor]
  dsimp only [integrand, ContinuousMap.coe_mk]
  field_simp [Real.pi_ne_zero]
  norm_num

end Grad.COR12Extension
