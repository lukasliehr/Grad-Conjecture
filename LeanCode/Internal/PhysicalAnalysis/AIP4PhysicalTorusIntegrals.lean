import AIP3CompactExtension
import COR12TorusNormalization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Grad.InteriorPeriodization
open Grad.COR12Extension

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

theorem productTorus_integral_three_vector (field : C(ProductTorus, ComplexEuclidean 1)) :
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
      let pairField : C(UnitAddCircle × UnitAddCircle, ComplexEuclidean 1) :=
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

theorem normalizedTorus_integral_physical_vector (field : C(TorusCellDomain, ComplexEuclidean 1)) :
    (∫ point : ProductTorus, field (torusCellToProduct.symm point)) =
      ∫ cell : CellCircle, ∫ second : SpatialCircle, ∫ first : SpatialCircle,
        field ((first, second), cell)
          ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
  let normalized : C(ProductTorus, ComplexEuclidean 1) :=
    field.comp ⟨torusCellToProduct.symm, torusCellToProduct.symm.continuous⟩
  change (∫ point : ProductTorus, normalized point) = _
  rw [productTorus_integral_three_vector]
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

theorem spatialHaar_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : SpatialCircle → E) :
    (∫ point, field point ∂AddCircle.haarAddCircle) =
      (1 / 4 : ℝ) • ∫ coordinate in Set.Ioc (-2 : ℝ) 2, field (coordinate : SpatialCircle) := by
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.integral_preimage (4 : ℝ) (-2 : ℝ) field]
  norm_num

end Grad.InteriorPeriodization
