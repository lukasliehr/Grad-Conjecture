import COR12TorusBridge
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section

set_option linter.style.haveILetI false

open MeasureTheory

namespace Grad.COR12Extension

open Grad.DiskExtension.Operator
open Grad.FourierGrade

local instance cor12MeasureCellPeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

def spatialCircleAddEquiv : SpatialCircle ≃+ UnitAddCircle :=
  AddCircle.equivAddCircle (4 : ℝ) 1 (by norm_num) one_ne_zero

def cellCircleAddEquiv : Grad.ClosedJets.CellCircle ≃+ UnitAddCircle :=
  AddCircle.equivAddCircle (2 * Real.pi : ℝ) 1
    (mul_ne_zero (by norm_num) Real.pi_ne_zero) one_ne_zero

theorem spatialCircleAddEquiv_apply (point : SpatialCircle) :
    spatialCircleAddEquiv point = spatialCircleToUnit point := rfl

theorem cellCircleAddEquiv_apply (point : Grad.ClosedJets.CellCircle) :
    cellCircleAddEquiv point = cellCircleToUnit point := rfl

theorem spatialCircle_haar_map :
    Measure.map spatialCircleAddEquiv AddCircle.haarAddCircle =
      AddCircle.haarAddCircle := by
  letI mappedHaar :
      (Measure.map spatialCircleAddEquiv
        AddCircle.haarAddCircle).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map AddCircle.haarAddCircle
      spatialCircleAddEquiv spatialCircleToUnit.continuous
      spatialCircleToUnit.symm.continuous
  have mappedMeasurable : Measurable
      (spatialCircleAddEquiv : SpatialCircle → UnitAddCircle) := by
    change Measurable (spatialCircleToUnit : SpatialCircle → UnitAddCircle)
    exact spatialCircleToUnit.measurable
  letI mappedProbability : IsProbabilityMeasure
      (Measure.map spatialCircleAddEquiv AddCircle.haarAddCircle) :=
    ⟨by
      rw [Measure.map_apply_of_aemeasurable
        mappedMeasurable.aemeasurable MeasurableSet.univ]
      simp⟩
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem cellCircle_haar_map :
    Measure.map cellCircleAddEquiv AddCircle.haarAddCircle =
      AddCircle.haarAddCircle := by
  letI mappedHaar :
      (Measure.map cellCircleAddEquiv
        AddCircle.haarAddCircle).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map AddCircle.haarAddCircle
      cellCircleAddEquiv cellCircleToUnit.continuous
      cellCircleToUnit.symm.continuous
  have mappedMeasurable : Measurable
      (cellCircleAddEquiv : Grad.ClosedJets.CellCircle → UnitAddCircle) := by
    change Measurable
      (cellCircleToUnit : Grad.ClosedJets.CellCircle → UnitAddCircle)
    exact cellCircleToUnit.measurable
  letI mappedProbability : IsProbabilityMeasure
      (Measure.map cellCircleAddEquiv AddCircle.haarAddCircle) :=
    ⟨by
      rw [Measure.map_apply_of_aemeasurable
        mappedMeasurable.aemeasurable MeasurableSet.univ]
      simp⟩
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem spatialCircleToUnit_measurePreserving :
    MeasurePreserving spatialCircleToUnit AddCircle.haarAddCircle
      AddCircle.haarAddCircle :=
  ⟨spatialCircleToUnit.measurable, spatialCircle_haar_map⟩

theorem cellCircleToUnit_measurePreserving :
    MeasurePreserving cellCircleToUnit AddCircle.haarAddCircle
      AddCircle.haarAddCircle :=
  ⟨cellCircleToUnit.measurable, cellCircle_haar_map⟩

end Grad.COR12Extension
