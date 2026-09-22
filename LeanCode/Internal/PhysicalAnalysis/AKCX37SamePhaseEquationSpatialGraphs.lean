import AKCX36ActualPhaseRemainderGraphs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.CellWeights

/-- Every actual phase remainder in the native equation has the completed
spatial grade; q+1/q+2 are input cell reserves, never extra spatial derivatives. -/
theorem startupPhaseEquation_spatialGraphs (sigma gamma scale : ℝ)
    (nonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale) (scaleOne : scale ≤ 1)
    (order : ℕ) (field fieldFirst fieldSecond : StartupL2 3)
    (tensor tensorFirst tensorSecond : Fin 2 → Fin 2 → StartupL2 3)
    (flux fluxFirst : Fin 2 → StartupL2 3)
    (fieldRegular : ∀ weight, ∃ graph : GraphGrade 3 order weight openUnitDisk,
      base 3 order openUnitDisk (fun _ => weight) graph = field)
    (tensorRegular : ∀ outer inner weight, ∃ graph : GraphGrade 3 order weight openUnitDisk,
      base 3 order openUnitDisk (fun _ => weight) graph = tensor outer inner)
    (fluxRegular : ∀ direction weight, ∃ graph : GraphGrade 3 order weight openUnitDisk,
      base 3 order openUnitDisk (fun _ => weight) graph = flux direction)
    (fieldFirstSame : StartupRadialRelated (fun cell _ => cellWeight cell) fieldFirst field)
    (fieldSecondSame : StartupRadialRelated (fun cell _ => cellWeight cell^2) fieldSecond field)
    (tensorFirstSame : ∀ outer inner, StartupRadialRelated (fun cell _ => cellWeight cell) (tensorFirst outer inner) (tensor outer inner))
    (tensorSecondSame : ∀ outer inner, StartupRadialRelated (fun cell _ => cellWeight cell^2) (tensorSecond outer inner) (tensor outer inner))
    (fluxFirstSame : ∀ direction, StartupRadialRelated (fun cell _ => cellWeight cell) (fluxFirst direction) (flux direction)) :
    (∃ graph : GraphGrade 3 order 0 openUnitDisk,
      base 3 order openUnitDisk (fun _ => 0) graph =
        startupPhaseEquationZeroth sigma gamma scale nonnegative scaleNonnegative scaleOne 0 fieldSecond tensorSecond fluxFirst) ∧
    (∀ direction, ∃ graph : GraphGrade 3 order 0 openUnitDisk,
      base 3 order openUnitDisk (fun _ => 0) graph =
        startupPhaseEquationFlux sigma gamma scale nonnegative scaleNonnegative scaleOne fieldFirst tensorFirst flux direction) := by
  have fieldOne (direction : Fin 2) := startupScaledPhaseFirstField_spatialGraph sigma gamma scale nonnegative scaleNonnegative scaleOne
    order direction field fieldFirst (fieldRegular (order+1)) fieldFirstSame
  have fieldTwo (direction : Fin 2) := startupScaledPhaseSecondField_spatialGraph sigma gamma scale nonnegative scaleNonnegative scaleOne
    order direction direction field fieldSecond (fieldRegular (order+2)) fieldSecondSame
  have tensorOne (outer inner direction : Fin 2) := startupScaledPhaseFirstField_spatialGraph sigma gamma scale nonnegative scaleNonnegative scaleOne
    order direction (tensor outer inner) (tensorFirst outer inner) (tensorRegular outer inner (order+1)) (tensorFirstSame outer inner)
  have tensorTwo (outer inner : Fin 2) := startupScaledPhaseSecondField_spatialGraph sigma gamma scale nonnegative scaleNonnegative scaleOne
    order outer inner (tensor outer inner) (tensorSecond outer inner) (tensorRegular outer inner (order+2)) (tensorSecondSame outer inner)
  have fluxOne (direction : Fin 2) := startupScaledPhaseFirstField_spatialGraph sigma gamma scale nonnegative scaleNonnegative scaleOne
    order direction (flux direction) (fluxFirst direction) (fluxRegular direction (order+1)) (fluxFirstSame direction)
  constructor
  · refine ⟨0+(∑ outer : Fin 2, ∑ inner : Fin 2, (tensorTwo outer inner).choose)+
      (∑ direction : Fin 2, (fluxOne direction).choose)-(∑ direction : Fin 2, (fieldTwo direction).choose),?_⟩
    simp only [map_sub,map_add,map_sum,map_zero,show ∀ outer inner, base 3 order openUnitDisk (fun _ => 0) (tensorTwo outer inner).choose = _ from fun outer inner => (tensorTwo outer inner).choose_spec,
      show ∀ direction, base 3 order openUnitDisk (fun _ => 0) (fluxOne direction).choose = _ from fun direction => (fluxOne direction).choose_spec,
      show ∀ direction, base 3 order openUnitDisk (fun _ => 0) (fieldTwo direction).choose = _ from fun direction => (fieldTwo direction).choose_spec]
    rfl
  · intro direction
    refine ⟨(fluxRegular direction 0).choose+(∑ inner : Fin 2, (tensorOne direction inner inner).choose)+
      (∑ outer : Fin 2, (tensorOne outer direction outer).choose)-(2 : ℂ) • (fieldOne direction).choose,?_⟩
    simp only [map_sub,map_add,map_sum,map_smul,(fluxRegular direction 0).choose_spec,(fieldOne direction).choose_spec,
      show ∀ outer inner dir, base 3 order openUnitDisk (fun _ => 0) (tensorOne outer inner dir).choose = _ from
        fun outer inner dir => (tensorOne outer inner dir).choose_spec]
    rfl

end Grad.CartesianStartup
