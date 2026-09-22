import ANR10RadialCore
import GC20RangeExtension
import ASG5FaithfulWeightedGraph

noncomputable section
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.AnnularSourceGraph Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

instance radialDiskNormed : NormedAddCommGroup diskGrade := by infer_instance
instance radialDiskComplex : InnerProductSpace ℂ diskGrade :=
  @Submodule.innerProductSpace ℂ DiskAmbient _ _ (by infer_instance) diskGrade
instance radialDiskReal : InnerProductSpace ℝ diskGrade :=
  InnerProductSpace.rclikeToReal ℂ diskGrade
instance radialDiskPairing : Inner ℝ diskGrade := radialDiskReal.toInner
instance radialDiskModule : Module ℝ diskGrade := radialDiskReal.toNormedSpace.toModule
instance radialDiskSpace : NormedSpace ℝ diskGrade := radialDiskReal.toNormedSpace

/-- Extend the genuine coefficient graph using precisely the actual disk
H1 norm. The target is the annular C∞-core weighted graph completion. -/
theorem diskRadial_exists (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (mode : ℤ) :
    ∃ extraction : diskGrade →L[ℝ] WeightedRadialH1 1 lower,
      (∀ field, extraction (diskCoreInto field) = diskRadialCore lower positive mode field) ∧
      (∀ field, ‖extraction field‖ ≤ diskRadialBound * ‖field‖) := by
  let embed := diskCoreInto.restrictScalars ℝ
  have result := collarRange_extension (C := ClosedJet 1) (F := diskGrade)
    (T := WeightedRadialH1 1 lower) embed (diskRadialCore lower positive mode)
    diskRadialBound diskRadialBound_nonnegative (diskRadialCore_bound lower positive bounded mode)
  obtain ⟨extension, coreLaw, bound⟩ := result
  let inclusion : diskGrade →L[ℝ] (LinearMap.range embed).topologicalClosure :=
    (ContinuousLinearMap.id ℝ _).codRestrict _ (fun field => diskCoreInto_denseRange field)
  exact ⟨extension.comp inclusion, coreLaw, fun field => bound (inclusion field)⟩

def diskRadial (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (mode : ℤ) :
    diskGrade →L[ℝ] WeightedRadialH1 1 lower :=
  (diskRadial_exists lower positive bounded mode).choose

theorem diskRadial_core (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (mode : ℤ)
    (field : ClosedJet 1) :
    diskRadial lower positive bounded mode (diskCoreInto field) = diskRadialCore lower positive mode field :=
  (diskRadial_exists lower positive bounded mode).choose_spec.1 field

theorem diskRadial_bound (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (mode : ℤ)
    (field : diskGrade) :
    ‖diskRadial lower positive bounded mode field‖ ≤ diskRadialBound * ‖field‖ :=
  (diskRadial_exists lower positive bounded mode).choose_spec.2 field

/-- Both radial coordinates are those of the SAME smooth coefficient graph;
no independent derivative or boundary coordinate is inserted. -/
theorem diskRadial_coordinate_core (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : ClosedJet 1) (coordinate : Fin 2) :
    weightedRadialCoordinate 1 lower coordinate
      (diskRadial lower positive bounded mode (diskCoreInto field)) =
      diskRadialCoefficientL2 lower positive mode coordinate.val field := by
  rw [diskRadial_core]
  exact diskRadialCore_coordinate lower positive mode field coordinate

/-- The actual coefficient extraction gives the ordinary weak first derivative
on each closed collar, by the proved weighted-to-ordinary graph map. -/
theorem diskRadial_weakDerivative (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : diskGrade) :
    CollarWeakDerivative lower
      (collarH1Coordinate (ComplexEuclidean 1) lower 0
        (weightedToOrdinary 1 lower positive bounded (diskRadial lower positive bounded mode field)))
      (collarH1Coordinate (ComplexEuclidean 1) lower 1
        (weightedToOrdinary 1 lower positive bounded (diskRadial lower positive bounded mode field))) := by
  exact weightedRadial_weak 1 lower positive bounded (diskRadial lower positive bounded mode field)

end Grad.CircularHighRegularity
