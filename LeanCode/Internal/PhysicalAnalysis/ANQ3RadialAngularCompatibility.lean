import ANQ2CompletedRadialSequence
import ANG29OriginalSourceConsumer

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Complex scalar compatibility of both genuine radial coordinates,
without changing the accepted real radial graph carrier. -/
theorem diskRadial_coordinate_smul (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (coordinate : Fin 2) (scalar : ℂ) (field : diskGrade) :
    weightedRadialCoordinate 1 lower coordinate (diskRadial lower positive bounded mode (scalar • field)) =
      scalar • weightedRadialCoordinate 1 lower coordinate (diskRadial lower positive bounded mode field) := by
  let mapping := (weightedRadialCoordinate 1 lower coordinate).comp (diskRadial lower positive bounded mode)
  have leftContinuous : Continuous (fun field : diskGrade => mapping (scalar • field)) :=
    mapping.continuous.comp (continuous_id.const_smul scalar)
  have rightContinuous : Continuous (fun field : diskGrade => scalar • mapping field) :=
    mapping.continuous.const_smul scalar
  apply isClosed_property diskCoreInto_denseRange (isClosed_eq leftContinuous rightContinuous) _ field
  intro core
  have first := congrArg (fun current : diskGrade =>
    weightedRadialCoordinate 1 lower coordinate (diskRadial lower positive bounded mode current))
      (diskCoreInto.map_smul scalar core).symm
  have second := diskRadial_coordinate_core lower positive bounded mode (scalar • core) coordinate
  have third := (diskRadialCoefficientL2 lower positive mode coordinate.val).map_smul scalar core
  have fourth := congrArg (fun radial => scalar • radial)
    (diskRadial_coordinate_core lower positive bounded mode core coordinate).symm
  exact first.trans (second.trans (third.trans fourth))

theorem diskRadial_norm_sq_smul (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (scalar : ℂ) (field : diskGrade) :
    ‖diskRadial lower positive bounded mode (scalar • field)‖ ^ 2 =
      ‖scalar‖ ^ 2 * ‖diskRadial lower positive bounded mode field‖ ^ 2 := by
  simp only [weightedRadialH1_norm_sq, diskRadial_coordinate_smul, norm_smul, mul_pow, mul_add]

/-- Extracting mode m after the completed angular projection at m leaves
the actual entire radial H1 graph unchanged, including its weak slope. -/
theorem diskRadial_angular_self (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : diskGrade) :
    diskRadial lower positive bounded mode (diskAngularMode mode field) =
      diskRadial lower positive bounded mode field := by
  apply weightedRadial_value_injective 1 lower positive bounded
  exact (diskRadial_bulk lower positive bounded mode (diskAngularMode mode field)).trans
    ((congrArg (diskL2Radial lower positive bounded mode) (diskAngularMode_bulk mode field)).trans
      ((diskL2Radial_mode_self lower positive bounded mode (diskBulk field)).trans
        (diskRadial_bulk lower positive bounded mode field).symm))

theorem diskRadial_highAngular_self (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : highDiskGrade) :
    diskRadial lower positive bounded mode (highDiskMode mode field).val =
      diskRadial lower positive bounded mode field.val :=
  diskRadial_angular_self lower positive bounded mode field.val

end Grad.CircularHighRegularity
