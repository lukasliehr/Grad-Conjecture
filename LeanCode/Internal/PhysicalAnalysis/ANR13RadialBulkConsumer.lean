import ANR11CompletedRadialExtraction
import ANR12DiskL2Radial

noncomputable section
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.AnnularSourceGraph Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The value of the completed radial H1 graph is the Fourier coefficient
of the SAME actual disk L2 field. -/
theorem diskRadial_bulk (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (mode : ℤ)
    (field : diskGrade) :
    weightedRadialCoordinate 1 lower 0 (diskRadial lower positive bounded mode field) =
      diskL2Radial lower positive bounded mode (diskBulk field) := by
  apply isClosed_property diskCoreInto_denseRange
    (isClosed_eq ((weightedRadialCoordinate 1 lower 0).continuous.comp
      (diskRadial lower positive bounded mode).continuous)
      ((diskL2Radial lower positive bounded mode).continuous.comp diskBulk.continuous)) _ field
  intro core
  exact (diskRadial_coordinate_core lower positive bounded mode core 0).trans
    ((diskL2Radial_core lower positive bounded mode core).symm.trans
      (congrArg (diskL2Radial lower positive bounded mode) (diskBulk_core core).symm))

/-- Actual AN18 coefficient extraction: every real parameter, every actual
high L2 source, the original weighted radial graph and a uniform H1 bound. -/
theorem weakInverse_radial (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (parameter : ℝ) (source : highDiskL2) :
    let solution := highRobinWeakInverse parameter source
    let radial := diskRadial lower positive bounded mode solution.val
    weightedRadialCoordinate 1 lower 0 radial =
      diskL2Radial lower positive bounded mode (highDiskBulk solution) ∧
    ‖radial‖ ≤ (2 * diskRadialBound) * ‖source‖ ∧
    CollarWeakDerivative lower
      (collarH1Coordinate (ComplexEuclidean 1) lower 0 (weightedToOrdinary 1 lower positive bounded radial))
      (collarH1Coordinate (ComplexEuclidean 1) lower 1 (weightedToOrdinary 1 lower positive bounded radial)) := by
  dsimp only
  refine ⟨diskRadial_bulk lower positive bounded mode _, ?_, diskRadial_weakDerivative lower positive bounded mode _⟩
  have radialBound := diskRadial_bound lower positive bounded mode (highRobinWeakInverse parameter source).val
  have inverseBound := (actualHighRobinWeakSolve parameter source).2.1
  have transfer : diskRadialBound * ‖highRobinWeakInverse parameter source‖ ≤
      diskRadialBound * (2 * ‖source‖) :=
    mul_le_mul_of_nonneg_left inverseBound diskRadialBound_nonnegative
  exact radialBound.trans (transfer.trans_eq (by ring))

end Grad.CircularHighRegularity
