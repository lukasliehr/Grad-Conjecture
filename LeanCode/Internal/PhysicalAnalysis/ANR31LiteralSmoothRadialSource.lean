import ANR30ActualClosedCollarDerivative

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.WeightedTrace

def diskCoreRadialCurve (mode : ℤ) (field : ClosedJet 1) : C(ℝ, ComplexEuclidean 1) :=
  ⟨radialCoefficientJet (originalPolarValue field) mode 0,
    (radialCoefficientJet_smooth _ (originalPolarValue_smooth _) mode 0).continuous⟩

theorem diskCoreRadialCurve_smooth (mode : ℤ) (field : ClosedJet 1) :
    ContDiff ℝ ∞ (diskCoreRadialCurve mode field) :=
  radialCoefficientJet_smooth _ (originalPolarValue_smooth _) mode 0

theorem radialOrdinary_diskL2Radial_core (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : ClosedJet 1) :
    radialOrdinary 1 lower positive (diskL2Radial lower positive bounded mode (closedL2Core field)) =
      collarContinuousL2 (ComplexEuclidean 1) lower (diskCoreRadialCurve mode field) :=
  (congrArg (radialOrdinary 1 lower positive) (diskL2Radial_core lower positive bounded mode field)).trans
    (radialOrdinary_toLp 1 lower positive (diskCoreRadialCurve mode field))

theorem weakRadialLaplacian_rhs (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (high : mode ∉ lowAngularModes) (parameter : ℝ) (source : highDiskL2) :
    weakRadialLaplacian lower positive bounded mode parameter source =
      (((parameter ^ 2 * (1 - 4 / (mode : ℝ) ^ 2) : ℝ)) : ℂ) •
        diskRadialValue lower positive bounded mode (highRobinWeakInverse parameter source).val -
      radialOrdinary 1 lower positive (diskL2Radial lower positive bounded mode source.val) := by
  let decode := radialOrdinary 1 lower positive
  let bulk := diskL2Radial lower positive bounded mode (highDiskBulk (highRobinWeakInverse parameter source))
  let forcing := diskL2Radial lower positive bounded mode source.val
  let scalar : ℂ := (((parameter ^ 2 * (1 - 4 / (mode : ℝ) ^ 2) : ℝ)) : ℂ)
  have equation := congrArg decode (weakInverse_radial_rhs lower positive bounded parameter source mode high)
  have subtraction := decode.map_sub (scalar • bulk) forcing
  have multiplication := decode.map_smul scalar bulk
  have valueLaw := diskRadial_ordinary_bulk lower positive bounded mode (highRobinWeakInverse parameter source).val
  have transferred := multiplication.trans (congrArg (fun value : CollarL2 (ComplexEuclidean 1) lower => scalar • value) valueLaw)
  exact equation.trans (subtraction.trans
    (congrArg (fun value : CollarL2 (ComplexEuclidean 1) lower => value - decode forcing) transferred))

theorem weakRadialLaplacian_smoothSource (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (high : mode ∉ lowAngularModes) (parameter : ℝ) (source : highDiskL2)
    (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    weakRadialLaplacian lower positive bounded mode parameter source =
      (((parameter ^ 2 * (1 - 4 / (mode : ℝ) ^ 2) : ℝ)) : ℂ) •
        diskRadialValue lower positive bounded mode (highRobinWeakInverse parameter source).val -
      collarContinuousL2 (ComplexEuclidean 1) lower (diskCoreRadialCurve mode core) := by
  have coreLaw := (congrArg (fun value : DiskL2 1 => radialOrdinary 1 lower positive
    (diskL2Radial lower positive bounded mode value)) same).trans
      (radialOrdinary_diskL2Radial_core lower positive bounded mode core)
  exact (weakRadialLaplacian_rhs lower positive bounded mode high parameter source).trans
    (congrArg (fun value : CollarL2 (ComplexEuclidean 1) lower =>
      (((parameter ^ 2 * (1 - 4 / (mode : ℝ) ^ 2) : ℝ)) : ℂ) •
        diskRadialValue lower positive bounded mode (highRobinWeakInverse parameter source).val - value) coreLaw)

theorem weakRadialLaplacian_smoothSource_ae (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (high : mode ∉ lowAngularModes) (parameter : ℝ) (source : highDiskL2)
    (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      weakRadialLaplacian lower positive bounded mode parameter source radius =
        (((parameter ^ 2 * (1 - 4 / (mode : ℝ) ^ 2) : ℝ)) : ℂ) •
          diskRadialValue lower positive bounded mode (highRobinWeakInverse parameter source).val radius -
        diskCoreRadialCurve mode core radius := by
  let value := diskRadialValue lower positive bounded mode (highRobinWeakInverse parameter source).val
  let forcing := collarContinuousL2 (ComplexEuclidean 1) lower (diskCoreRadialCurve mode core)
  let scalar : ℂ := (((parameter ^ 2 * (1 - 4 / (mode : ℝ) ^ 2) : ℝ)) : ℂ)
  have identity := weakRadialLaplacian_smoothSource lower positive bounded mode high parameter source core same
  filter_upwards [Lp.coeFn_sub (scalar • value) forcing, Lp.coeFn_smul scalar value,
    (collarContinuous_memLp (ComplexEuclidean 1) lower (diskCoreRadialCurve mode core)).coeFn_toLp]
    with radius subtraction multiplication sourceLaw
  have pointwise := congrArg (fun field : CollarL2 (ComplexEuclidean 1) lower => field radius) identity
  exact pointwise.trans (subtraction.trans (congrArg₂ (fun first second : ComplexEuclidean 1 => first - second)
    multiplication sourceLaw))

end Grad.CircularHighRegularity
