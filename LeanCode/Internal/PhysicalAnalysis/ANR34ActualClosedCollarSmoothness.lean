import ANR32ActualClassicalRadialSystem
import ANR33RadialODEBootstrap

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.WeightedTrace

/-- AN19/V4 qualitative closed-collar regularity for the same constructed
weak inverse and the exact original smooth source. All radial orders and
both endpoints follow from the derived weak equation and primitive proof. -/
theorem weakInverse_closedCollar_smooth (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (high : mode ∉ lowAngularModes) (parameter : ℝ) (source : highDiskL2)
    (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    ContDiffOn ℝ ∞
      (radialSectionExtension 1 lower bounded.le
        (diskRadialValueSection lower positive bounded mode (highRobinWeakInverse parameter source).val))
      (Icc lower 1) := by
  have existence := weakInverse_classical_radial_system lower positive bounded mode high parameter source core same
  obtain ⟨flux, _actual, first, second⟩ := existence
  have regularity := radialSystem_smooth 1 lower positive bounded mode
    (((parameter ^ 2 * (1 - 4 / (mode : ℝ) ^ 2) : ℝ)) : ℂ)
    (diskCoreRadialCurve mode core) (diskCoreRadialCurve_smooth mode core)
    (radialSectionExtension 1 lower bounded.le
      (diskRadialValueSection lower positive bounded mode (highRobinWeakInverse parameter source).val))
    flux first second
  exact regularity.1

theorem diskRadialValueSection_endpoint (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (field : diskGrade) (endpoint : Fin 2) :
    diskRadialValueSection lower positive bounded mode field
      ⟨radialEndpointRadius lower endpoint, radialEndpointRadius_mem lower bounded.le endpoint⟩ =
      weightedRadialTrace 1 lower positive bounded endpoint (diskRadial lower positive bounded.le mode field) :=
  weightedRadialSection_endpoint 1 lower positive bounded endpoint _

end Grad.CircularHighRegularity
