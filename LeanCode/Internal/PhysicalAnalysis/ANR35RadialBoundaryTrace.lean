import ANR34ActualClosedCollarSmoothness

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryTrace
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.WeightedTrace

private theorem polarClosedPoint_boundary (angle : ℝ) :
    polarClosedPoint 1 angle (by norm_num) le_rfl = boundaryDiskPoint (angle : CellCircle) := by
  apply Subtype.ext
  change polarPlane (1, angle) = boundaryCirclePoint (angle : CellCircle)
  rw [boundaryCirclePoint_coe, polarPlane_eq]
  simp [radialDirection, collarPlane]

theorem diskCoreRadialCurve_boundary (mode : ℤ) (field : ClosedJet 1) :
    diskCoreRadialCurve mode field 1 = diskBoundaryFourier (diskCoreInto field) (mode, 0) := by
  have functions : (fun angle => originalPolarValue field (1, angle)) =
      (fun angle : ℝ => field.value (boundaryDiskPoint (angle : CellCircle))) := by
    funext angle
    rw [originalPolarValue_closed field 1 angle (by norm_num) le_rfl, polarClosedPoint_boundary]
  change angularCoefficient (fun angle => originalPolarValue field (1, angle)) mode = _
  exact (congrArg (fun value : ℝ → ComplexEuclidean 1 => angularCoefficient value mode) functions).trans
    ((angularCoefficient_circle (fun angle : CellCircle => field.value (boundaryDiskPoint angle)) mode).trans
      (diskBoundaryFourier_core_cell field mode).symm)

/-- The actual closed-collar upper trace is exactly the same physical
boundary Fourier coefficient already used by the Robin form. -/
theorem diskRadial_upper_boundary (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (field : diskGrade) :
    weightedRadialTrace 1 lower positive bounded 1 (diskRadial lower positive bounded.le mode field) =
      diskBoundaryFourier field (mode, 0) := by
  let evaluation := lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 (mode, 0)
  apply isClosed_property diskCoreInto_denseRange
    (isClosed_eq ((weightedRadialTrace 1 lower positive bounded 1).continuous.comp
      (diskRadial lower positive bounded.le mode).continuous)
      (evaluation.continuous.comp diskBoundaryFourier.continuous)) _ field
  intro core
  have radial := congrArg (weightedRadialTrace 1 lower positive bounded 1)
    (diskRadial_core lower positive bounded.le mode core)
  have endpoint := weightedRadialTrace_core 1 lower positive bounded 1 (diskRadialSmoothCore mode core)
  have literal : (diskRadialSmoothCore mode core).val.val.1 (radialEndpointRadius lower 1) =
      diskCoreRadialCurve mode core 1 := by
    have index : (1 : Fin 2) ≠ 0 := by decide
    simp only [radialEndpointRadius, if_neg index]
    rfl
  exact radial.trans (endpoint.trans (literal.trans (diskCoreRadialCurve_boundary mode core)))

theorem diskRadialValueSection_upper (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (field : diskGrade) :
    diskRadialValueSection lower positive bounded mode field ⟨1, bounded.le, le_rfl⟩ =
      diskBoundaryFourier field (mode, 0) :=
  (diskRadialValueSection_endpoint lower positive bounded mode field 1).trans
    (diskRadial_upper_boundary lower positive bounded mode field)

end Grad.CircularHighRegularity
