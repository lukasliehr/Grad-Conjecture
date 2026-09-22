import SBT16BulkBoundaryCompatibility

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceBoundaryTrace
open Grad.ClosedJets Grad.CartesianState Grad.AxisCore Grad.QuotientProjection
open Grad.SourceCollarDivision Grad.SourceCollarBulk Grad.FlatSourceProjection
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.SourceCollar Grad.BoundaryTrace

/-- The actual three known source coordinates of the physical outer row.
The angular derivative is the derivative of F0 itself. -/
def physicalKnownSourceTuple (bulk : AnnularBulkSource) (angle : ℝ) : ComplexEuclidean 3 :=
  WithLp.toLp 2 ![bulk.F0 angle, deriv bulk.F0 angle, bulk.F2 angle]

/-- Zero prescribed physical datum leaves all three source coordinates
unchanged. The theorem identifies each with its original full Fourier
field, including the genuine angular derivative. -/
theorem homogeneousOuter_preserves_knownSource (parameters : PhaseParameters) (L epsilon : ℝ)
    (state : ACore parameters 3) (source : CartesianSourceCore parameters) (axialAngle polarAngle : ℝ) :
    physicalKnownSourceTuple
      (attachHomogeneousPhysicalOuterDatum
        (actualAnnularBulkSource parameters L epsilon state 1 (by norm_num) axialAngle source)).bulk polarAngle =
      WithLp.toLp 2 ![
        coreValue (tangentialBoundaryCore parameters source.1)
          (boundaryDiskPoint (polarAngle : CellCircle)) axialAngle 0,
        coreValue (rotationCore parameters (tangentialBoundaryCore parameters source.1))
          (boundaryDiskPoint (polarAngle : CellCircle)) axialAngle 0,
        (L : ℂ)⁻¹ * coreValue source.2.2 (boundaryDiskPoint (polarAngle : CellCircle)) axialAngle 0] := by
  rw [attachHomogeneousPhysicalOuterDatum_bulk]
  unfold physicalKnownSourceTuple
  rw [← sourceForce_physical_outer, ← sourceRotation_physical_outer, ← sourceFourth_physical_outer]

theorem prescribedOuter_preserves_knownSource (bulk : AnnularBulkSource) (datum : ℝ → ℂ) (angle : ℝ) :
    physicalKnownSourceTuple (attachPhysicalOuterDatum bulk datum).bulk angle =
      physicalKnownSourceTuple bulk angle := rfl

/-- Literal BS37 on the original completed fourfold source Hilbert space,
same nu and analytic width. The constant is independent of the inner
radius. All three endpoints belong to the actual completed radial
derivative graph, including RF0; they are not free boundary coordinates. -/
def OuterSourceTraceGoal : Prop :=
  ∀ (parameters : PhaseParameters) (L : ℝ), 0 < L → ∀ power : ℕ,
    (∀ source : ZAmbient parameters (power + 2),
      ‖sourceOuterTrace parameters L power source‖ ≤ sourceOuterTraceConstant L power * ‖source‖) ∧
    (∀ source : ZAmbient parameters (power + 2),
      ‖sourceOuterTrace parameters L power source‖ ^ 2 =
        ∑ coordinate : Fin 3, ∑' mode : ℤ × ℤ,
          Real.exp (2 * boundaryPhase parameters mode.2) * annularFrequency mode.1 mode.2 ^ (2 * power) *
            ‖sourceBoundaryCoefficient parameters power
              (sourceOuterTrace parameters L power source coordinate) mode‖ ^ 2) ∧
    (∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1 / 2)
        (source : ZAmbient parameters (power + 2)) (mode : ℤ × ℤ),
      let graphF := completedForceTangential lower positive (bounded.trans (by norm_num)) parameters power source
      let graphR := completedForceAngular lower positive (bounded.trans (by norm_num)) parameters power source
      let graphH := completedFourthSource lower positive (bounded.trans (by norm_num)) parameters L power source
      ((((annularFrequency mode.1 mode.2 : ℂ)⁻¹) • graphF.val 0 mode,
          ((annularFrequency mode.1 mode.2 : ℂ)⁻¹) • graphF.val 1 mode),
          sourceOuterTrace parameters L power source 0 mode) ∈ radialEndpointGraph 1 lower ∧
      ((graphR.val 0 mode, graphR.val 1 mode), sourceOuterTrace parameters L power source 1 mode) ∈
          radialEndpointGraph 1 lower ∧
      ((graphH.val 0 mode, graphH.val 1 mode), sourceOuterTrace parameters L power source 2 mode) ∈
          radialEndpointGraph 1 lower)

theorem actualOuterSourceTrace : OuterSourceTraceGoal := by
  intro parameters L positive power
  refine ⟨sourceOuterTrace_bound parameters L positive power,
    fun source => sourceBoundaryTuple_literal_norm parameters power _, ?_⟩
  intro lower lowerPositive bounded source mode
  exact ⟨forceOuterTrace_bulk_endpoint lower lowerPositive (bounded.trans (by norm_num)) parameters power source mode,
    rotationOuterTrace_bulk_endpoint lower lowerPositive (bounded.trans (by norm_num)) parameters power source mode,
    fourthOuterTrace_bulk_endpoint lower lowerPositive (bounded.trans (by norm_num)) parameters L power source mode⟩

/-- Immediate original-source consumer of the nonzero known-source tuple.
No conclusion replaces homogeneous physical boundary data by a zero trace. -/
theorem originalSourceOuterTrace_ready : OuterSourceTraceGoal := actualOuterSourceTrace

end Grad.SourceBoundaryTrace
