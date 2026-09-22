import AEK5ActualKnownFunctional

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace Grad.AnnularCurrentSource

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.AxisCore Grad.RealFixedRanges
open Grad.AnnularSourceGraph Grad.AnnularVariational
open Grad.ActualBoundaryPrimitives

/-- The genuine graph outer tuple in the original `(F0,RF0,F2)` order.
`F0` is lowered from split angular grade one, `RF0` is the exact normalized
angular generator of that same graph, and `F2` has split grade zero. -/
def highGraphOuterTuple (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (graphs : HighRadialSourceGraphs parameters lower grade) : SourceBoundaryTuple :=
  WithLp.toLp 2 ![
    annularEndpointInclusion parameters 1 (radialEndpointRadius lower 1)
      0 0 1 0 (by omega) (by omega)
      (totalSourceTrace parameters 1 lower positive bounded 1 0 grade 1 graphs.1),
    sourceRotationTrace parameters 1 lower positive bounded 0 grade 1 graphs.1,
    totalSourceTrace parameters 1 lower positive bounded 0 0 grade 1 graphs.2]

@[simp] theorem highGraphOuterTuple_f0 (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (graphs : HighRadialSourceGraphs parameters lower grade) :
    highGraphOuterTuple parameters lower positive bounded grade graphs 0 =
      annularEndpointInclusion parameters 1 (radialEndpointRadius lower 1)
        0 0 1 0 (by omega) (by omega)
        (totalSourceTrace parameters 1 lower positive bounded 1 0 grade 1 graphs.1) := rfl

@[simp] theorem highGraphOuterTuple_rf0 (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (graphs : HighRadialSourceGraphs parameters lower grade) :
    highGraphOuterTuple parameters lower positive bounded grade graphs 1 =
      sourceRotationTrace parameters 1 lower positive bounded 0 grade 1 graphs.1 := rfl

@[simp] theorem highGraphOuterTuple_f2 (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (graphs : HighRadialSourceGraphs parameters lower grade) :
    highGraphOuterTuple parameters lower positive bounded grade graphs 2 =
      totalSourceTrace parameters 1 lower positive bounded 0 0 grade 1 graphs.2 := rfl

/-- One coherent BF2/BF13 data packet.  The weighted bulk rows are independent
norm coordinates.  The graph equalities identify them with the same physical
`F0/F2` after the exact radial tilt, while the outer equality identifies the
genuine graph traces with the original global `sourceRange`.  There are no
trace fields for `f,g,q_c,rq_v`. -/
structure ActualHighKnownData (parameters : PhaseParameters) (L lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (large : 3 ≤ angular + cell + 2) where
  weighted : HighKnownSourceBulk lower
  auxiliary : HighAuxiliarySourceBulk lower
  graphs : HighRadialSourceGraphs parameters lower (angular + cell)
  source : sourceRange parameters (angular + cell + 2) large
  datum : HighBoundaryPrimitive parameters angular cell
  innerValue : AnnularBoundary
  weightedGraph : WeightedGraphCompatibility parameters lower (angular + cell) graphs weighted
  outerGraph : highGraphOuterTuple parameters lower positive bounded (angular + cell) graphs =
    sourceOuterTrace parameters L (angular + cell) source.val

/-- Exact outer source-range convention used by BCI/AHV: the radial graph tuple
is definitionally ordered `(F0,RF0,F2)` and equals the original completed
`sourceOuterTrace`; it is never supplied as an independent boundary datum. -/
theorem ActualHighKnownData.outer_sourceRange
    {parameters : PhaseParameters} {L lower : ℝ} {positive : 0 < lower}
    {bounded : lower < 1} {angular cell : ℕ}
    {large : 3 ≤ angular + cell + 2}
    (data : ActualHighKnownData parameters L lower positive bounded angular cell large) :
    highGraphOuterTuple parameters lower positive bounded (angular + cell) data.graphs =
      sourceOuterTrace parameters L (angular + cell) data.source.val :=
  data.outerGraph

end Grad.AnnularCurrentSource
