import AKN25FullOriginalSourceNormComponents
import ANH7HighOrbits
import SCS41OriginalPolarPoint

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularSourceGraph
open Grad.SourceCollarBulk Grad.SourceCollarRestriction Grad.SourceCollarFullSource Grad.AnnularCurrentSource
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.Constraints Grad.SourceCollar
open Grad.BoundaryTrace Grad.CircularHighWeak Grad.GaugeCoefficients.Radial

/-- The actual scalar Cartesian mean constraint holds separately on every
cell and every circle. -/
theorem originalScalarCircle_mean_zero {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (mean : angularCore parameters 0 field = 0)
    (cell : ℤ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    angularCoefficient (fun angle => (field.val cell).value
      (Grad.SourceCollarDivision.polarClosedPoint radius angle nonnegative bounded)) 0 = 0 := by
  have equality := congrArg (fun candidate : ACore parameters dimension =>
    (candidate.val cell).value (axisClosedPoint radius (by rwa [abs_of_nonneg nonnegative]))) mean
  change (angularClosedJet 0 (field.val cell)).value
    (axisClosedPoint radius (by rwa [abs_of_nonneg nonnegative])) = 0 at equality
  have points (angle : ℝ) : Grad.SourceCollarDivision.polarClosedPoint radius angle nonnegative bounded =
      rotatedPoint angle (axisClosedPoint radius (by rwa [abs_of_nonneg nonnegative])) :=
    divisionPolarPoint_eq_original radius angle nonnegative bounded
  simp_rw [points]
  exact (orbitCoefficient_projection (field.val cell) _ 0).trans equality

/-- The original Cartesian radial constraint gives zero mean of the SAME
F1 circle coefficient, cell by cell. -/
theorem originalRadialCircle_mean_zero (parameters : PhaseParameters)
    (field : ACore parameters 2) (mean : radialSourceCore parameters field = 0)
    (cell : ℤ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    angularCoefficient (radialPolarField (fun angle => (field.val cell).value
      (Grad.SourceCollarDivision.polarClosedPoint radius angle nonnegative bounded))) 0 = 0 := by
  have absBound : |radius| ≤ 1 := by rwa [abs_of_nonneg nonnegative]
  have points (angle : ℝ) : Grad.SourceCollarDivision.polarClosedPoint radius angle nonnegative bounded =
      Grad.Constraints.polarClosedPoint radius absBound angle :=
    divisionPolarPoint_eq_original radius angle nonnegative bounded
  simp_rw [points]
  have zeroAt := congrArg (fun candidate : ACore parameters 2 =>
    (candidate.val cell).value (axisClosedPoint radius absBound) 0) mean
  rw [radialSourceCore_axis_value field cell radius absBound] at zeroAt
  change polarRadialMean (field.val cell) radius absBound 0 = 0 at zeroAt
  have periodic : Function.Periodic (fun angle => polarRadialComponent angle
      ((field.val cell).value (Grad.Constraints.polarClosedPoint radius absBound angle))) (2 * Real.pi) := by
    intro angle
    simp only [Grad.Constraints.polarClosedPoint_periodic radius absBound angle,
      polarRadialComponent, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have continuousField : Continuous (fun angle => (field.val cell).value
      (Grad.Constraints.polarClosedPoint radius absBound angle)) :=
    (field.val cell).value.continuous.comp (continuous_rotatedPoint_joint.comp
      (continuous_id.prodMk continuous_const))
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  rw [angularCoefficient_component _]
  · change angularCoefficient (fun angle => polarRadialComponent angle
      ((field.val cell).value (Grad.Constraints.polarClosedPoint radius absBound angle))) 0 = 0
    rw [← sourceAngularAverage_eq_coefficient _ periodic]
    simpa only [polarRadialMean, sourceAngularAverage, add_zero] using zeroAt
  · unfold radialPolarField
    exact ((Grad.Constraints.Gauges.planarComponentMap 0).continuous.comp
      ((Complex.continuous_ofReal.comp Real.continuous_cos).smul continuousField)).add
      ((Grad.Constraints.Gauges.planarComponentMap 1).continuous.comp
      ((Complex.continuous_ofReal.comp Real.continuous_sin).smul continuousField))

end Grad.ExhaustionSourceAllocation
