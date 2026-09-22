import ANR13RadialBulkConsumer

noncomputable section
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.GaugeCoefficients.Radial

private theorem polarClosedPoint_rotate_zero (radius angle : ℝ) (nonnegative : 0 ≤ radius)
    (bounded : radius ≤ 1) :
    rotatedPoint angle (polarClosedPoint radius 0 nonnegative bounded) =
      polarClosedPoint radius angle nonnegative bounded := by
  apply Subtype.ext
  change planeRotation angle (polarPlane (radius, 0)) = polarPlane (radius, angle)
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [planeRotation, polarPlane, collarPlane, mul_comm]

/-- Every radial coefficient is literally the accepted angular projection
at the point on the same physical circle, including both collar endpoints. -/
theorem radialCoefficient_projection_value (field : ClosedJet 1) (mode : ℤ) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    radialCoefficientJet (originalPolarValue field) mode 0 radius =
      (angularClosedJet mode field).value (polarClosedPoint radius 0 nonnegative bounded) := by
  have functions : (fun angle => originalPolarValue field (radius, angle)) =
      (fun angle => field.value (rotatedPoint angle (polarClosedPoint radius 0 nonnegative bounded))) := by
    funext angle
    rw [originalPolarValue_closed _ radius angle nonnegative bounded, polarClosedPoint_rotate_zero]
  exact (congrArg (fun value : ℝ → ComplexEuclidean 1 => angularCoefficient value mode) functions).trans
    (orbitCoefficient_projection field (polarClosedPoint radius 0 nonnegative bounded) mode)

theorem radialCoefficient_mode_self (field : ClosedJet 1) (mode : ℤ) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    radialCoefficientJet (originalPolarValue (angularClosedJet mode field)) mode 0 radius =
      radialCoefficientJet (originalPolarValue field) mode 0 radius := by
  rw [radialCoefficient_projection_value _ mode radius nonnegative bounded,
    angularClosedJet_projection, if_pos rfl,
    radialCoefficient_projection_value _ mode radius nonnegative bounded]

private theorem diskRadialCoefficientL2_self (lower : ℝ) (positive : 0 < lower) (mode : ℤ)
    (field : ClosedJet 1) :
    diskRadialCoefficientL2 lower positive mode 0 (angularClosedJet mode field) =
      diskRadialCoefficientL2 lower positive mode 0 field := by
  apply Lp.ext
  filter_upwards [radialToLp_ae lower
    (radialCoefficientJet (originalPolarValue (angularClosedJet mode field)) mode 0)
    (radialCoefficientJet_smooth _ (originalPolarValue_smooth _) mode 0).continuous,
    radialToLp_ae lower (radialCoefficientJet (originalPolarValue field) mode 0)
    (radialCoefficientJet_smooth _ (originalPolarValue_smooth _) mode 0).continuous,
    annular_interior_ae lower positive] with radius first second inside
  exact first.trans ((congrArg (fun value : ComplexEuclidean 1 => Real.sqrt radius • value)
    (radialCoefficient_mode_self field mode radius inside.1.le inside.2.le)).trans second.symm)

theorem diskL2Radial_mode_self (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : DiskL2 1) :
    diskL2Radial lower positive bounded mode (diskMode mode field) =
      diskL2Radial lower positive bounded mode field := by
  apply isClosed_property closedL2Core_denseRange
    (isClosed_eq ((diskL2Radial lower positive bounded mode).continuous.comp (diskMode mode).continuous)
      (diskL2Radial lower positive bounded mode).continuous) _ field
  intro core
  exact (congrArg (diskL2Radial lower positive bounded mode) (diskMode_core mode core)).trans
    ((diskL2Radial_core lower positive bounded mode (angularClosedJet mode core)).trans
      ((diskRadialCoefficientL2_self lower positive mode core).trans
        (diskL2Radial_core lower positive bounded mode core).symm))

/-- Literal AN19 multiplier coefficient on the same radial Fourier field. -/
theorem diskL2Radial_B (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (high : mode ∉ lowAngularModes) (field : DiskL2 1) :
    diskL2Radial lower positive bounded mode (diskB field) =
      ((1 - 4 / (mode : ℝ) ^ 2 : ℝ) : ℂ) • diskL2Radial lower positive bounded mode field := by
  exact (diskL2Radial_mode_self lower positive bounded mode (diskB field)).symm.trans
    ((congrArg (diskL2Radial lower positive bounded mode) (diskB_literal_high mode high field)).trans
      (((diskL2Radial lower positive bounded mode).map_smul _ _).trans
        (congrArg (fun value : RadialL2 1 lower => ((1 - 4 / (mode : ℝ) ^ 2 : ℝ) : ℂ) • value)
          (diskL2Radial_mode_self lower positive bounded mode field))))

end Grad.CircularHighRegularity
