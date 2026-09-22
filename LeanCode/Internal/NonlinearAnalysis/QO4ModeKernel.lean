import QO3AngularCoordinates

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

open scoped Topology
open Filter

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit Grad.AxisJet Grad.QuotientProjection
open Grad.NonlinearDivision

variable {parameters : PhaseParameters}

theorem starCoordinate_ne_zero {point : SpatialPlane} (offAxis : point ≠ 0) :
    signedComplexCoordinate (-1) point ≠ 0 := by
  intro vanishes
  have first : point 0 = 0 := by
    simpa [signedComplexCoordinate] using congrArg Complex.re vanishes
  have second : point 1 = 0 := by
    have imaginary := congrArg Complex.im vanishes
    simpa [signedComplexCoordinate] using imaginary
  apply offAxis
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> assumption

/-- Multiplication by z-bar is injective on the actual smooth closed-disk
coefficient carrier, including at the axis by continuity. No normed inverse
of multiplication or off-axis domain restriction is introduced. -/
theorem starZMulCore_eq_zero {dimension : ℕ} (field : ACore parameters dimension)
    (annihilated : starZMulCore parameters field = 0) : field = 0 := by
  apply acore_ext
  intro cell point
  have offAxisValue (argument : ClosedDisk) (offAxis : argument.val ≠ 0) :
      (field.val cell).value argument = 0 := by
    have equality := congrArg (fun source : ACore parameters dimension => (source.val cell).value argument) annihilated
    rw [starZMulCore_jet, coordinateMultiplyJet_value] at equality
    change signedComplexCoordinate (-1) argument.val • (field.val cell).value argument = 0 at equality
    exact (smul_eq_zero.mp equality).resolve_left (starCoordinate_ne_zero offAxis)
  change (field.val cell).value point = 0
  by_cases axis : point.val = 0
  · have pointAxis : point = closedOrigin := Subtype.ext axis
    rw [pointAxis]
    have converges : Tendsto (fun index => (field.val cell).value (axisSequence index)) atTop
        (𝓝 ((field.val cell).value closedOrigin)) :=
      ((field.val cell).value.continuous.tendsto closedOrigin).comp axisSequence_tendsto
    have zeroLimit : Tendsto (fun index => (field.val cell).value (axisSequence index)) atTop (𝓝 0) := by
      simpa only [offAxisValue _ (axisSequence_offAxis _)] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ComplexEuclidean dimension)) atTop (𝓝 0))
    exact tendsto_nhds_unique converges zeroLimit
  · exact offAxisValue point axis

theorem modeProjection_eq_zero_of_raw_mean (field : SmoothQuotient parameters)
    (meanZero : angularCore parameters 0
      (starZMulCore parameters (field 0) + zMulCore parameters (field 1)) = 0) :
    modeProjection parameters field = 0 := by
  have doubled : (2 : ℂ) • starZMulCore parameters (firstMode parameters field) = 0 :=
    (rawFirstPair_mean field).symm.trans meanZero
  have coordinateZero : starZMulCore parameters (firstMode parameters field) = 0 :=
    (smul_eq_zero.mp doubled).resolve_left (by norm_num)
  have modeZero := starZMulCore_eq_zero (firstMode parameters field) coordinateZero
  rw [modeProjection_apply, modeZero, map_zero]
  funext coordinate
  fin_cases coordinate <;> rfl

end Grad.NonlinearRange
