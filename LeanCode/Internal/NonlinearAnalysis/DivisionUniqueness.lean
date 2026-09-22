import DivisionConsumer

noncomputable section

open Set Filter Topology

namespace Grad.NonlinearDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearQuotientBounds

/-- The accepted radial integral of one closed jet is continuous on the
closed disk: it is the value of the accepted `radialIntervalJet`. -/
theorem integralCoefficient_continuous {dimension : ℕ} (field : ClosedJet dimension) :
    Continuous (fun point : ClosedDisk => integralCoefficient field point) := by
  have identity : (fun point : ClosedDisk => integralCoefficient field point) =
      (radialIntervalJet 0 1 field).value :=
    funext (fun point => (radialIntervalJet_full_value field point).symm)
  rw [identity]
  exact (radialIntervalJet 0 1 field).value.continuous

/-- Off the axis, every quotient by `|y|^2` is determined by cancellation. -/
theorem quotient_unique_off_axis {dimension : ℕ} {field : ClosedJet dimension}
    (radial : IsRotationInvariant field) (origin : field.value closedOrigin = 0)
    (quotient : ClosedDisk → ComplexEuclidean dimension)
    (division : ∀ point : ClosedDisk, field.value point = ‖point.val‖ ^ 2 • quotient point)
    (point : ClosedDisk) (offAxis : point.val ≠ 0) :
    quotient point = integralCoefficient (laplacianJet field) point := by
  have nonzero : ‖point.val‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr offAxis)
  apply smul_right_injective (ComplexEuclidean dimension) nonzero
  exact (division point).symm.trans ((actualRadialDivision dimension field radial origin).1 point)

theorem spatialBasis_norm (coordinate : Fin 2) : ‖spatialBasis coordinate‖ = 1 := by
  simp [spatialBasis, PiLp.norm_single]

theorem axis_sequence_mem (index : ℕ) :
    (1 / ((index : ℝ) + 1)) • spatialBasis 0 ∈ closedUnitDisk := by
  change ‖(1 / ((index : ℝ) + 1)) • spatialBasis 0‖ ≤ 1
  have nonneg : (0 : ℝ) ≤ 1 / ((index : ℝ) + 1) := by positivity
  rw [norm_smul, spatialBasis_norm, mul_one, Real.norm_of_nonneg nonneg,
    div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg index : (0 : ℝ) ≤ index)]

/-- Off-axis points of the closed disk converging to the axis. -/
def axisSequence (index : ℕ) : ClosedDisk :=
  ⟨(1 / ((index : ℝ) + 1)) • spatialBasis 0, axis_sequence_mem index⟩

theorem axisSequence_offAxis (index : ℕ) : (axisSequence index).val ≠ 0 := by
  change (1 / ((index : ℝ) + 1)) • spatialBasis 0 ≠ 0
  apply smul_ne_zero
  · positivity
  · intro zero
    have norm := spatialBasis_norm 0
    rw [zero, norm_zero] at norm
    exact zero_ne_one norm

theorem axisSequence_tendsto : Tendsto axisSequence atTop (𝓝 closedOrigin) := by
  rw [tendsto_subtype_rng]
  change Tendsto (fun index : ℕ => (1 / ((index : ℝ) + 1)) • spatialBasis 0) atTop
    (𝓝 (0 : SpatialPlane))
  have limit := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (spatialBasis 0)
  simpa only [zero_smul] using limit

/-- O12 uniqueness, goal-only: every quotient field that is continuous on the
closed disk and divides `q0` by `|y|^2` at every closed point is the accepted
`I Δ q0`, axis value included. Off the axis this is cancellation; on the axis
it is continuity along off-axis points converging to the axis. -/
theorem quotient_unique {dimension : ℕ} {field : ClosedJet dimension}
    (radial : IsRotationInvariant field) (origin : field.value closedOrigin = 0)
    (quotient : ClosedDisk → ComplexEuclidean dimension) (continuous : Continuous quotient)
    (division : ∀ point : ClosedDisk, field.value point = ‖point.val‖ ^ 2 • quotient point)
    (point : ClosedDisk) :
    quotient point = integralCoefficient (laplacianJet field) point := by
  by_cases axis : point.val = 0
  · have pointAxis : point = closedOrigin := Subtype.ext axis
    rw [pointAxis]
    have agree : ∀ index, quotient (axisSequence index) =
        integralCoefficient (laplacianJet field) (axisSequence index) :=
      fun index => quotient_unique_off_axis radial origin quotient division _
        (axisSequence_offAxis index)
    have leftLimit : Tendsto (fun index => quotient (axisSequence index)) atTop
        (𝓝 (quotient closedOrigin)) :=
      (continuous.tendsto closedOrigin).comp axisSequence_tendsto
    have rightLimit : Tendsto (fun index => integralCoefficient (laplacianJet field) (axisSequence index))
        atTop (𝓝 (integralCoefficient (laplacianJet field) closedOrigin)) :=
      ((integralCoefficient_continuous (laplacianJet field)).tendsto closedOrigin).comp
        axisSequence_tendsto
    exact tendsto_nhds_unique (leftLimit.congr agree) rightLimit
  · exact quotient_unique_off_axis radial origin quotient division point axis

end Grad.NonlinearDivision
