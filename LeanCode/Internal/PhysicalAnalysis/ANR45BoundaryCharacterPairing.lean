import ANR44HighBoundaryCharacter

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace Grad.BoundaryLift

theorem boundaryCharacter_boundary (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) (away : (0 : ℝ) ∉ tsupport test) (angle : CellCircle) :
    (boundaryCharacterJet mode vector test smooth away).value (boundaryDiskPoint angle) =
      test 1 • (fourier mode angle • vector) := by
  have unit := unitComplexCoordinate_polar 1 (by norm_num) angle
  simp only [one_smul] at unit
  change ((test ‖boundaryCirclePoint angle‖ : ℂ) * unitComplexCoordinate (boundaryCirclePoint angle) ^ mode) • vector = _
  rw [boundaryCirclePoint_norm, unit, circle_zpow_fourier, mul_smul, Complex.coe_smul]

private theorem circleCharacter_inner (mode : ℤ) (vector : ComplexEuclidean 1)
    (field : C(CellCircle, ComplexEuclidean 1)) :
    (∫ angle : CellCircle, inner ℂ (fourier mode angle • vector) (field angle)) =
      (2 * Real.pi) • inner ℂ vector (fourierCoeff field mode) := by
  have normalization := angular_inner_coefficient mode vector (fun angle : ℝ => field angle)
    (field.continuous.comp (AddCircle.continuous_mk' _))
  have coefficient := angularCoefficient_circle field mode
  have normalized := normalization.trans (congrArg (fun value : ComplexEuclidean 1 =>
    (2 * Real.pi) • inner ℂ vector value) coefficient)
  rw [← AddCircle.intervalIntegral_preimage (2 * Real.pi) (-Real.pi),
    show -Real.pi + 2 * Real.pi = Real.pi by ring,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    ← integral_Icc_eq_integral_Ioc]
  have equality : (fun angle : ℝ => inner ℂ (fourier mode (angle : CellCircle) • vector) (field angle)) =
      (fun angle => inner ℂ (cellExponential mode angle • vector) (field angle)) := by
    funext angle
    rw [show fourier mode (angle : CellCircle) = cellExponential mode angle from cellCharacter_coe _ _]
  exact (congrArg (fun function : ℝ → ℂ => ∫ angle in Icc (-Real.pi) Real.pi, function angle) equality).trans normalized

private theorem boundaryCharacter_pairing_core (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) (away : (0 : ℝ) ∉ tsupport test) (field : ClosedJet 1) :
    inner ℂ (coreBoundaryL2 (boundaryCharacterJet mode vector test smooth away)) (coreBoundaryL2 field) =
      (2 * Real.pi) • (test 1 • inner ℂ vector (diskBoundaryFourier (diskCoreInto field) (mode, 0))) := by
  have integrals : inner ℂ (coreBoundaryL2 (boundaryCharacterJet mode vector test smooth away)) (coreBoundaryL2 field) =
      test 1 • ∫ angle : CellCircle, inner ℂ (fourier mode angle • vector) (field.value (boundaryDiskPoint angle)) := by
    rw [L2.inner_def, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [coreBoundaryL2_ae (boundaryCharacterJet mode vector test smooth away), coreBoundaryL2_ae field]
      with angle first second
    rw [first, second, boundaryCharacter_boundary, inner_smul_left_eq_smul]
  have circle := circleCharacter_inner mode vector (closedBoundaryValue field)
  have coefficient := diskBoundaryFourier_core_cell field mode
  exact integrals.trans ((congrArg (fun value : ℂ => test 1 • value) circle).trans
    ((smul_comm (test 1) (2 * Real.pi) _).trans
      (congrArg (fun value : ComplexEuclidean 1 => (2 * Real.pi) • (test 1 • inner ℂ vector value)) coefficient.symm)))

/-- Ordinary dθ boundary pairing, directly on the actual completed H1 trace. -/
theorem boundaryCharacter_boundary_pairing (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) (away : (0 : ℝ) ∉ tsupport test) (field : diskGrade) :
    inner ℂ (diskBoundary (diskCoreInto (boundaryCharacterJet mode vector test smooth away))) (diskBoundary field) =
      (2 * Real.pi) • (test 1 • inner ℂ vector (diskBoundaryFourier field (mode, 0))) := by
  let jet := boundaryCharacterJet mode vector test smooth away
  let evaluation := lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 (mode, 0)
  have sourceContinuous : Continuous (fun field : diskGrade => inner ℂ (diskBoundary (diskCoreInto jet)) (diskBoundary field)) :=
    (innerSL ℂ (diskBoundary (diskCoreInto jet))).continuous.comp diskBoundary.continuous
  have targetContinuous : Continuous (fun field : diskGrade =>
      (2 * Real.pi) • (test 1 • inner ℂ vector (diskBoundaryFourier field (mode, 0)))) :=
    (((innerSL ℂ vector).continuous.comp (evaluation.continuous.comp diskBoundaryFourier.continuous)).const_smul (test 1)).const_smul
      (2 * Real.pi : ℝ)
  apply isClosed_property diskCoreInto_denseRange (isClosed_eq sourceContinuous targetContinuous) _ field
  intro core
  exact (congrArg₂ (fun first second : BoundaryL2 => inner ℂ first second) (diskBoundary_core jet) (diskBoundary_core core)).trans
    (boundaryCharacter_pairing_core mode vector test smooth away core)

end Grad.CircularHighRegularity
