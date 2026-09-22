import AXF17CanonicalCompletion

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet Grad.AxisCore
open Grad.GaugeCoefficients.Radial

theorem profileScalarZero_vanish_ge (cell : ℤ) (point : SpatialPlane)
    (outside : (4 * cellFrequency cell)⁻¹ ≤ ‖point‖) :
    profileScalarZero cell point = 0 := by
  apply Function.notMem_support.mp
  change cellFrequency cell • point ∉ Function.support ⇑jetBump
  rw [jetBump_support, Metric.mem_ball, dist_zero_right, not_lt, norm_smul,
    Real.norm_of_nonneg (cellFrequency_pos cell).le]
  have scaled := mul_le_mul_of_nonneg_left outside (cellFrequency_pos cell).le
  have cancel : cellFrequency cell * (4 * cellFrequency cell)⁻¹ = 1 / 4 := by
    rw [mul_inv]
    rw [show cellFrequency cell * (4⁻¹ * (cellFrequency cell)⁻¹) =
      (cellFrequency cell * (cellFrequency cell)⁻¹) * 4⁻¹ from by ring,
      mul_inv_cancel₀ (cellFrequency_pos cell).ne', one_mul]
    norm_num
  rw [cancel] at scaled
  exact scaled

/-- Averaging the fixed bump preserves its exact scaled open support,
including vanishing on the cap circle, in every Fourier cell. -/
theorem radialValueInsertion_vanish {parameters : PhaseParameters} {dimension : ℕ}
    (data : AxisSmoothCore parameters dimension) (cell : ℤ) (point : ClosedDisk)
    (outside : (4 * cellFrequency cell)⁻¹ ≤ ‖point.val‖) :
    ((radialValueInsertion data).val cell).value point = 0 := by
  change (angularClosedJet 0 (profileJetZero cell (data.val cell))).value point = 0
  rw [angularClosedJet_value]
  have integrand : ∀ angle : ℝ,
      angularCharacter 0 angle • (profileJetZero cell (data.val cell)).value
        (rotatedPoint angle point) = 0 := by
    intro angle
    change angularCharacter 0 angle •
      (profileScalarZero cell (planeRotation angle point.val) • data.val cell) = 0
    rw [profileScalarZero_vanish_ge cell _ (by simpa only [planeRotation_norm] using outside)]
    simp
  simp_rw [integrand]
  simp

theorem radialFirstInsertion_vanish {parameters : PhaseParameters} {dimension : ℕ}
    (direction : Fin 2) (data : AxisSmoothCore parameters dimension)
    (cell : ℤ) (point : ClosedDisk)
    (outside : (4 * cellFrequency cell)⁻¹ ≤ ‖point.val‖) :
    ((radialFirstInsertion direction data).val cell).value point = 0 := by
  change point.val direction • ((radialValueInsertion data).val cell).value point = 0
  rw [radialValueInsertion_vanish data cell point outside, smul_zero]

end Grad.FlatSourceProjection
