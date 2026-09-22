import AXF26CartesianFlatRange

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.QuotientProjection
open Grad.AxisSplit Grad.AxisJet Grad.AxisCore Grad.PhysicalFamily
open Grad.GaugeCoefficients.Radial

/-- One fixed real radial profile for every cell and every grade. -/
def fixedRadialProfile : SpatialPlane → ℝ := rotationAverage jetBump

theorem fixedRadialProfile_smooth : ContDiff ℝ ∞ fixedRadialProfile := by
  have swap : ContDiff ℝ ∞ (fun argument : SpatialPlane × ℝ => (argument.2, argument.1)) :=
    contDiff_snd.prodMk contDiff_fst
  have rotation := physicalRotation_contDiff.comp swap
  have bump : ContDiff ℝ ∞ (fun point : SpatialPlane => jetBump point) := jetBump.contDiff
  have integrand : ContDiff ℝ ∞ (fun argument : SpatialPlane × ℝ =>
      jetBump (planeRotationAction argument.2 argument.1)) :=
    bump.comp rotation
  rw [← contDiffOn_univ]
  change ContDiffOn ℝ ∞ (fun point => rotationAverage jetBump point) univ
  simp_rw [rotationAverage_eq_compactIntegral]
  exact (contDiffOn_const (c := ((2 * Real.pi)⁻¹ : ℝ))).smul
    (contDiffOn_compactIntegral isOpen_univ integrand.contDiffOn 0 (2 * Real.pi))

theorem fixedRadialProfile_radial (angle : ℝ) (point : SpatialPlane) :
    fixedRadialProfile (planeRotationAction angle point) = fixedRadialProfile point :=
  rotationAverage_rotation jetBump angle point

theorem fixedRadialProfile_vanish (point : SpatialPlane) (outside : 1 / 4 ≤ ‖point‖) :
    fixedRadialProfile point = 0 := by
  have vanish (angle : ℝ) : jetBump (planeRotationAction angle point) = 0 := by
    apply Function.notMem_support.mp
    rw [jetBump_support, Metric.mem_ball, dist_zero_right, physicalRotation_norm, not_lt]
    exact outside
  simp only [fixedRadialProfile, rotationAverage, vanish]
  simp

theorem fixedRadialProfile_one (point : SpatialPlane) (inside : ‖point‖ ≤ 1 / 8) :
    fixedRadialProfile point = 1 := by
  have one (angle : ℝ) : jetBump (planeRotationAction angle point) = 1 := by
    apply jetBump.one_of_mem_closedBall
    simpa only [Metric.mem_closedBall, dist_zero_right, physicalRotation_norm,
      jetBump_rIn] using inside
  change rotationAverage jetBump point = 1
  simp only [rotationAverage, one, intervalIntegral.integral_const, sub_zero,
    smul_smul, inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul]

theorem fixedRadialProfile_scaled (cell : ℤ) (point : SpatialPlane) :
    fixedRadialProfile (cellFrequency cell • point) = (2 * Real.pi)⁻¹ •
      ∫ angle in (0 : ℝ)..2 * Real.pi, profileScalarZero cell (planeRotation angle point) := by
  unfold fixedRadialProfile rotationAverage profileScalarZero
  congr 1
  apply intervalIntegral.integral_congr
  intro angle _
  change jetBump (planeRotationAction angle (cellFrequency cell • point)) =
    jetBump (cellFrequency cell • planeRotation angle point)
  rw [physicalRotation_eq_orthogonal, (planeRotationEquiv angle).map_smul]
  rfl

/-- Literal M28/BS6 common scaled profile, not just an equivalent cutoff. -/
theorem radialValueInsertion_fixedProfile {parameters : PhaseParameters} {dimension : ℕ}
    (data : AxisSmoothCore parameters dimension) (cell : ℤ) (point : ClosedDisk) :
    ((radialValueInsertion data).val cell).value point =
      fixedRadialProfile (cellFrequency cell • point.val) • data.val cell := by
  change (angularClosedJet 0 (profileJetZero cell (data.val cell))).value point = _
  rw [angularClosedJet_value, fixedRadialProfile_scaled]
  simp only [angularCharacter_zero_mode, one_smul]
  change (2 * Real.pi)⁻¹ •
    (∫ angle in (0 : ℝ)..2 * Real.pi,
      profileScalarZero cell (planeRotation angle point.val) • data.val cell) = _
  rw [intervalIntegral.integral_smul_const, smul_smul]
  rfl

theorem radialFirstInsertion_fixedProfile {parameters : PhaseParameters} {dimension : ℕ}
    (direction : Fin 2) (data : AxisSmoothCore parameters dimension)
    (cell : ℤ) (point : ClosedDisk) :
    ((radialFirstInsertion direction data).val cell).value point =
      (point.val direction * fixedRadialProfile (cellFrequency cell • point.val)) • data.val cell := by
  change point.val direction • ((radialValueInsertion data).val cell).value point = _
  rw [radialValueInsertion_fixedProfile, smul_smul]

end Grad.FlatSourceProjection
