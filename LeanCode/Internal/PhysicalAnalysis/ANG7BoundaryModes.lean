import ANG5ContractiveModes

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.CircularHighWeak
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.BoundaryTrace
open Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger
attribute [local instance] diskComplexNormedSpace

private theorem boundaryRotation (angle : ℝ) :
    rotatedPoint angle (boundaryDiskPoint (0 : CellCircle)) = boundaryDiskPoint (angle : CellCircle) := by
  apply Subtype.ext
  change planeRotation angle (boundaryCirclePoint (0 : CellCircle)) = boundaryCirclePoint (angle : CellCircle)
  rw [show (0 : CellCircle) = ((0 : ℝ) : CellCircle) from rfl, boundaryCirclePoint_coe, boundaryCirclePoint_coe]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [planeRotation, collarPlane]

theorem boundaryCoefficient_angular (mode : ℤ) (field : ClosedJet 1) :
    fourierCoeff (fun angle : CellCircle => field.value (boundaryDiskPoint angle)) mode =
      (angularClosedJet mode field).value (boundaryDiskPoint 0) := by
  have orbit := orbitCoefficient_projection field (boundaryDiskPoint 0) mode
  simp_rw [boundaryRotation] at orbit
  exact (angularCoefficient_circle (fun angle : CellCircle => field.value (boundaryDiskPoint angle)) mode).symm.trans orbit

theorem diskBoundaryFourier_angular_core (mode other cell : ℤ) (field : ClosedJet 1) :
    diskBoundaryFourier (diskCoreInto (angularClosedJet mode field)) (other, cell) =
      if other = mode then diskBoundaryFourier (diskCoreInto field) (other, cell) else 0 := by
  by_cases cellZero : cell = 0
  · subst cell
    have projected := congrArg (fun jet : ClosedJet 1 => jet.value (boundaryDiskPoint 0))
      (angularClosedJet_projection other mode field)
    have composed := (diskBoundaryFourier_core_cell (angularClosedJet mode field) other).trans
      ((boundaryCoefficient_angular other (angularClosedJet mode field)).trans projected)
    refine composed.trans ?_
    split_ifs with equal
    · exact (boundaryCoefficient_angular other field).symm.trans (diskBoundaryFourier_core_cell field other).symm
    · rfl
  · refine (diskBoundaryFourier_core_zero _ _ _ cellZero).trans ?_
    split_ifs
    · exact (diskBoundaryFourier_core_zero field other cell cellZero).symm
    · rfl

/-- The genuine H1 trace of an angular projection has precisely the same
angular Fourier mask, on all boundary coordinates. -/
theorem diskBoundaryFourier_angular (mode : ℤ) (field : diskGrade) (index : ℤ × ℤ) :
    diskBoundaryFourier (diskAngularMode mode field) index =
      if index.1 = mode then diskBoundaryFourier field index else 0 := by
  let evaluation := lp.evalCLM ℂ (fun _ : ℤ × ℤ => Grad.GenericCarriers.PhysicalValue 1) 2 index
  apply isClosed_property diskCoreInto_denseRange
    (isClosed_eq (evaluation.continuous.comp (diskBoundaryFourier.continuous.comp (diskAngularMode mode).continuous))
      (by split_ifs
          · exact evaluation.continuous.comp diskBoundaryFourier.continuous
          · exact continuous_const)) _ field
  intro core
  change diskBoundaryFourier (diskAngularMode mode (diskCoreInto core)) index = _
  exact (congrArg (fun value : diskGrade => diskBoundaryFourier value index)
    (diskAngularMode_core mode core)).trans (diskBoundaryFourier_angular_core mode index.1 index.2 core)

theorem diskBoundaryFourier_angular_contract (mode : ℤ) (field : diskGrade) :
    ‖diskBoundaryFourier (diskAngularMode mode field)‖ ≤ ‖diskBoundaryFourier field‖ := by
  apply lp.norm_mono (by norm_num)
  intro index
  rw [diskBoundaryFourier_angular]
  split_ifs
  · exact le_refl _
  · exact (norm_zero.le).trans (norm_nonneg (diskBoundaryFourier field index))

theorem diskBoundary_angular_contract (mode : ℤ) (field : diskGrade) :
    ‖diskBoundary (diskAngularMode mode field)‖ ≤ ‖diskBoundary field‖ := by
  have fourier := diskBoundaryFourier_angular_contract mode field
  have squares := pow_le_pow_left₀ (norm_nonneg _) fourier 2
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact ((diskBoundary_fourier_norm_sq (diskAngularMode mode field)).le.trans
    (mul_le_mul_of_nonneg_left squares (by positivity))).trans_eq
    (diskBoundary_fourier_norm_sq field).symm

end Grad.CircularHighWeak
