import AngularCharacters
import ClosedJetSmoothExtension

noncomputable section

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace Grad.Constraints

open Grad.ClosedJets Grad.PhysicalFamily

/-- N1 on literal Cartesian spatial functions. Values are not rotated. -/
def angularProjectionValue {dimension : ℕ} (mode : ℤ)
    (field : SpatialPlane → ComplexEuclidean dimension) (point : SpatialPlane) :
    ComplexEuclidean dimension :=
  (2 * Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi,
    angularCharacter mode angle • field (planeRotationAction angle point)

theorem angularProjectionValue_eq_compactIntegral {dimension : ℕ} (mode : ℤ)
    (field : SpatialPlane → ComplexEuclidean dimension) (point : SpatialPlane) :
    angularProjectionValue mode field point =
      (2 * Real.pi)⁻¹ • ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
        angularCharacter mode angle • field (planeRotationAction angle point) := by
  rw [angularProjectionValue, intervalIntegral.integral_of_le (by positivity)]
  rw [integral_Icc_eq_integral_Ioc]

theorem angularProjectionValue_smooth {dimension : ℕ} (mode : ℤ)
    {field : SpatialPlane → ComplexEuclidean dimension} (smooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (angularProjectionValue mode field) := by
  have rotationSmooth : ContDiff ℝ ∞ (fun argument : SpatialPlane × ℝ =>
      planeRotationAction argument.2 argument.1) := by
    rw [contDiff_piLp]
    intro coordinate
    fin_cases coordinate <;>
      simp [planeRotationAction, Grad.GeometryClosure.planarRotation, Matrix.vecHead, Matrix.vecTail] <;>
      fun_prop
  have integrandSmooth : ContDiff ℝ ∞ (fun argument : SpatialPlane × ℝ =>
      angularCharacter mode argument.2 • field (planeRotationAction argument.2 argument.1)) :=
    ((angularCharacter_smooth mode).comp contDiff_snd).smul (smooth.comp rotationSmooth)
  rw [← contDiffOn_univ]
  change ContDiffOn ℝ ∞ (fun point => angularProjectionValue mode field point) univ
  simp_rw [angularProjectionValue_eq_compactIntegral]
  exact (contDiffOn_const (c := ((2 * Real.pi)⁻¹ : ℝ))).smul
    (contDiffOn_compactIntegral isOpen_univ integrandSmooth.contDiffOn 0 (2 * Real.pi))

def angularClosedJet {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension) :
    ClosedJet dimension :=
  globalClosedJet (angularProjectionValue mode (smoothClosedExtension field))
    (angularProjectionValue_smooth mode (smoothClosedExtension_smooth field))

/-- Literal N1 on every point of the original closed disk. The extension
used to construct the jet disappears completely from this identity. -/
theorem angularClosedJet_value {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension)
    (point : ClosedDisk) :
    (angularClosedJet mode field).value point =
      (2 * Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi,
        angularCharacter mode angle • field.value
          (Grad.GaugeCoefficients.Radial.rotatedPoint angle point) := by
  rw [angularClosedJet, globalClosedJet_value, angularProjectionValue]
  congr 1
  apply intervalIntegral.integral_congr
  intro angle _
  have rotated := smoothClosedExtension_value field
    (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)
  simpa only [physicalRotation_eq_orthogonal,
    Grad.GaugeCoefficients.Radial.planeRotationEquiv_apply,
    Grad.GaugeCoefficients.Radial.rotatedPoint] using
      congrArg (fun value => angularCharacter mode angle • value) rotated

end Grad.Constraints
