import AKBL29LiteralFixedGaugeMeans

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.BoundaryTrace
open Grad.Constraints Grad.Constraints.Gauges Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger

 theorem startupPolarClosedPoint_norm (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) :
    ‖(Grad.Constraints.polarClosedPoint radius bounded angle).val‖ = |radius| := by
  change ‖planeRotationEquiv angle (axisClosedPoint radius bounded).val‖ = _
  rw [LinearIsometryEquiv.norm_map]
  change ‖WithLp.toLp 2 ![radius,(0 : ℝ)]‖ = _
  rw [PiLp.norm_eq_of_L2]
  simp [Fin.sum_univ_two,Real.sqrt_sq_eq_abs]

/-- Every actual disk point has the literal closed polar representation. -/
 theorem startupClosedPoint_polar (point : ClosedDisk) :
    ∃ angle : ℝ, Grad.Constraints.polarClosedPoint ‖point.val‖
      (by rw [abs_of_nonneg (norm_nonneg _)]; exact point.property) angle = point := by
  obtain ⟨angle,same⟩ := startupPoint_polar_rotation point.val
  refine ⟨angle,Subtype.ext ?_⟩
  change planeRotationEquiv angle (axisClosedPoint ‖point.val‖ _).val = point.val
  have axis : (axisClosedPoint ‖point.val‖ (by rw [abs_of_nonneg (norm_nonneg _)]; exact point.property)).val =
      ‖point.val‖ • spatialDirection 0 := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [axisClosedPoint,spatialDirection]
  rw [axis]
  exact same

/-- The literal two gauge means force C0=0 on the genuine punctured field,
using one unchanged circle. Continuity at the axis is not a premise. -/
 theorem startupPuncturedComplement_zero_of_gaugeMeans (raw : Spatial → PhysicalValue 3)
    (continuousRaw : ContinuousOn raw (openUnitDisk \ {(0 : Spatial)}))
    (radius : ℝ) (positive : 0 < radius) (inside : radius < 1) (bounded : |radius| ≤ 1) (angle : ℝ)
    (tangential : angularCoefficient (fun polar => polarTangentialComponent polar
      (planarPartMap (raw (Grad.Constraints.polarClosedPoint radius bounded polar).val))) 0 = 0)
    (scalar : angularCoefficient (fun polar => toroidalPartMap
      (raw (Grad.Constraints.polarClosedPoint radius bounded polar).val)) 0 = 0) :
    cartesianComplementValue (fun other : ClosedDisk => raw other.val)
      (Grad.Constraints.polarClosedPoint radius bounded angle) = 0 := by
  let point := Grad.Constraints.polarClosedPoint radius bounded angle
  have pointNorm : ‖point.val‖ = radius := (startupPolarClosedPoint_norm radius bounded angle).trans (abs_of_pos positive)
  obtain ⟨localized,same⟩ := startupCircle_continuousLocalization raw continuousRaw point.val
    (by rw [pointNorm]; exact positive) (by rw [pointNorm]; exact inside)
  have localPolar (polar : ℝ) : localized (Grad.Constraints.polarClosedPoint radius bounded polar) =
      raw (Grad.Constraints.polarClosedPoint radius bounded polar).val := by
    apply same
    rw [startupPolarClosedPoint_norm,pointNorm,abs_of_pos positive]
  have result := startupComplement_zero_of_gaugeMeans localized localized.continuous radius bounded angle
    (by simpa only [localPolar] using tangential) (by simpa only [localPolar] using scalar)
  exact (startupComplement_norm_locality _ localized point (fun other normSame => (same other normSame).symm)).trans result

end Grad.CartesianStartup
