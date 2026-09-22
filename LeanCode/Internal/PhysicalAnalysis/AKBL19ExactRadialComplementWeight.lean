import AKBL18SamePuncturedGaugeInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.Constraints Grad.Constraints.Gauges Grad.PhysicalFamily Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.AnalyticWeights.Calculus

 theorem startupCharacter_radial_smul {dimension : ℕ} (mode : ℤ)
    (weight : ClosedDisk → ℝ) (radial : ∀ first second : ClosedDisk, ‖first.val‖ = ‖second.val‖ → weight first = weight second)
    (raw : ClosedDisk → PhysicalValue dimension) (point : ClosedDisk) :
    closedCharacterProjection mode (fun other => weight other • raw other) point =
      weight point • closedCharacterProjection mode raw point := by
  rw [closedCharacterProjection_integral,closedCharacterProjection_integral]
  have weightAt (angle : ℝ) : weight (Grad.GaugeCoefficients.Radial.rotatedPoint angle point) = weight point :=
    radial _ point (LinearIsometryEquiv.norm_map (planeRotationEquiv angle) point.val)
  simp_rw [weightAt,smul_comm (angularCharacter mode _) (weight point)]
  rw [intervalIntegral.integral_smul]
  exact smul_comm _ _ _

 theorem startupAverage_radial_smul
    (weight : ClosedDisk → ℝ) (radial : ∀ first second : ClosedDisk, ‖first.val‖ = ‖second.val‖ → weight first = weight second)
    (raw : ClosedDisk → PhysicalValue 2) (point : ClosedDisk) :
    closedEquivariantValue (fun other => weight other • raw other) point =
      weight point • closedEquivariantValue raw point := by
  rw [closedEquivariantValue,startupCharacter_radial_smul 1 weight radial,
    startupCharacter_radial_smul (-1) weight radial]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul,smul_add,closedEquivariantValue]

 theorem startupTangential_radial_smul
    (weight : ClosedDisk → ℝ) (radial : ∀ first second : ClosedDisk, ‖first.val‖ = ‖second.val‖ → weight first = weight second)
    (raw : ClosedDisk → PhysicalValue 2) (point : ClosedDisk) :
    closedTangentialValue (fun other => weight other • raw other) point =
      weight point • closedTangentialValue raw point := by
  rw [closedTangentialValue,startupAverage_radial_smul weight radial,
    startupAverage_radial_smul weight radial,radial (orthogonalClosedPoint cartesianReflectionEquiv point) point
      (LinearIsometryEquiv.norm_map _ _)]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul,← smul_sub,smul_comm (1/2 : ℂ),closedTangentialValue]

/-- Exact radial conjugation commutes with the true fixed complement on
arbitrary rough closed values, with no derivative or axis regularity premise. -/
 theorem startupComplement_radial_smul
    (weight : ClosedDisk → ℝ) (radial : ∀ first second : ClosedDisk, ‖first.val‖ = ‖second.val‖ → weight first = weight second)
    (raw : ClosedDisk → PhysicalValue 3) (point : ClosedDisk) :
    cartesianComplementValue (fun other => weight other • raw other) point =
      weight point • cartesianComplementValue raw point := by
  have planarSame : (fun other => planarPartMap (weight other • raw other)) =
      (fun other => weight other • planarPartMap (raw other)) := by
    funext other
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul]
  have scalarSame : (fun other => toroidalPartMap (weight other • raw other)) =
      (fun other => weight other • toroidalPartMap (raw other)) := by
    funext other
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul]
  rw [cartesianComplementValue,planarSame,scalarSame,startupTangential_radial_smul weight radial,
    startupCharacter_radial_smul 0 weight radial]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul,smul_add,cartesianComplementValue]

 theorem startupComplement_originalWeight (sigma gamma ell : ℝ) (cell : ℤ)
    (raw : ClosedDisk → PhysicalValue 3) (point : ClosedDisk) :
    cartesianComplementValue (fun other => physicalWeight sigma gamma ell cell other.val • raw other) point =
      physicalWeight sigma gamma ell cell point.val • cartesianComplementValue raw point := by
  apply startupComplement_radial_smul
  intro first second sameNorm
  simp only [physicalWeight,sameNorm]

end Grad.CartesianStartup
