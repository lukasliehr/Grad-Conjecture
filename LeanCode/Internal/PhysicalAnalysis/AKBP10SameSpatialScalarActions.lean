import AKBP9SameCutoffDivDivEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

namespace StartupRadialRelated
variable {scalar : Spatial → ℝ}

theorem point {input output : ℕ} {weighted original : StartupL2 input}
    (same : StartupRadialRelated (fun _ => scalar) weighted original)
    (mapping : OperatorValue input output) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (radial : ∀ point, scalar (orthogonal point) = scalar point) :
    StartupRadialRelated (fun _ => scalar) (startupPointKernel mapping orthogonal weighted)
      (startupPointKernel mapping orthogonal original) := by
  filter_upwards [(startupOrthogonal_disk_preserving orthogonal).quasiMeasurePreserving.ae same,
    startupPointKernel_field_ae mapping orthogonal weighted,startupPointKernel_field_ae mapping orthogonal original]
      with point same value raw
  intro cell
  rw [value cell,raw cell,same cell,radial]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul]

/-- A common spatial multiplier passes through the full mixed-cell matrix
sum. This does not assert commutation of a cell-dependent phase or moment. -/
theorem matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    {weighted original : StartupL2 input} (same : StartupRadialRelated (fun _ => scalar) weighted original) :
    StartupRadialRelated (fun _ => scalar) (originalMatrixKernel admissible family coherent weighted)
      (originalMatrixKernel admissible family coherent original) := by
  filter_upwards [same,startupMatrix_allCell_hasSum_ae admissible family coherent weighted,
    startupMatrix_allCell_hasSum_ae admissible family coherent original] with point same weightedSum originalSum
  intro output
  have multiplied := (originalSum output).const_smul (scalar point)
  apply (weightedSum output).unique
  apply multiplied.congr_fun
  intro input
  rw [same input]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul]

variable (radial : ∀ first second : Spatial, ‖first‖ = ‖second‖ → scalar first = scalar second)

include radial in
theorem average {weighted original : StartupL2 2} (same : StartupRadialRelated (fun _ => scalar) weighted original) :
    StartupRadialRelated (fun _ => scalar) (originalAverageKernel weighted) (originalAverageKernel original) := by
  have rotates : ∀ (cell : ℤ) angle point, (fun _ => scalar) cell (planeRotationEquiv angle point) = scalar point :=
    fun _ angle point => radial _ point (LinearIsometryEquiv.norm_map _ _)
  exact ((same.angular rotates (angularCharacter 1) (angularCharacter_smooth 1)).value positiveHelicity).add
    ((same.angular rotates (angularCharacter (-1)) (angularCharacter_smooth (-1))).value negativeHelicity)

include radial in
theorem tangential {weighted original : StartupL2 2} (same : StartupRadialRelated (fun _ => scalar) weighted original) :
    StartupRadialRelated (fun _ => scalar) (originalTangentialKernel weighted) (originalTangentialKernel original) := by
  exact ((same.average radial).sub ((same.average radial).point reflectionValueMap cartesianReflectionEquiv
    (fun point => radial _ point (LinearIsometryEquiv.norm_map _ _)))).smul (1/2)

include radial in
theorem complement {weighted original : StartupL2 3} (same : StartupRadialRelated (fun _ => scalar) weighted original) :
    StartupRadialRelated (fun _ => scalar) (originalComplementKernel weighted) (originalComplementKernel original) := by
  have rotates : ∀ (cell : ℤ) angle point, (fun _ => scalar) cell (planeRotationEquiv angle point) = scalar point :=
    fun _ angle point => radial _ point (LinearIsometryEquiv.norm_map _ _)
  exact (((same.value planarPartMap).tangential radial).value planarInclusionMap).add
    (((same.value toroidalPartMap).angular rotates (angularCharacter 0) (angularCharacter_smooth 0)).value toroidalInclusionMap)

include radial in
theorem circle {weighted original : StartupL2 3} (same : StartupRadialRelated (fun _ => scalar) weighted original) :
    StartupRadialRelated (fun _ => scalar) (originalCircleKernel weighted) (originalCircleKernel original) :=
  same.sub (same.complement radial)

include radial in
theorem current {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge))
    {weighted original : StartupL2 3} (same : StartupRadialRelated (fun _ => scalar) weighted original) :
    StartupRadialRelated (fun _ => scalar) (originalCurrentKernel admissible gauge coherent inverseCoherent weighted)
      (originalCurrentKernel admissible gauge coherent inverseCoherent original) := by
  exact same.sub (((same.matrix admissible (fullGaugeFamily gauge) (fullGaugeFamily_coherent gauge coherent)).complement radial).matrix
    admissible (complementExtensionFamily admissible gauge)
      (complementExtensionFamily_coherent admissible gauge coherent inverseCoherent))

end StartupRadialRelated
end Grad.CartesianStartup
