import AKBP23ActualFirstRowsDivDiv
import AKBP6FixedTensorRadialCovariance

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.Constraints Grad.Constraints.Gauges Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger

namespace StartupRadialRelated
variable {symbol : ℤ → Spatial → ℝ}

theorem neg {dimension : ℕ} {weighted original : StartupL2 dimension}
    (same : StartupRadialRelated symbol weighted original) : StartupRadialRelated symbol (-weighted) (-original) := by
  simpa only [neg_one_smul] using same.smul (-1 : ℂ)

theorem radialPoint {input output : ℕ} {weighted original : StartupL2 input}
    (same : StartupRadialRelated symbol weighted original) (mapping : OperatorValue input output)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (radial : ∀ cell point, symbol cell (orthogonal point) = symbol cell point) :
    StartupRadialRelated symbol (startupPointKernel mapping orthogonal weighted) (startupPointKernel mapping orthogonal original) := by
  filter_upwards [(startupOrthogonal_disk_preserving orthogonal).quasiMeasurePreserving.ae same,
    startupPointKernel_field_ae mapping orthogonal weighted,startupPointKernel_field_ae mapping orthogonal original]
    with point same weightedValue originalValue
  intro cell
  rw [weightedValue cell,originalValue cell,same cell,radial]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul]

variable (radial : ∀ cell (first second : Spatial), ‖first‖ = ‖second‖ → symbol cell first = symbol cell second)

include radial in
theorem radialAverage {weighted original : StartupL2 2} (same : StartupRadialRelated symbol weighted original) :
    StartupRadialRelated symbol (originalAverageKernel weighted) (originalAverageKernel original) := by
  have rotates : ∀ cell angle point, symbol cell (planeRotationEquiv angle point) = symbol cell point :=
    fun cell angle point => radial cell _ point (LinearIsometryEquiv.norm_map _ _)
  exact ((same.angular rotates (angularCharacter 1) (angularCharacter_smooth 1)).value positiveHelicity).add
    ((same.angular rotates (angularCharacter (-1)) (angularCharacter_smooth (-1))).value negativeHelicity)

include radial in
theorem radialTangential {weighted original : StartupL2 2} (same : StartupRadialRelated symbol weighted original) :
    StartupRadialRelated symbol (originalTangentialKernel weighted) (originalTangentialKernel original) := by
  exact ((same.radialAverage radial).sub ((same.radialAverage radial).radialPoint reflectionValueMap cartesianReflectionEquiv
    (fun cell point => radial cell _ point (LinearIsometryEquiv.norm_map _ _)))).smul (1/2)

include radial in
theorem radialCircle {weighted original : StartupL2 3} (same : StartupRadialRelated symbol weighted original) :
    StartupRadialRelated symbol (originalCircleKernel weighted) (originalCircleKernel original) := by
  have rotates : ∀ cell angle point, symbol cell (planeRotationEquiv angle point) = symbol cell point :=
    fun cell angle point => radial cell _ point (LinearIsometryEquiv.norm_map _ _)
  exact same.sub ((((same.value planarPartMap).radialTangential radial).value planarInclusionMap).add
    (((same.value toroidalPartMap).angular rotates (angularCharacter 0) (angularCharacter_smooth 0)).value toroidalInclusionMap))

include radial in
theorem radialPrimitive {weighted original : StartupL2 2} (same : StartupRadialRelated symbol weighted original) :
    StartupRadialRelated symbol (startupCovariantPrimitiveKernel weighted) (startupCovariantPrimitiveKernel original) := by
  have rotates : ∀ cell angle point, symbol cell (planeRotationEquiv angle point) = symbol cell point :=
    fun cell angle point => radial cell _ point (LinearIsometryEquiv.norm_map _ _)
  exact (same.angular rotates (fun angle => ((angle * Real.cos angle : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp (contDiff_id.mul Real.contDiff_cos))).sub
      ((same.angular rotates (fun angle => ((angle * Real.sin angle : ℝ) : ℂ))
        (Complex.ofRealCLM.contDiff.comp (contDiff_id.mul Real.contDiff_sin))).value quarterValueMap)

include radial in
theorem recoveredGradient {vector rawVector right rawRight : StartupL2 2}
    (vectorSame : StartupRadialRelated symbol vector rawVector) (rightSame : StartupRadialRelated symbol right rawRight) :
    StartupRadialRelated symbol (startupRecoveredGradient vector right) (startupRecoveredGradient rawVector rawRight) :=
  (vectorSame.sub (vectorSame.radialAverage radial)).add
    ((rightSame.add ((vectorSame.value quarterValueMap).smul 2)).radialPrimitive radial)

include radial in
theorem sourceFlux {weighted original : StartupL2 2} (same : StartupRadialRelated symbol weighted original) :
    StartupRadialRelated symbol (startupERSourceFlux weighted) (startupERSourceFlux original) :=
  ((same.radialAverage radial).value quarterValueMap).smul (1/2)

theorem lowerScalar {determinant rawDeterminant scalarMoment rawScalarMoment scalarFluxMoment rawScalarFluxMoment : StartupL2 1}
    (scale : ℝ) (detSame : StartupRadialRelated symbol determinant rawDeterminant)
    (scalarSame : StartupRadialRelated symbol scalarMoment rawScalarMoment)
    (fluxSame : StartupRadialRelated symbol scalarFluxMoment rawScalarFluxMoment) :
    StartupRadialRelated symbol (startupERLowerScalar scale determinant scalarMoment scalarFluxMoment)
      (startupERLowerScalar scale rawDeterminant rawScalarMoment rawScalarFluxMoment) :=
  (detSame.neg.sub (scalarSame.axial scale)).add (fluxSame.axial scale)

include radial in
theorem lowerFlux {lower rawLower : StartupL2 1} {gradient rawGradient : StartupL2 2}
    (lowerSame : StartupRadialRelated symbol lower rawLower) (gradientSame : StartupRadialRelated symbol gradient rawGradient)
    (direction : Fin 2) :
    StartupRadialRelated symbol (startupERLowerFlux lower gradient direction) (startupERLowerFlux rawLower rawGradient direction) := by
  have rotates : ∀ cell angle point, symbol cell (planeRotationEquiv angle point) = symbol cell point :=
    fun cell angle point => radial cell _ point (LinearIsometryEquiv.norm_map _ _)
  unfold startupERLowerFlux
  split_ifs
  · exact (((lowerSame.value (startupComponentEntry 0 0)).neg).add
      (((lowerSame.trueInverse rotates 0).value (startupComponentEntry 1 0)).smul 2)).sub
        (gradientSame.value (startupComponentEntry 2 direction))
  · exact ((((lowerSame.trueInverse rotates 0).value (startupComponentEntry 0 0)).smul (-2)).sub
      (lowerSame.value (startupComponentEntry 1 0))).sub (gradientSame.value (startupComponentEntry 2 direction))

include radial in
theorem threeRowTensor {force rawForce flux rawFlux : StartupL2 2} {scalar rawScalar : StartupL2 1}
    (forceSame : StartupRadialRelated symbol force rawForce) (scalarSame : StartupRadialRelated symbol scalar rawScalar)
    (fluxSame : StartupRadialRelated symbol flux rawFlux) (outer inside : Fin 2) :
    StartupRadialRelated symbol (startupThreeRowTensor force scalar flux outer inside)
      (startupThreeRowTensor rawForce rawScalar rawFlux outer inside) := by
  apply StartupRadialRelated.principalRows
    (fun cell angle point => radial cell _ point (LinearIsometryEquiv.norm_map _ _))
  intro row
  fin_cases row
  · exact forceSame.value planarInclusionMap
  · exact scalarSame.value toroidalInclusionMap
  · exact fluxSame.value planarInclusionMap

end StartupRadialRelated
end Grad.CartesianStartup
