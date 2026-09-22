import AKDP83GenericCompactPlanarEstimate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.CartesianStartup
open Grad.GenericCarriers Grad.PDEBootstrap Grad.ClosedJets Grad.WeightedJets

theorem startupAxialField_scale {dimension : ℕ} (scale : ℝ) (moment : StartupL2 dimension) :
    startupAxialField scale moment=(scale : ℂ) • startupAxialField 1 moment := by
  simp only [startupAxialField,Complex.ofReal_one,one_mul,smul_smul]

namespace StartupSignedFamily

/-- Unit coefficient coordinates retain the original physical axial scale. -/
def physicalNativeLowerFlux (scale : ℝ) (determinant scalar scalarFlux : StartupSignedFamily 1 1 1)
    (gradient : StartupSignedFamily 2 1 1) (direction : Fin 2) : StartupSignedFamily 3 1 1 :=
  ((((determinant.smul (-1)).sub ((scalar.shift 1).smul (scale : ℂ))).add
    ((scalarFlux.shift 1).smul (scale : ℂ))).lowerFlux ((gradient.shift 1).smul (scale : ℂ)) direction)

theorem physicalNativeLowerFlux_field (scale : ℝ) (determinant scalar scalarFlux : StartupSignedFamily 1 1 1)
    (gradient : StartupSignedFamily 2 1 1)
    (existingDeterminant existingScalar existingFlux : StartupMoments 1) (existingGradient : StartupMoments 2)
    (detSame : determinant.field=existingDeterminant.field) (scalarSame : scalar.field=existingScalar.field)
    (fluxSame : scalarFlux.field=existingFlux.field) (gradientSame : gradient.field=existingGradient.field)
    (direction : Fin 2) :
    (physicalNativeLowerFlux scale determinant scalar scalarFlux gradient direction).field=
      startupNativeLowerFlux scale existingDeterminant existingScalar existingFlux existingGradient direction := by
  rw [physicalNativeLowerFlux,lowerFlux_field]
  change startupERLowerFlux (((-1 : ℂ) • determinant.field-(scale : ℂ) • (scalar.shift 1).field)+
    (scale : ℂ) • (scalarFlux.shift 1).field) ((scale : ℂ) • (gradient.shift 1).field) direction=_
  rw [neg_one_smul,detSame,scalar.shift_one_sameAxial existingScalar scalarSame,
    scalarFlux.shift_one_sameAxial existingFlux fluxSame,gradient.shift_one_sameAxial existingGradient gradientSame]
  simp only [div_self one_ne_zero,←startupAxialField_scale]
  rfl

theorem HasSpatialGrade.physicalNativeLowerFlux {order : ℕ} (scale : ℝ)
    {determinant scalar scalarFlux : StartupSignedFamily 1 1 1} {gradient : StartupSignedFamily 2 1 1}
    (detRegular : determinant.HasSpatialGrade order) (scalarRegular : scalar.HasSpatialGrade order)
    (fluxRegular : scalarFlux.HasSpatialGrade order) (gradientRegular : gradient.HasSpatialGrade order) (direction : Fin 2) :
    (physicalNativeLowerFlux scale determinant scalar scalarFlux gradient direction).HasSpatialGrade order :=
  ((((detRegular.smul (-1)).sub ((scalarRegular.shift 1).smul (scale : ℂ))).add
    ((fluxRegular.shift 1).smul (scale : ℂ))).lowerFlux ((gradientRegular.shift 1).smul (scale : ℂ)) direction)

end StartupSignedFamily
end Grad.CartesianStartup
