import AKCO14ActualAllPowerKnownTensor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 3000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState Grad.WeightedJets
open Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger

private theorem signedPrimitive_cellwise : StartupCellwise startupCovariantPrimitiveKernel :=
  (startupAngularKernel_cellwise _ _ _).sub
    ((originalValueKernel_cellwise _).comp (startupAngularKernel_cellwise _ _ _))

private theorem signedTrueInverse_cellwise : StartupCellwise (startupTrueAngularInverse 1 0) :=
  (startupAngularKernel_cellwise _ _ _).comp
    ((StartupCellwise.id 1).sub (startupAngularKernel_cellwise _ _ _))

namespace StartupSignedFamily
variable {dimension : ℕ} {L ell : ℝ}

def value {input output : ℕ} (family : StartupSignedFamily input L ell) (mapping : OperatorValue input output) :
    StartupSignedFamily output L ell := family.map (originalValueKernel mapping) (originalValueKernel_cellwise mapping)

def circle (family : StartupSignedFamily 3 L ell) : StartupSignedFamily 3 L ell :=
  family.map originalCircleKernel originalCircleKernel_cellwise

def average (family : StartupSignedFamily 2 L ell) : StartupSignedFamily 2 L ell :=
  family.map originalAverageKernel originalAverageKernel_cellwise

def primitive (family : StartupSignedFamily 2 L ell) : StartupSignedFamily 2 L ell :=
  family.map startupCovariantPrimitiveKernel signedPrimitive_cellwise

def recoveredGradient (vector right : StartupSignedFamily 2 L ell) : StartupSignedFamily 2 L ell :=
  (vector.sub vector.average).add ((right.add ((vector.value quarterValueMap).smul 2)).primitive)

theorem recoveredGradient_field (vector right : StartupSignedFamily 2 L ell) :
    (vector.recoveredGradient right).field = startupRecoveredGradient vector.field right.field := rfl

def trueInverse (family : StartupSignedFamily 1 L ell) : StartupSignedFamily 1 L ell :=
  family.map (startupTrueAngularInverse 1 0) signedTrueInverse_cellwise

theorem shift_one_sameAxial (family : StartupSignedFamily dimension L ell)
    (existing : StartupMoments dimension) (sameBase : family.field = existing.field) :
    (family.shift 1).field = startupAxialField (ell/L) (existing.moment 1) := by
  apply Lp.ext
  filter_upwards [family.same 1,startupAxialField_ae (ell/L) (existing.moment 1) existing.field existing.first_related]
    with point signed axial
  apply lp.ext
  funext cell
  change family.moment 1 point cell = _
  rw [signed cell,pow_one,axial cell,sameBase]
  congr 1
  unfold startupAxialFrequency
  push_cast
  ring

def lowerFlux (lower : StartupSignedFamily 1 L ell) (axialGradient : StartupSignedFamily 2 L ell)
    (direction : Fin 2) : StartupSignedFamily 3 L ell :=
  (if direction = 0 then
    ((lower.value (startupComponentEntry 0 0)).smul (-1)).add
      ((lower.trueInverse.value (startupComponentEntry 1 0)).smul 2)
   else ((lower.trueInverse.value (startupComponentEntry 0 0)).smul (-2)).sub
      (lower.value (startupComponentEntry 1 0))).sub
    (axialGradient.value (startupComponentEntry 2 direction))

theorem lowerFlux_field (lower : StartupSignedFamily 1 L ell) (axialGradient : StartupSignedFamily 2 L ell)
    (direction : Fin 2) : (lower.lowerFlux axialGradient direction).field =
    startupERLowerFlux lower.field axialGradient.field direction := by
  unfold lowerFlux startupERLowerFlux
  split_ifs
  · change (-1 : ℂ) • originalValueKernel (startupComponentEntry 0 0) lower.field +
      (2 : ℂ) • originalValueKernel (startupComponentEntry 1 0) (startupTrueAngularInverse 1 0 lower.field) -
      originalValueKernel (startupComponentEntry 2 direction) axialGradient.field = _
    rw [neg_one_smul]
  · rfl

def nativeLowerFlux (determinant scalar scalarFlux : StartupSignedFamily 1 L ell)
    (gradient : StartupSignedFamily 2 L ell) (direction : Fin 2) : StartupSignedFamily 3 L ell :=
  ((((determinant.smul (-1)).sub (scalar.shift 1)).add (scalarFlux.shift 1)).lowerFlux (gradient.shift 1) direction)

/-- Literal lower flux equality with the existing native carrier. The
frequency shifts consume only the SAME already available natural moments. -/
theorem nativeLowerFlux_field (determinant scalar scalarFlux : StartupSignedFamily 1 L ell)
    (gradient : StartupSignedFamily 2 L ell)
    (existingDeterminant existingScalar existingFlux : StartupMoments 1) (existingGradient : StartupMoments 2)
    (detSame : determinant.field = existingDeterminant.field) (scalarSame : scalar.field = existingScalar.field)
    (fluxSame : scalarFlux.field = existingFlux.field) (gradientSame : gradient.field = existingGradient.field)
    (direction : Fin 2) :
    (nativeLowerFlux determinant scalar scalarFlux gradient direction).field =
      startupNativeLowerFlux (ell/L) existingDeterminant existingScalar existingFlux existingGradient direction := by
  rw [nativeLowerFlux,lowerFlux_field]
  change startupERLowerFlux (((-1 : ℂ) • determinant.field - (scalar.shift 1).field) + (scalarFlux.shift 1).field)
    (gradient.shift 1).field direction = _
  rw [neg_one_smul,detSame,scalar.shift_one_sameAxial existingScalar scalarSame,
    scalarFlux.shift_one_sameAxial existingFlux fluxSame,gradient.shift_one_sameAxial existingGradient gradientSame]
  rfl

end StartupSignedFamily
end Grad.CartesianStartup
