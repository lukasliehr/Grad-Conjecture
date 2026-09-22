import AKDW7OriginalUnitNativeSpatialEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
namespace Grad.CartesianStartup
open Grad.GenericCarriers Grad.PDEBootstrap Grad.ClosedJets Grad.WeightedJets
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.Constraints Grad.Constraints.Gauges
namespace StartupSignedFamily

theorem lowerFlux_moment {L ell : ℝ} (lower : StartupSignedFamily 1 L ell)
    (gradient : StartupSignedFamily 2 L ell) (direction : Fin 2) (power : ℕ) :
    (lower.lowerFlux gradient direction).moment power=
      startupERLowerFlux (lower.moment power) (gradient.moment power) direction := by
  unfold lowerFlux startupERLowerFlux
  split_ifs
  · change (-1 : ℂ) • originalValueKernel (startupComponentEntry 0 0) (lower.moment power)+
      (2 : ℂ) • originalValueKernel (startupComponentEntry 1 0) (startupTrueAngularInverse 1 0 (lower.moment power))-
      originalValueKernel (startupComponentEntry 2 direction) (gradient.moment power)=_
    rw [neg_one_smul]
  · rfl

theorem recoveredGradient_moment {L ell : ℝ} (vector right : StartupSignedFamily 2 L ell) (power : ℕ) :
    (vector.recoveredGradient right).moment power=
      startupRecoveredGradient (vector.moment power) (right.moment power) := rfl

theorem recoveredGradient_sourceSplit {L ell : ℝ} (vector known force : StartupSignedFamily 2 L ell) (power : ℕ) :
    (vector.recoveredGradient (known.sub force)).moment power=
      (vector.recoveredGradient (force.smul (-1))).moment power+known.primitive.moment power := by
  simp only [recoveredGradient_moment]
  change startupRecoveredGradient (vector.moment power) (known.moment power-force.moment power)=
    startupRecoveredGradient (vector.moment power) ((-1 : ℂ) • force.moment power)+
      startupCovariantPrimitiveKernel (known.moment power)
  unfold startupRecoveredGradient
  simp only [neg_one_smul,map_add,map_sub,map_neg]
  abel

/-- The actual native flux splits into one physical axial derivative of
the exact coefficient image and two genuine known-source contributions. -/
theorem physicalNativeLowerFlux_sourceSplit (scale : ℝ)
    (determinant scalar scalarFlux : StartupSignedFamily 1 1 1)
    (vector known force : StartupSignedFamily 2 1 1) (direction : Fin 2) :
    (physicalNativeLowerFlux scale determinant scalar scalarFlux
      (vector.recoveredGradient (known.sub force)) direction).field=
    (scale : ℂ) • (((scalarFlux.sub scalar).lowerFlux
      (vector.recoveredGradient (force.smul (-1))) direction).shift 1).field+
    ((determinant.smul (-1)).lowerFlux ((known.primitive.shift 1).smul (scale : ℂ)) direction).field := by
  rw [physicalNativeLowerFlux,lowerFlux_field,lowerFlux_field]
  change startupERLowerFlux (((-1 : ℂ) • determinant.field-(scale : ℂ) • scalar.moment 1)+
      (scale : ℂ) • scalarFlux.moment 1)
      ((scale : ℂ) • (vector.recoveredGradient (known.sub force)).moment 1) direction=
    (scale : ℂ) • ((scalarFlux.sub scalar).lowerFlux
      (vector.recoveredGradient (force.smul (-1))) direction).moment 1+
    startupERLowerFlux ((-1 : ℂ) • determinant.field) ((scale : ℂ) • known.primitive.moment 1) direction
  rw [lowerFlux_moment,recoveredGradient_sourceSplit]
  change startupERLowerFlux (((-1 : ℂ) • determinant.field-(scale : ℂ) • scalar.moment 1)+
      (scale : ℂ) • scalarFlux.moment 1)
      ((scale : ℂ) • ((vector.recoveredGradient (force.smul (-1))).moment 1+known.primitive.moment 1)) direction=
    (scale : ℂ) • startupERLowerFlux (scalarFlux.moment 1-scalar.moment 1)
      ((vector.recoveredGradient (force.smul (-1))).moment 1) direction+
    startupERLowerFlux ((-1 : ℂ) • determinant.field) ((scale : ℂ) • known.primitive.moment 1) direction
  simp only [startupERLowerFlux_linear,map_add,map_sub,map_smul,smul_add,smul_sub]
  abel

end StartupSignedFamily
end Grad.CartesianStartup
