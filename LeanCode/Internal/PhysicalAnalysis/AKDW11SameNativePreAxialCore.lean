import AKDW10OriginalUnitNativeFluxEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap
open Grad.ActualOriginalSourceMoments Grad.ActualOriginalSourceFirst Grad.OriginalCoreRealization
open Grad.Constraints Grad.Constraints.Gauges Grad.GaugeCoefficients.Physical.RadialLedger

/-- Signed representatives of one original core have identical literal
axial moments; no derivative or PDE equality is assumed. -/
theorem startupSigned_sameOriginalMoment {dimension : ℕ} (parameters : PhaseParameters)
    (family : StartupSignedFamily dimension 1 1) (core : ACore parameters dimension)
    (same : family.field=originalSourceFieldLinear parameters core) (power : ℕ) :
    family.moment power=originalSourceFieldLinear parameters (originalSignedAxialCore parameters core 1 1 power) :=
  StartupSignedFamily.moment_congr_of_field family (startupOriginalSignedFamily parameters core 1 1) same power

/-- Exact coefficient part of the same native flux, with its one signed
cell displacement identified with the genuine original core derivative. -/
theorem startupNativePreAxial_sameOriginal (parameters : PhaseParameters)
    (family : StartupSignedFamily 3 1 1)
    (force : StartupSignedFamily 2 1 1) (scalarFlux : StartupSignedFamily 1 1 1)
    (forceKernel : StartupL2 3 →L[ℂ] StartupL2 2) (scalarKernel : StartupL2 3 →L[ℂ] StartupL2 1)
    (forceSame : force.field=forceKernel family.field) (scalarSame : scalarFlux.field=scalarKernel family.field)
    (image : ACore parameters 3) (direction : Fin 2)
    (same : originalSourceFieldLinear parameters image=
      startupNativePreAxialFluxKernel forceKernel scalarKernel direction family.field) (power : ℕ) :
    (((scalarFlux.sub (family.value toroidalPartMap)).lowerFlux
      ((family.value planarPartMap).recoveredGradient (force.smul (-1))) direction).shift power).field=
      originalSourceFieldLinear parameters (originalSignedAxialCore parameters image 1 1 power) := by
  refine startupSigned_sameOriginalMoment parameters
    ((scalarFlux.sub (family.value toroidalPartMap)).lowerFlux
      ((family.value planarPartMap).recoveredGradient (force.smul (-1))) direction) image ?_ power
  rw [StartupSignedFamily.lowerFlux_field,StartupSignedFamily.recoveredGradient_field]
  change startupERLowerFlux (scalarFlux.field-originalValueKernel toroidalPartMap family.field)
    (startupRecoveredGradient (originalValueKernel planarPartMap family.field) ((-1 : ℂ) • force.field)) direction=_
  rw [neg_one_smul,forceSame,scalarSame]
  exact (startupNativePreAxialFluxKernel_value forceKernel scalarKernel family.field direction).symm.trans same.symm

end Grad.CartesianStartup
