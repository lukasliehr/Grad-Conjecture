import AKDW20KnownNativeFluxCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers
open Grad.OriginalCoreRealization Grad.ActualOriginalSourceFirst

/-- The known source flux core is exactly the source term in the literal
physical-scale native split; its signed derivative is not a free input. -/
theorem startupKnownNativeFluxCore_same (parameters : PhaseParameters) (scale : ℝ)
    (determinant : StartupSignedFamily 1 1 1) (known : StartupSignedFamily 2 1 1)
    (determinantCore : ACore parameters 1) (forceCore : ACore parameters 2)
    (determinantSame : determinant.field=originalSourceFieldLinear parameters determinantCore)
    (forceSame : known.field=originalSourceFieldLinear parameters forceCore) (direction : Fin 2) :
    ((determinant.smul (-1)).lowerFlux ((known.primitive.shift 1).smul (scale : ℂ)) direction).field=
      originalSourceFieldLinear parameters (startupKnownNativeFluxCore parameters scale determinantCore forceCore direction) := by
  let gradient := known.primitive.value (startupComponentEntry (2 : Fin 3) direction)
  have gradientSame : gradient.field=originalSourceFieldLinear parameters (startupKnownGradientEntryCore parameters forceCore direction) := by
    change originalValueKernel (startupComponentEntry (2 : Fin 3) direction) (startupCovariantPrimitiveKernel known.field)=_
    rw [forceSame]
    exact (startupKnownGradientEntryCore_same parameters forceCore direction).symm
  have momentSame : originalValueKernel (startupComponentEntry (2 : Fin 3) direction) (known.primitive.moment 1)=
      originalSourceFieldLinear parameters (originalSignedAxialCore parameters (startupKnownGradientEntryCore parameters forceCore direction) 1 1 1) :=
    startupSigned_sameOriginalMoment parameters gradient (startupKnownGradientEntryCore parameters forceCore direction) gradientSame 1
  rw [StartupSignedFamily.lowerFlux_field,startupERLowerFlux_linear]
  change startupLowerScalarFluxKernel direction ((-1 : ℂ) • determinant.field)-
    originalValueKernel (startupComponentEntry (2 : Fin 3) direction) ((scale : ℂ) • known.primitive.moment 1)=_
  simp only [startupKnownNativeFluxCore,map_sub,map_neg,map_smul,neg_one_smul]
  rw [determinantSame,←startupKnownDeterminantFluxCore_same parameters determinantCore direction,momentSame]

end Grad.CartesianStartup
