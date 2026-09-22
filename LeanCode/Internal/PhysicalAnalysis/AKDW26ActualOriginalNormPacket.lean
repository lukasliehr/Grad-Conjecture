import AKDW22SameKnownNativeFlux
import AKDW25ActualNativeFluxLowerGraphs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 4000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.NonlinearProduct
open Grad.ActualOriginalSourceMoments Grad.OriginalCoreRealization Grad.SourceCollarCoefficients Grad.ActualOriginalSourceFirst
open Grad.Constraints Grad.Constraints.Gauges Grad.GaugeCoefficients.Physical.RadialLedger

/-- A product carrier avoids a large dependent structure recursor. -/
def StartupOriginalUnitNormData (parameters : PhaseParameters) (length radius : ℝ) :=
  OriginalUnitRankState parameters length radius ×
    ACore parameters 3 ×
    StartupSignedFamily 3 1 1 ×
    ACore parameters 2 ×
    ACore parameters 1 ×
    ACore parameters 1 ×
    StartupSignedFirstFamily 2 1 1 ×
    StartupSignedFirstFamily 1 1 1 ×
    StartupSignedFirstFamily 1 1 1

namespace StartupOriginalUnitNormData
variable {parameters : PhaseParameters} {length radius : ℝ}
abbrev coefficient (data : StartupOriginalUnitNormData parameters length radius) : OriginalUnitRankState parameters length radius := data.1
abbrev core (data : StartupOriginalUnitNormData parameters length radius) : ACore parameters 3 := data.2.1
abbrev field (data : StartupOriginalUnitNormData parameters length radius) : StartupSignedFamily 3 1 1 := data.2.2.1
abbrev forceCore (data : StartupOriginalUnitNormData parameters length radius) : ACore parameters 2 := data.2.2.2.1
abbrev thirdCore (data : StartupOriginalUnitNormData parameters length radius) : ACore parameters 1 := data.2.2.2.2.1
abbrev determinantCore (data : StartupOriginalUnitNormData parameters length radius) : ACore parameters 1 := data.2.2.2.2.2.1
abbrev knownForce (data : StartupOriginalUnitNormData parameters length radius) : StartupSignedFirstFamily 2 1 1 := data.2.2.2.2.2.2.1
abbrev knownThird (data : StartupOriginalUnitNormData parameters length radius) : StartupSignedFirstFamily 1 1 1 := data.2.2.2.2.2.2.2.1
abbrev determinant (data : StartupOriginalUnitNormData parameters length radius) : StartupSignedFirstFamily 1 1 1 := data.2.2.2.2.2.2.2.2
end StartupOriginalUnitNormData

/-- SAME original cores and signed source families for the faithful
physical-L unit equation; no norm or equation is postulated here. -/
def StartupOriginalUnitNormPacket (parameters : PhaseParameters) (length radius : ℝ) :=
  { data : StartupOriginalUnitNormData parameters length radius //
    data.field.field=(originalSourceMoments parameters data.core).field ∧
    data.knownForce.field=(originalSourceMoments parameters data.forceCore).field ∧
    data.knownThird.field=(originalSourceMoments parameters data.thirdCore).field ∧
    data.determinant.field=(originalSourceMoments parameters data.determinantCore).field }

namespace StartupOriginalUnitNormPacket
variable {parameters : PhaseParameters} {length radius : ℝ}
abbrev coefficient (packet : StartupOriginalUnitNormPacket parameters length radius) : OriginalUnitRankState parameters length radius := packet.val.coefficient
abbrev core (packet : StartupOriginalUnitNormPacket parameters length radius) : ACore parameters 3 := packet.val.core
abbrev field (packet : StartupOriginalUnitNormPacket parameters length radius) : StartupSignedFamily 3 1 1 := packet.val.field
abbrev forceCore (packet : StartupOriginalUnitNormPacket parameters length radius) : ACore parameters 2 := packet.val.forceCore
abbrev thirdCore (packet : StartupOriginalUnitNormPacket parameters length radius) : ACore parameters 1 := packet.val.thirdCore
abbrev determinantCore (packet : StartupOriginalUnitNormPacket parameters length radius) : ACore parameters 1 := packet.val.determinantCore
abbrev knownForce (packet : StartupOriginalUnitNormPacket parameters length radius) : StartupSignedFirstFamily 2 1 1 := packet.val.knownForce
abbrev knownThird (packet : StartupOriginalUnitNormPacket parameters length radius) : StartupSignedFirstFamily 1 1 1 := packet.val.knownThird
abbrev determinant (packet : StartupOriginalUnitNormPacket parameters length radius) : StartupSignedFirstFamily 1 1 1 := packet.val.determinant

theorem fieldSame (packet : StartupOriginalUnitNormPacket parameters length radius) :
    packet.field.field=originalSourceFieldLinear parameters packet.core := packet.property.1

theorem forceSame (packet : StartupOriginalUnitNormPacket parameters length radius) :
    packet.knownForce.field=originalSourceFieldLinear parameters packet.forceCore := packet.property.2.1

theorem thirdSame (packet : StartupOriginalUnitNormPacket parameters length radius) :
    packet.knownThird.field=originalSourceFieldLinear parameters packet.thirdCore := packet.property.2.2.1

theorem determinantSame (packet : StartupOriginalUnitNormPacket parameters length radius) :
    packet.determinant.field=originalSourceFieldLinear parameters packet.determinantCore := packet.property.2.2.2

variable {parameters : PhaseParameters} {length radius : ℝ}
    (radiusNonnegative : 0≤radius) (packet : StartupOriginalUnitNormPacket parameters length radius)

def principalCore (outer inner : Fin 2) : ACore parameters 3 :=
  (packet.coefficient.principal_core_exists radiusNonnegative packet.core outer inner).choose

theorem principalCore_same (outer inner : Fin 2) :
    originalSourceFieldLinear parameters (packet.principalCore radiusNonnegative outer inner)=
      startupGenuinePrincipalTensorKernel (unitDiskAdmissible parameters) packet.coefficient.data
        (packet.coefficient.coherent radiusNonnegative) (packet.coefficient.inverseCoherent radiusNonnegative) outer inner
        (originalSourceFieldLinear parameters packet.core) :=
  (packet.coefficient.principal_core_exists radiusNonnegative packet.core outer inner).choose_spec

def knownTensorCore (outer inner : Fin 2) : ACore parameters 3 :=
  (startupKnownTensor_core_exists parameters packet.forceCore packet.thirdCore outer inner).choose

theorem knownTensorCore_same (outer inner : Fin 2) :
    originalSourceFieldLinear parameters (packet.knownTensorCore outer inner)=
      (StartupSignedFirstFamily.knownTensor packet.knownForce packet.knownThird outer inner).field := by
  rw [StartupSignedFirstFamily.knownTensor_field,packet.forceSame,packet.thirdSame]
  exact (startupKnownTensor_core_exists parameters packet.forceCore packet.thirdCore outer inner).choose_spec

def tensorFamily (outer inner : Fin 2) : StartupSignedFamily 3 1 1 :=
  startupSignedFullTensor (unitDiskAdmissible parameters) packet.coefficient.data
    (packet.coefficient.coherent radiusNonnegative) (packet.coefficient.inverseCoherent radiusNonnegative) packet.field
    (StartupSignedFirstFamily.knownTensor packet.knownForce packet.knownThird) outer inner

theorem tensorFamily_same (outer inner : Fin 2) :
    (packet.tensorFamily radiusNonnegative outer inner).field=
      originalSourceFieldLinear parameters (packet.principalCore radiusNonnegative outer inner+packet.knownTensorCore outer inner) := by
  change ((StartupSignedAction.principalTensor (unitDiskAdmissible parameters) packet.coefficient.data
    (packet.coefficient.coherent radiusNonnegative) (packet.coefficient.inverseCoherent radiusNonnegative) outer inner).action packet.field).field+
      (StartupSignedFirstFamily.knownTensor packet.knownForce packet.knownThird outer inner).field=_
  rw [StartupSignedAction.sameField,StartupSignedAction.principalTensor_coarse,packet.fieldSame,map_add,
    packet.principalCore_same radiusNonnegative outer inner,packet.knownTensorCore_same]

def forceFamily : StartupSignedFamily 2 1 1 :=
  (StartupSignedAction.force (unitDiskAdmissible parameters) packet.coefficient.data
    (packet.coefficient.coherent radiusNonnegative) (packet.coefficient.inverseCoherent radiusNonnegative)).action packet.field

def scalarFluxFamily : StartupSignedFamily 1 1 1 :=
  (StartupSignedAction.scalarFlux (unitDiskAdmissible parameters) packet.coefficient.data
    (packet.coefficient.coherent radiusNonnegative) (packet.coefficient.inverseCoherent radiusNonnegative)).action packet.field

def axialCore (direction : Fin 2) : ACore parameters 3 :=
  (packet.coefficient.nativePreAxial_core_exists radiusNonnegative packet.core direction).choose

theorem axialCore_same (direction : Fin 2) :
    originalSourceFieldLinear parameters (packet.axialCore radiusNonnegative direction)=
      startupNativePreAxialFluxKernel
        (startupGenuineForceKernel (unitDiskAdmissible parameters) packet.coefficient.data
          (packet.coefficient.coherent radiusNonnegative) (packet.coefficient.inverseCoherent radiusNonnegative))
        (originalScalarFluxKernel (unitDiskAdmissible parameters) packet.coefficient.data
          (packet.coefficient.coherent radiusNonnegative) (packet.coefficient.inverseCoherent radiusNonnegative)) direction
        (originalSourceFieldLinear parameters packet.core) :=
  (packet.coefficient.nativePreAxial_core_exists radiusNonnegative packet.core direction).choose_spec

def knownFluxCore (scale : ℝ) (direction : Fin 2) : ACore parameters 3 :=
  startupKnownNativeFluxCore parameters scale packet.determinantCore packet.forceCore direction

def fluxFamily (scale : ℝ) (direction : Fin 2) : StartupSignedFamily 3 1 1 :=
  StartupSignedFamily.physicalNativeLowerFlux scale packet.determinant.toStartupSignedFamily
    (packet.field.value toroidalPartMap) (packet.scalarFluxFamily radiusNonnegative)
    ((packet.field.value planarPartMap).recoveredGradient
      (packet.knownForce.toStartupSignedFamily.sub (packet.forceFamily radiusNonnegative))) direction

theorem fluxFamily_same (scale : ℝ) (direction : Fin 2) :
    (packet.fluxFamily radiusNonnegative scale direction).field=(scale : ℂ) •
      originalSourceFieldLinear parameters (originalSignedAxialCore parameters (packet.axialCore radiusNonnegative direction) 1 1 1)+
        originalSourceFieldLinear parameters (packet.knownFluxCore scale direction) := by
  have forceSame : (packet.forceFamily radiusNonnegative).field=
      startupGenuineForceKernel (unitDiskAdmissible parameters) packet.coefficient.data
        (packet.coefficient.coherent radiusNonnegative) (packet.coefficient.inverseCoherent radiusNonnegative) packet.field.field := by
    rw [forceFamily,StartupSignedAction.sameField,StartupSignedAction.force_coarse]
  have scalarSame : (packet.scalarFluxFamily radiusNonnegative).field=
      originalScalarFluxKernel (unitDiskAdmissible parameters) packet.coefficient.data
        (packet.coefficient.coherent radiusNonnegative) (packet.coefficient.inverseCoherent radiusNonnegative) packet.field.field := by
    rw [scalarFluxFamily,StartupSignedAction.sameField,StartupSignedAction.scalarFlux_coarse]
  rw [fluxFamily,StartupSignedFamily.physicalNativeLowerFlux_sourceSplit]
  rw [startupNativePreAxial_sameOriginal parameters packet.field (packet.forceFamily radiusNonnegative)
    (packet.scalarFluxFamily radiusNonnegative) _ _ forceSame scalarSame (packet.axialCore radiusNonnegative direction)
    direction (by rw [packet.fieldSame]; exact packet.axialCore_same radiusNonnegative direction) 1,
    startupKnownNativeFluxCore_same parameters scale packet.determinant.toStartupSignedFamily packet.knownForce.toStartupSignedFamily
      packet.determinantCore packet.forceCore packet.determinantSame packet.forceSame direction]
  rfl

end StartupOriginalUnitNormPacket
end Grad.CartesianStartup
