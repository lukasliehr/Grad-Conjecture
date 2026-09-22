import AKDW27OriginalPacketSourcePayment
import AKDW16ActualOriginalKnownSourceCores

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
namespace Grad.OriginalMainConsumer
open Grad.ClosedJets Grad.CartesianState Grad.CartesianStartup Grad.PDEBootstrap Grad.GenericCarriers
open Grad.OriginalCoreRealization Grad.ActualOriginalSourceMoments Grad.ActualOriginalSourceFirst
open Grad.QuotientProjection Grad.NonlinearProduct Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation

/-- The SAME original signed family, with its genuine first graphs retained. -/
def originalCoreSignedFirst {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) : StartupSignedFirstFamily dimension 1 1 where
  toStartupSignedFamily := startupOriginalSignedFamily parameters core 1 1
  first power := originalSourceSpatialGraph parameters (originalSignedAxialCore parameters core 1 1 power) 1
  firstBase power := originalSourceSpatialGraph_base parameters (originalSignedAxialCore parameters core 1 1 power) 1

theorem originalCoreSignedFirst_same {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) :
    (originalCoreSignedFirst parameters core).field=originalSourceFieldLinear parameters core := rfl

theorem originalCoreSignedFirst_allSpatial {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (grade : ℕ) :
    (originalCoreSignedFirst parameters core).toStartupSignedFamily.HasSpatialGrade grade :=
  startupOriginalSignedFamily_allSpatial parameters core one_ne_zero one_ne_zero grade

/-- Actual original source rows on unit coordinates, retaining the physical
length in both scalar rows and later in the single axial flux scale. -/
def originalSourceNormPacket {parameters : PhaseParameters} {length radius : ℝ}
    (coefficient : OriginalUnitRankState parameters length radius)
    (core : ACore parameters 3) (source : SmoothQuotient parameters) :
    StartupOriginalUnitNormPacket parameters length radius :=
  ⟨(coefficient,core,startupOriginalSignedFamily parameters core 1 1,
    startupOriginalKnownForceCore parameters source,
    startupOriginalKnownScalarCore parameters length source 3,
    startupOriginalKnownScalarCore parameters length source 2,
    originalCoreSignedFirst parameters (startupOriginalKnownForceCore parameters source),
    originalCoreSignedFirst parameters (startupOriginalKnownScalarCore parameters length source 3),
    originalCoreSignedFirst parameters (startupOriginalKnownScalarCore parameters length source 2)),
    rfl,rfl,rfl,rfl⟩

variable {parameters : PhaseParameters} {length radius : ℝ}
  (coefficient : OriginalUnitRankState parameters length radius)
  (core : ACore parameters 3) (source : SmoothQuotient parameters)

theorem originalSourceNormPacket_coefficient :
    (originalSourceNormPacket coefficient core source).coefficient=coefficient := rfl

theorem originalSourceNormPacket_core :
    (originalSourceNormPacket coefficient core source).core=core := rfl

theorem originalSourceNormPacket_field :
    (originalSourceNormPacket coefficient core source).field=startupOriginalSignedFamily parameters core 1 1 := rfl

theorem originalSourceNormPacket_force :
    (originalSourceNormPacket coefficient core source).forceCore=startupOriginalKnownForceCore parameters source := rfl

theorem originalSourceNormPacket_third :
    (originalSourceNormPacket coefficient core source).thirdCore=startupOriginalKnownScalarCore parameters length source 3 := rfl

theorem originalSourceNormPacket_determinant :
    (originalSourceNormPacket coefficient core source).determinantCore=startupOriginalKnownScalarCore parameters length source 2 := rfl

theorem originalSourceNormPacket_field_allSpatial (grade : ℕ) :
    (originalSourceNormPacket coefficient core source).field.HasSpatialGrade grade :=
  startupOriginalSignedFamily_allSpatial parameters core one_ne_zero one_ne_zero grade

theorem originalSourceNormPacket_force_allSpatial (grade : ℕ) :
    (originalSourceNormPacket coefficient core source).knownForce.toStartupSignedFamily.HasSpatialGrade grade :=
  originalCoreSignedFirst_allSpatial parameters _ grade

theorem originalSourceNormPacket_third_allSpatial (grade : ℕ) :
    (originalSourceNormPacket coefficient core source).knownThird.toStartupSignedFamily.HasSpatialGrade grade :=
  originalCoreSignedFirst_allSpatial parameters _ grade

theorem originalSourceNormPacket_determinant_allSpatial (grade : ℕ) :
    (originalSourceNormPacket coefficient core source).determinant.toStartupSignedFamily.HasSpatialGrade grade :=
  originalCoreSignedFirst_allSpatial parameters _ grade

/-- The known force is the exact corrected original radial source projection. -/
theorem originalSourceNormPacket_force_field :
    (originalSourceNormPacket coefficient core source).knownForce.field=
      startupGenuineQradKernel (originalSourceFieldLinear parameters (cartesianSourceVector source)) :=
  startupOriginalKnownForceCore_same parameters source

theorem originalSourceNormPacket_third_field :
    (originalSourceNormPacket coefficient core source).knownThird.field=
      (length : ℂ)⁻¹ • originalSourceFieldLinear parameters (source 3) :=
  startupOriginalKnownScalarCore_same parameters length source 3

theorem originalSourceNormPacket_determinant_field :
    (originalSourceNormPacket coefficient core source).determinant.field=
      (length : ℂ)⁻¹ • originalSourceFieldLinear parameters (source 2) :=
  startupOriginalKnownScalarCore_same parameters length source 2

end Grad.OriginalMainConsumer
