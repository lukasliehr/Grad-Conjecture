import AJE13ActualKnownDataCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularReconstruction
open Grad.AnnularCurrentEnergy Grad.AnnularHighInverseOrbit Grad.AnnularCrossOrbit Grad.AnnularKernelL2

theorem sourceBulkMatrixUnit_translation {src tgt : ℕ} (lower : ℝ) (row : Fin tgt) (column : Fin src)
    (tau : OrbitParameter) (field : DivisionRow src lower) :
    bulkMatrixUnit lower row column (orbitLpAction (RadialL2 src lower) tau field) =
      orbitLpAction (RadialL2 tgt lower) tau (bulkMatrixUnit lower row column field) := by
  apply lp.ext
  funext mode
  change radialMatrixUnit lower row column (orbitCharacter tau mode • field mode) =
    orbitCharacter tau mode • radialMatrixUnit lower row column (field mode)
  exact map_smul _ _ _

theorem knownEightPacket_translation (lower : ℝ) (tau : OrbitParameter) (known : HighKnownSourceBulk lower) :
    highKnownEightPacket lower (WithLp.toLp 2 (fun slot => orbitLpAction (RadialL2 1 lower) tau (known slot))) =
      orbitLpAction (RadialL2 8 lower) tau (highKnownEightPacket lower known) := by
  change bulkMatrixUnit lower (4 : Fin 8) (0 : Fin 1) (orbitLpAction (RadialL2 1 lower) tau (known 0)) +
      bulkMatrixUnit lower (5 : Fin 8) (0 : Fin 1) (orbitLpAction (RadialL2 1 lower) tau (known 1)) +
      bulkMatrixUnit lower (6 : Fin 8) (0 : Fin 1) (orbitLpAction (RadialL2 1 lower) tau (known 2)) +
      bulkMatrixUnit lower (7 : Fin 8) (0 : Fin 1) (orbitLpAction (RadialL2 1 lower) tau (known 3)) = _
  rw [sourceBulkMatrixUnit_translation,sourceBulkMatrixUnit_translation,
    sourceBulkMatrixUnit_translation,sourceBulkMatrixUnit_translation]
  change _ = orbitLpAction (RadialL2 8 lower) tau
    (bulkMatrixUnit lower (4 : Fin 8) (0 : Fin 1) (known 0) +
      bulkMatrixUnit lower (5 : Fin 8) (0 : Fin 1) (known 1) +
      bulkMatrixUnit lower (6 : Fin 8) (0 : Fin 1) (known 2) +
      bulkMatrixUnit lower (7 : Fin 8) (0 : Fin 1) (known 3))
  simp only [map_add]

theorem radialRadiusRow_translation (lower : ℝ) (positive : 0 < lower) (tau : OrbitParameter)
    (field : DivisionRow 1 lower) :
    radialRadiusRow lower positive (orbitLpAction (RadialL2 1 lower) tau field) =
      orbitLpAction (RadialL2 1 lower) tau (radialRadiusRow lower positive field) := by
  apply lp.ext
  funext mode
  exact map_smul (scalarRadialMap lower ⟨fun radius => radius, continuous_id⟩ 1
    (fun radius inside => by
      change |radius| ≤ 1
      rw [abs_of_nonneg (positive.le.trans inside.1)]
      exact inside.2)) (orbitCharacter tau mode) (field mode)

theorem knownDirectPacket_translation (lower : ℝ) (positive : 0 < lower) (tau : OrbitParameter)
    (auxiliary : HighAuxiliarySourceBulk lower) :
    directKnownThreePacket lower positive (WithLp.toLp 2 (fun slot => orbitLpAction (RadialL2 1 lower) tau (auxiliary slot))) =
      orbitLpAction (RadialL2 3 lower) tau (directKnownThreePacket lower positive auxiliary) := by
  change bulkMatrixUnit lower (1 : Fin 3) (0 : Fin 1) (orbitLpAction (RadialL2 1 lower) tau (auxiliary 1)) +
    bulkMatrixUnit lower (2 : Fin 3) (0 : Fin 1)
      (orbitLpAction (RadialL2 1 lower) tau (auxiliary 2) -
        radialRadiusRow lower positive (orbitLpAction (RadialL2 1 lower) tau (auxiliary 0))) = _
  rw [radialRadiusRow_translation,← map_sub,sourceBulkMatrixUnit_translation,sourceBulkMatrixUnit_translation,← map_add]
  rfl

variable (parameters : PhaseParameters) (lower : ℝ)

theorem knownAmbientEight_translation (tau : OrbitParameter) (data : ActualHighKnownAmbient parameters lower 0 0) :
    knownAmbientEight parameters lower 0 0 (highKnownAmbientTranslation parameters lower 0 0 tau data) =
      orbitLpAction (RadialL2 8 lower) tau (knownAmbientEight parameters lower 0 0 data) :=
  knownEightPacket_translation lower tau data.ofLp.1.ofLp.1

theorem knownAmbientDirect_translation (positive : 0 < lower) (tau : OrbitParameter)
    (data : ActualHighKnownAmbient parameters lower 0 0) :
    knownAmbientDirect parameters lower 0 0 positive (highKnownAmbientTranslation parameters lower 0 0 tau data) =
      orbitLpAction (RadialL2 3 lower) tau (knownAmbientDirect parameters lower 0 0 positive data) :=
  knownDirectPacket_translation lower positive tau data.ofLp.1.ofLp.2

end Grad.AnnularStrongOrbit
