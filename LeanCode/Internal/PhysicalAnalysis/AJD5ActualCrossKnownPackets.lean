import AJD4OriginalCrossDatumTranslations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit
open Grad.ActualBoundaryPrimitives Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource

variable (parameters : PhaseParameters) (lower : ℝ)

def crossBulkCoordinate (row : Fin 3) : CrossHighData parameters lower →L[ℂ] AnnularBulk lower :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => AnnularBulk lower) row).comp
    ((ContinuousLinearMap.fst ℂ (CrossHighBulk lower) (HighBoundaryPrimitive parameters 0 0)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ (CrossHighBulk lower) (HighBoundaryPrimitive parameters 0 0)).toContinuousLinearMap)

def crossBoundaryCoordinate : CrossHighData parameters lower →L[ℂ] HighBoundaryPrimitive parameters 0 0 :=
  (ContinuousLinearMap.snd ℂ (CrossHighBulk lower) (HighBoundaryPrimitive parameters 0 0)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ (CrossHighBulk lower) (HighBoundaryPrimitive parameters 0 0)).toContinuousLinearMap

/-- With F0=RF0=F2=0, the actual known eight-packet has only the f slot. -/
def crossKnownEight : CrossHighData parameters lower →L[ℂ] DivisionRow 8 lower :=
  (highBulkSlot lower 7).comp (crossBulkCoordinate parameters lower 0)

/-- Exact direct qc and rqv output; the graph source g is zero on this datum. -/
def crossKnownDirect : CrossHighData parameters lower →L[ℂ] DivisionRow 3 lower :=
  (highBulkSlot lower 1).comp (crossBulkCoordinate parameters lower 1) +
  (highBulkSlot lower 2).comp (crossBulkCoordinate parameters lower 2)

theorem crossKnownEight_literal (datum : CrossHighData parameters lower) :
    highKnownEightPacket lower (crossKnownWeighted parameters lower datum) = crossKnownEight parameters lower datum := by
  change (bulkMatrixUnit lower (4 : Fin 8) (0 : Fin 1)) 0 +
    (bulkMatrixUnit lower (5 : Fin 8) (0 : Fin 1)) 0 +
    (bulkMatrixUnit lower (6 : Fin 8) (0 : Fin 1)) 0 +
    (bulkMatrixUnit lower (7 : Fin 8) (0 : Fin 1)) (highBulkIntoFull lower (datum.ofLp.1 0)) = _
  simp only [map_zero, zero_add]
  rfl

theorem crossKnownDirect_literal (positive : 0 < lower) (datum : CrossHighData parameters lower) :
    directKnownThreePacket lower positive (crossKnownAuxiliary parameters lower datum) = crossKnownDirect parameters lower datum := by
  change (bulkMatrixUnit lower (1 : Fin 3) (0 : Fin 1)) (highBulkIntoFull lower (datum.ofLp.1 1)) +
    (bulkMatrixUnit lower (2 : Fin 3) (0 : Fin 1))
      (highBulkIntoFull lower (datum.ofLp.1 2) - radialRadiusRow lower positive 0) = _
  rw [map_zero, sub_zero]
  rfl

def CrossPacketCovariant {dimension : ℕ} (mapping : CrossHighData parameters lower →L[ℂ] DivisionRow dimension lower) : Prop :=
  ∀ (tau : OrbitParameter) (datum : CrossHighData parameters lower),
    mapping (crossDataTranslation parameters lower tau datum) = orbitLpAction (RadialL2 dimension lower) tau (mapping datum)

theorem crossSlot_covariant {dimension : ℕ} (slot : Fin dimension) (row : Fin 3) :
    CrossPacketCovariant parameters lower ((highBulkSlot lower slot).comp (crossBulkCoordinate parameters lower row)) := by
  intro tau datum
  apply lp.ext
  funext mode
  change radialMatrixUnit lower slot 0 (highBulkIntoFull lower
    ((crossDataTranslation parameters lower tau datum).ofLp.1 row) mode) =
    orbitCharacter tau mode • radialMatrixUnit lower slot 0 (highBulkIntoFull lower (datum.ofLp.1 row) mode)
  by_cases high : 3 ≤ |mode.1|
  · rw [highBulkIntoFull_high lower _ ⟨mode, high⟩, highBulkIntoFull_high lower _ ⟨mode, high⟩,
      crossDataTranslation_bulk, map_smul]
  · rw [highBulkIntoFull_low lower _ mode high, highBulkIntoFull_low lower _ mode high, map_zero, smul_zero]

theorem CrossPacketCovariant.add {dimension : ℕ}
    {first second : CrossHighData parameters lower →L[ℂ] DivisionRow dimension lower}
    (hf : CrossPacketCovariant parameters lower first) (hg : CrossPacketCovariant parameters lower second) :
    CrossPacketCovariant parameters lower (first + second) := by
  intro tau datum
  change first (crossDataTranslation parameters lower tau datum) + second (crossDataTranslation parameters lower tau datum) = _
  rw [hf tau datum, hg tau datum]
  exact (map_add (orbitLpAction (RadialL2 dimension lower) tau) _ _).symm

theorem crossKnownEight_covariant : CrossPacketCovariant parameters lower (crossKnownEight parameters lower) :=
  crossSlot_covariant parameters lower 7 0

theorem crossKnownDirect_covariant : CrossPacketCovariant parameters lower (crossKnownDirect parameters lower) :=
  (crossSlot_covariant parameters lower (1 : Fin 3) 1).add parameters lower (crossSlot_covariant parameters lower (2 : Fin 3) 2)

end Grad.AnnularCrossOrbit
