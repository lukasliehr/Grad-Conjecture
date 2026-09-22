import AJD12OriginalOmegaCoordinateCovariance
import AJB6GenuineLowTraceDataTranslations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentGreen Grad.AnnularFluxTrace Grad.AnnularReconstruction
open Grad.AnnularHighInverseOrbit Grad.AnnularTiltedReference Grad.AnnularLowOrbit Grad.AnnularCurrentLow Grad.AnnularLowEnergy

variable (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L)

def HighCrossBulkCovariant (mapping : CrossHighSpace lower L positive lengthPositive →L[ℂ] AnnularBulk lower) : Prop :=
  ∀ (tau : OrbitParameter) (field : CrossHighSpace lower L positive lengthPositive) (mode : HighAnnularMode),
    mapping (highTranslationEquivalence lower L positive lengthPositive tau field) mode =
      orbitCharacter tau mode.val • mapping field mode

def HighCrossPacketCovariant {dimension : ℕ}
    (mapping : CrossHighSpace lower L positive lengthPositive →L[ℂ] DivisionRow dimension lower) : Prop :=
  ∀ (tau : OrbitParameter) (field : CrossHighSpace lower L positive lengthPositive),
    mapping (highTranslationEquivalence lower L positive lengthPositive tau field) =
      orbitLpAction (RadialL2 dimension lower) tau (mapping field)

theorem crossHighX_covariant : HighCrossBulkCovariant lower L positive lengthPositive
    (crossHighX lower L positive lengthPositive) := by
  intro tau field mode
  exact fluxTranslation_apply lower L positive lengthPositive tau field.ofLp.2 0 mode

theorem energyCovariant_highCross {mapping : annularEnergySpace lower L positive →L[ℂ] AnnularBulk lower}
    (covariant : EnergyBulkCovariant lower L positive mapping) :
    HighCrossBulkCovariant lower L positive lengthPositive
      (mapping.comp (crossHighW lower L positive lengthPositive)) := by
  intro tau field mode
  exact covariant tau field.ofLp.1 mode

theorem HighCrossBulkCovariant.slot {mapping : CrossHighSpace lower L positive lengthPositive →L[ℂ] AnnularBulk lower}
    (covariant : HighCrossBulkCovariant lower L positive lengthPositive mapping) {dimension : ℕ} (slot : Fin dimension) :
    HighCrossPacketCovariant lower L positive lengthPositive ((highBulkSlot lower slot).comp mapping) := by
  intro tau field
  apply lp.ext
  funext mode
  change radialMatrixUnit lower slot 0 (highBulkIntoFull lower
      (mapping (highTranslationEquivalence lower L positive lengthPositive tau field)) mode) =
    orbitCharacter tau mode • radialMatrixUnit lower slot 0 (highBulkIntoFull lower (mapping field) mode)
  by_cases high : 3 ≤ |mode.1|
  · have translated := covariant tau field ⟨mode, high⟩
    rw [highBulkIntoFull_high lower _ ⟨mode, high⟩, highBulkIntoFull_high lower _ ⟨mode, high⟩,
      translated, map_smul]
  · rw [highBulkIntoFull_low lower _ mode high, highBulkIntoFull_low lower _ mode high, map_zero, smul_zero]

theorem HighCrossPacketCovariant.add {dimension : ℕ}
    {first second : CrossHighSpace lower L positive lengthPositive →L[ℂ] DivisionRow dimension lower}
    (hf : HighCrossPacketCovariant lower L positive lengthPositive first)
    (hs : HighCrossPacketCovariant lower L positive lengthPositive second) :
    HighCrossPacketCovariant lower L positive lengthPositive (first + second) := by
  intro tau field
  change first (highTranslationEquivalence lower L positive lengthPositive tau field) +
    second (highTranslationEquivalence lower L positive lengthPositive tau field) = _
  rw [hf tau field, hs tau field]
  exact (map_add (orbitLpAction (RadialL2 dimension lower) tau) _ _).symm

/-- Actual free flux and the three physical energy inputs commute with the original high graph unitary. -/
theorem highCrossSevenInput_covariant :
    HighCrossPacketCovariant lower L positive lengthPositive (highCrossSevenInput lower L positive lengthPositive) := by
  have angular := energyCovariant_highCross lower L positive lengthPositive
    ((highEnergyAngularRadius_covariant lower L positive).decode lower L positive)
  have cell := energyCovariant_highCross lower L positive lengthPositive
    (((highEnergyCell_covariant lower L positive).smul lower L positive (L : ℂ)).decode lower L positive)
  have radius := energyCovariant_highCross lower L positive lengthPositive
    ((highEnergyRadius_covariant lower L positive).decode lower L positive)
  exact ((((crossHighX_covariant lower L positive lengthPositive).slot lower L positive lengthPositive (0 : Fin 7)).add
    lower L positive lengthPositive (angular.slot lower L positive lengthPositive (1 : Fin 7))).add
    lower L positive lengthPositive (cell.slot lower L positive lengthPositive (2 : Fin 7))).add
    lower L positive lengthPositive (radius.slot lower L positive lengthPositive (3 : Fin 7))

end Grad.AnnularCrossOrbit
