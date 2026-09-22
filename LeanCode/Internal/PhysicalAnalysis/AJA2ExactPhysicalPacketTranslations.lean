import AJA1ActualPhysicalCoordinateTranslations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.AnnularHighInverseOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularGrades Grad.AnnularFluxTrace Grad.AnnularTiltedReference Grad.AnnularCurrentEnergy
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit

variable (lower length : ℝ) (positive : 0 < lower)

def EnergyPacketCovariant {dimension : ℕ}
    (mapping : annularEnergySpace lower length positive →L[ℂ] DivisionRow dimension lower) : Prop :=
  ∀ (tau : OrbitParameter) (field : annularEnergySpace lower length positive),
    mapping (energyTranslation lower length positive tau field) =
      orbitLpAction (RadialL2 dimension lower) tau (mapping field)

theorem EnergyBulkCovariant.slot {mapping : annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower}
    (covariant : EnergyBulkCovariant lower length positive mapping) {dimension : ℕ} (slot : Fin dimension) :
    EnergyPacketCovariant lower length positive ((highBulkSlot lower slot).comp mapping) := by
  intro tau field
  apply lp.ext
  funext mode
  change radialMatrixUnit lower slot 0 (highBulkIntoFull lower
      (mapping (energyTranslation lower length positive tau field)) mode) =
    orbitCharacter tau mode • radialMatrixUnit lower slot 0 (highBulkIntoFull lower (mapping field) mode)
  by_cases high : 3 ≤ |mode.1|
  · have translated := covariant tau field ⟨mode, high⟩
    rw [highBulkIntoFull_high lower _ ⟨mode, high⟩, highBulkIntoFull_high lower _ ⟨mode, high⟩,
      translated, map_smul]
  · rw [highBulkIntoFull_low lower _ mode high, highBulkIntoFull_low lower _ mode high, map_zero, smul_zero]

theorem EnergyPacketCovariant.add {dimension : ℕ}
    {first second : annularEnergySpace lower length positive →L[ℂ] DivisionRow dimension lower}
    (hfirst : EnergyPacketCovariant lower length positive first) (hsecond : EnergyPacketCovariant lower length positive second) :
    EnergyPacketCovariant lower length positive (first + second) := by
  intro tau field
  change first (energyTranslation lower length positive tau field) +
    second (energyTranslation lower length positive tau field) = _
  rw [hfirst tau field, hsecond tau field]
  exact (map_add (orbitLpAction (RadialL2 dimension lower) tau) _ _).symm

/-- Exact covariance of the literal normalized eight input slots. -/
theorem highEightEnergyPacket_translation (parameters : PhaseParameters) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) :
    EnergyPacketCovariant lower length positive
      (highEightEnergyPacket parameters lower length positive lengthPositive widthHalf widthLength) :=
  ((((highPhysicalDerivative_covariant lower length positive parameters lengthPositive widthHalf widthLength).slot
    lower length positive 0).add lower length positive
      (((highEnergyAngularRadius_covariant lower length positive).decode lower length positive).slot lower length positive 1)).add
      lower length positive
        ((((highEnergyCell_covariant lower length positive).smul lower length positive (length : ℂ)).decode lower length positive).slot
          lower length positive 2)).add lower length positive
            (((highEnergyRadius_covariant lower length positive).decode lower length positive).slot lower length positive 3)

/-- Exact covariance of the original three variational test factors. -/
theorem highEnergyTestPacket_translation (parameters : PhaseParameters) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) :
    EnergyPacketCovariant lower length positive
      (highEnergyTestPacket parameters lower length positive lengthPositive widthHalf widthLength) :=
  (((highPhysicalTestDerivative_covariant lower length positive parameters lengthPositive widthHalf widthLength).slot
    lower length positive 0).add lower length positive
      (((highEnergyCell_covariant lower length positive).decode lower length positive).slot lower length positive 1)).add
      lower length positive
        (((highEnergyAngularRadius_covariant lower length positive).decode lower length positive).slot lower length positive 2)

end Grad.AnnularHighInverseOrbit
