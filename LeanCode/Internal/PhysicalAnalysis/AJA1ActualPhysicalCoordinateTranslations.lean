import AIX13ActualEliminatedPhysicalOrbit
import AIZ1ActualEnergyTranslations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.AnnularHighInverseOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularGrades Grad.AnnularFluxTrace Grad.AnnularTiltedReference Grad.AnnularCurrentEnergy
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit

variable (lower length : ℝ) (positive : 0 < lower)

theorem bEnergyDecode_translation (tau : OrbitParameter) (field : annularEnergySpace lower length positive) :
    bEnergyDecode lower length positive (energyTranslation lower length positive tau field) =
      energyTranslation lower length positive tau (bEnergyDecode lower length positive field) := by
  apply Subtype.ext
  apply lp.ext
  funext mode
  simp only [bEnergyDecode, annularEnergyDiagonal_apply, energyTranslation_apply]
  exact smul_comm _ _ _

/-- Covariance of a literal scalar physical coordinate on the stored energy graph. -/
def EnergyBulkCovariant (mapping : annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower) : Prop :=
  ∀ (tau : OrbitParameter) (field : annularEnergySpace lower length positive) (mode : HighAnnularMode),
    mapping (energyTranslation lower length positive tau field) mode =
      orbitCharacter tau mode.val • mapping field mode

theorem energyDerivative_covariant : EnergyBulkCovariant lower length positive
    (annularEnergyDerivative lower length positive) := by
  intro tau field mode
  change annularModeDerivative lower ((energyTranslation lower length positive tau field).val mode) = _
  rw [energyTranslation_apply, map_smul]
  rfl

theorem energyMass_covariant : EnergyBulkCovariant lower length positive
    (annularEnergyMass lower length positive) := by
  intro tau field mode
  change annularModeMass lower ((energyTranslation lower length positive tau field).val mode) = _
  rw [energyTranslation_apply, map_smul]
  rfl

theorem EnergyBulkCovariant.add {first second : annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower}
    (hfirst : EnergyBulkCovariant lower length positive first) (hsecond : EnergyBulkCovariant lower length positive second) :
    EnergyBulkCovariant lower length positive (first + second) := by
  intro tau field mode
  change first (energyTranslation lower length positive tau field) mode +
    second (energyTranslation lower length positive tau field) mode = _
  rw [hfirst tau field mode, hsecond tau field mode]
  exact (smul_add _ _ _).symm

theorem EnergyBulkCovariant.sub {first second : annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower}
    (hfirst : EnergyBulkCovariant lower length positive first) (hsecond : EnergyBulkCovariant lower length positive second) :
    EnergyBulkCovariant lower length positive (first - second) := by
  intro tau field mode
  change first (energyTranslation lower length positive tau field) mode -
    second (energyTranslation lower length positive tau field) mode = _
  rw [hfirst tau field mode, hsecond tau field mode]
  exact (smul_sub _ _ _).symm

theorem EnergyBulkCovariant.smul {mapping : annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower}
    (covariant : EnergyBulkCovariant lower length positive mapping) (scalar : ℂ) :
    EnergyBulkCovariant lower length positive (scalar • mapping) := by
  intro tau field mode
  change scalar • mapping (energyTranslation lower length positive tau field) mode = _
  rw [covariant tau field mode]
  exact smul_comm _ _ _

theorem EnergyBulkCovariant.modeMap {mapping : annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower}
    (covariant : EnergyBulkCovariant lower length positive mapping)
    (family : HighAnnularMode → RadialL2 1 lower →L[ℂ] RadialL2 1 lower)
    (constant : ℝ) (nonnegative : 0 ≤ constant) (bound : ∀ mode value, ‖family mode value‖ ≤ constant * ‖value‖) :
    EnergyBulkCovariant lower length positive ((complexLpTwoMap family constant nonnegative bound).comp mapping) := by
  intro tau field mode
  change family mode (mapping (energyTranslation lower length positive tau field) mode) = _
  rw [covariant tau field mode, map_smul]
  rfl

theorem EnergyBulkCovariant.decode {mapping : annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower}
    (covariant : EnergyBulkCovariant lower length positive mapping) :
    EnergyBulkCovariant lower length positive (mapping.comp (bEnergyDecode lower length positive)) := by
  intro tau field mode
  change mapping (bEnergyDecode lower length positive (energyTranslation lower length positive tau field)) mode = _
  rw [bEnergyDecode_translation]
  exact covariant tau (bEnergyDecode lower length positive field) mode

/-- All three original non-radial physical coordinates retain their literal symbols. -/
theorem highEnergyRadius_covariant : EnergyBulkCovariant lower length positive (highEnergyRadius lower length positive) :=
  ((energyMass_covariant lower length positive).modeMap lower length positive _ _ _ _).smul lower length positive (1 / 2)

theorem highEnergyAngularRadius_covariant : EnergyBulkCovariant lower length positive (highEnergyAngularRadius lower length positive) :=
  ((energyMass_covariant lower length positive).modeMap lower length positive _ _ _ _).smul lower length positive Complex.I

theorem highEnergyCell_covariant : EnergyBulkCovariant lower length positive (highEnergyCell lower length positive) :=
  ((energyMass_covariant lower length positive).modeMap lower length positive _ _ _ _).modeMap lower length positive _ _ _ _

theorem highTiltPhase_covariant (parameters : PhaseParameters) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) :
    EnergyBulkCovariant lower length positive
      (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength) :=
  (energyMass_covariant lower length positive).modeMap lower length positive _ _ _ _

theorem highPhysicalDerivative_covariant (parameters : PhaseParameters) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) :
    EnergyBulkCovariant lower length positive
      (highPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength) :=
  ((energyDerivative_covariant lower length positive).sub lower length positive
    (highTiltPhase_covariant lower length positive parameters lengthPositive widthHalf widthLength)).decode lower length positive

theorem highPhysicalTestDerivative_covariant (parameters : PhaseParameters) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) :
    EnergyBulkCovariant lower length positive
      (highPhysicalTestDerivative parameters lower length positive lengthPositive widthHalf widthLength) :=
  ((energyDerivative_covariant lower length positive).add lower length positive
    (highTiltPhase_covariant lower length positive parameters lengthPositive widthHalf widthLength)).decode lower length positive

end Grad.AnnularHighInverseOrbit
