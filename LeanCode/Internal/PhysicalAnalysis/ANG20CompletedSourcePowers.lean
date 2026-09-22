import ANG19SourceRotationBounds

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open scoped BigOperators
namespace Grad.CircularHighWeak
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger

def sourcePowerFinite (order : ℕ) : (ℤ →₀ ClosedJet 1) →ₗ[ℂ] DiskL2 1 :=
  closedL2Core.comp ((rotationJetPower order).comp (Finsupp.lapply 0))

theorem sourcePowerFinite_bound (order : ℕ) (core : ℤ →₀ ClosedJet 1) :
    ‖sourcePowerFinite order core‖ ≤ unitRotationPowerConstant order *
      ‖apFiniteInto (grade := order) 1 0 0 1 core‖ := by
  have cell := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (apFiniteEmbed (grade := order) 1 0 0 1 core) 0
  rw [apFiniteEmbed_apply] at cell
  exact (rotationJetPower_L2_bound order (core 0)).trans
    (mul_le_mul_of_nonneg_left cell (unitRotationPowerConstant_nonnegative order))

private theorem sourceRotationPower_exists (order : ℕ) :
    ∃ mapping : apGrade 1 0 0 1 1 order →L[ℂ] DiskL2 1,
      (∀ core, mapping (apFiniteInto 1 0 0 1 core) = sourcePowerFinite order core) ∧
      (∀ field, ‖mapping field‖ ≤ unitRotationPowerConstant order * ‖field‖) :=
  apDense_extension (apFiniteInto (grade := order) 1 0 0 1)
    (apFiniteInto_injective 1 0 0 1) (apFiniteInto_denseRange 1 0 0 1)
    (sourcePowerFinite order) (unitRotationPowerConstant order)
    (unitRotationPowerConstant_nonnegative order) (sourcePowerFinite_bound order)

/-- Completed genuine R^s from the exact ordinary Cartesian grade s.
The auxiliary AP representation permits all cells; only cell zero is evaluated. -/
def sourceRotationPower (order : ℕ) : apGrade 1 0 0 1 1 order →L[ℂ] DiskL2 1 :=
  (sourceRotationPower_exists order).choose

theorem sourceRotationPower_core (order : ℕ) (core : ℤ →₀ ClosedJet 1) :
    sourceRotationPower order (apFiniteInto 1 0 0 1 core) = closedL2Core (rotationJetPower order (core 0)) :=
  (sourceRotationPower_exists order).choose_spec.1 core

theorem sourceRotationPower_bound (order : ℕ) (field : apGrade 1 0 0 1 1 order) :
    ‖sourceRotationPower order field‖ ≤ unitRotationPowerConstant order * ‖field‖ :=
  (sourceRotationPower_exists order).choose_spec.2 field

def sourceBulk (grade : ℕ) : apGrade 1 0 0 1 1 grade →L[ℂ] DiskL2 1 := apL2Trace 1 0 0 1 0

theorem sourceBulk_core (grade : ℕ) (core : ℤ →₀ ClosedJet 1) :
    sourceBulk grade (apFiniteInto 1 0 0 1 core) = closedL2Core (core 0) :=
  apL2Trace_core 1 0 0 1 0 core

theorem angular_rotationJetPower (order : ℕ) (mode : ℤ) (field : ClosedJet 1) :
    angularClosedJet mode (rotationJetPower order field) =
      (Complex.I * (mode : ℂ)) ^ order • angularClosedJet mode field := by
  induction order generalizing field with
  | zero => exact (one_smul ℂ _).symm
  | succ order previous =>
    have equality := (previous (rotationJet field)).trans
      (congrArg (fun value : ClosedJet 1 => (Complex.I * (mode : ℂ)) ^ order • value) (angular_rotationJet mode field))
    exact equality.trans ((smul_smul _ _ _).trans
      (congrArg (fun scalar : ℂ => scalar • angularClosedJet mode field) (pow_succ _ order).symm))

theorem sourceRotationPower_coefficient (order : ℕ) (mode : ℤ) (field : apGrade 1 0 0 1 1 order) :
    diskMode mode (sourceRotationPower order field) =
      (Complex.I * (mode : ℂ)) ^ order • diskMode mode (sourceBulk order field) := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := 1) (grade := order) 1 0 0 1)
    (isClosed_eq ((diskMode mode).continuous.comp (sourceRotationPower order).continuous)
      ((show Continuous (fun _ : apGrade 1 0 0 1 1 order => (Complex.I * (mode : ℂ)) ^ order) from continuous_const).smul
        ((diskMode mode).continuous.comp (sourceBulk order).continuous))) _ field
  intro core
  have left := (congrArg (diskMode mode) (sourceRotationPower_core order core)).trans
    ((diskMode_core mode (rotationJetPower order (core 0))).trans
      ((congrArg closedL2Core (angular_rotationJetPower order mode (core 0))).trans
        (closedL2Core.map_smul ((Complex.I * (mode : ℂ)) ^ order) (angularClosedJet mode (core 0)))))
  refine left.trans ?_
  exact congrArg (fun value : DiskL2 1 => (Complex.I * (mode : ℂ)) ^ order • value)
    ((diskMode_core mode (core 0)).symm.trans (congrArg (diskMode mode) (sourceBulk_core order core).symm))

end Grad.CircularHighWeak
