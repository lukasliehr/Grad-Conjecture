import AEN7ActualOuterNativeBounds

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.ExceptionalNative
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.ActualCenterBounds Grad.ActualExceptionalInverse Grad.OrdinaryInteriorBootstrap Grad.ActualInverseInduction
open Grad.OrdinaryDiskCalculus
open Grad.NonlinearDivision (laplacianJet)
open Grad.GaugeCoefficients.Physical.RadialLedger (apLoweringConstant apLoweringConstant_nonnegative)
local instance (priority := 2000) nativeUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade

theorem signedDatum_laplacian_bound (grade : ℕ) (datum : SignedEquationDatum) :
    ‖unitDiskCoreInto grade (laplacianJet datum.field)‖ ≤
      ordinarySignedDerivativeConstant grade * ‖unitDiskCoreInto (grade + 1) datum.forcing‖ := by
  rw [signedEquation_laplacian datum.sign datum.signed datum.field datum.forcing datum.equation,
    unitDiskCore_norm, unitDiskCore_norm]
  exact ordinarySignedDerivative_bound grade (-datum.sign) (by rcases datum.signed with h | h <;> simp [h]) datum.forcing

def signedGlobalSourceConstant (grade order : ℕ) : ℝ :=
  ordinaryInteriorSourceConstant order * ordinarySignedDerivativeConstant order * apLoweringConstant (order + 1) +
    signedOuterConstant grade (order + 2)

theorem signedGlobalSourceConstant_nonnegative (grade order : ℕ) : 0 ≤ signedGlobalSourceConstant grade order :=
  add_nonneg (mul_nonneg (mul_nonneg (interiorSourceConstant_nonnegative order)
    (ordinarySignedDerivativeConstant_nonnegative order)) (apLoweringConstant_nonnegative (order + 1)))
    (signedOuterConstant_nonnegative grade (order + 2))

theorem signedDatum_global_step (grade order : ℕ) (paid : order + 1 ≤ grade) (datum : SignedEquationDatum) :
    ‖unitDiskCoreInto (order + 2) datum.field‖ ≤
      max 0 (ordinaryInteriorStateConstant order) * ‖unitDiskCoreInto (order + 1) datum.field‖ +
        signedGlobalSourceConstant grade order * signedNativeSize grade datum := by
  have split := ((unitDiskCoreInto (order + 2)).map_add (centerInnerJet datum.mode datum.field)
    (centerOuterJet datum.mode datum.field)).symm.trans
      (congrArg (unitDiskCoreInto (order + 2)) (center_partition datum.mode datum.field))
  have source := (originalCore_lower paid datum.forcing).trans
    (mul_le_mul_of_nonneg_left (signedNativeSize_source grade datum) (apLoweringConstant_nonnegative (order + 1)))
  have laplacian := (signedDatum_laplacian_bound order datum).trans
    (mul_le_mul_of_nonneg_left source (ordinarySignedDerivativeConstant_nonnegative order))
  have inner := (centerInner_native_estimate order datum.mode datum.field datum.pure).trans
    (add_le_add (mul_le_mul_of_nonneg_left laplacian (interiorSourceConstant_nonnegative order))
      (mul_le_mul_of_nonneg_right (le_max_right 0 _) (norm_nonneg _)))
  have outer := signedProfile_outer_native grade datum (order + 2) (by omega)
  have combined := (congrArg norm split).symm.le.trans ((norm_add_le _ _).trans (add_le_add inner outer))
  exact combined.trans_eq (by unfold signedGlobalSourceConstant; ring)

/-- Genuine global elliptic gain for the actual signed equation. Both the
collar recurrence and the interior Laplacian estimate have been proved above. -/
theorem signedNativeGain_exists (grade : ℕ) : ∃ constant : ℝ, 0 ≤ constant ∧ ∀ datum : SignedEquationDatum,
    ‖unitDiskCoreInto (grade + 1) datum.field‖ ≤ constant * signedNativeSize grade datum := by
  have all : ∀ target : ℕ, target ≤ grade → ∃ constant : ℝ, 0 ≤ constant ∧ ∀ datum : SignedEquationDatum,
      ‖unitDiskCoreInto (target + 1) datum.field‖ ≤ constant * signedNativeSize grade datum := by
    intro target
    induction target with
    | zero => exact fun _ => ⟨1, zero_le_one, fun datum => by simpa using signedNativeSize_base grade datum⟩
    | succ target previous =>
      intro paid
      obtain ⟨constant, nonnegative, estimates⟩ := previous (by omega)
      refine ⟨max 0 (ordinaryInteriorStateConstant target) * constant + signedGlobalSourceConstant grade target,
        add_nonneg (mul_nonneg (le_max_left _ _) nonnegative) (signedGlobalSourceConstant_nonnegative grade target), ?_⟩
      intro datum
      exact (signedDatum_global_step grade target paid datum).trans
        ((add_le_add (mul_le_mul_of_nonneg_left (estimates datum) (le_max_left _ _)) le_rfl).trans_eq (by ring))
  exact all grade le_rfl

def signedNativeGainConstant (grade : ℕ) : ℝ := (signedNativeGain_exists grade).choose

theorem signedNativeGainConstant_nonnegative (grade : ℕ) : 0 ≤ signedNativeGainConstant grade :=
  (signedNativeGain_exists grade).choose_spec.1

theorem signedNativeGain (grade : ℕ) (datum : SignedEquationDatum) :
    ‖unitDiskCoreInto (grade + 1) datum.field‖ ≤ signedNativeGainConstant grade * signedNativeSize grade datum :=
  (signedNativeGain_exists grade).choose_spec.2 datum

end Grad.ExceptionalNative
