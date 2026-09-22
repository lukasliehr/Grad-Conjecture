import GC18APInverseHigh

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

def apLoweringConstant (grade : ℕ) : ℝ := Real.sqrt (Fintype.card (DerivativeIndex grade))

theorem apLoweringConstant_nonnegative (grade : ℕ) : 0 ≤ apLoweringConstant grade := Real.sqrt_nonneg _

theorem apLowerRow_bound {dimension low high : ℕ} (L sigma gamma ell : ℝ) (ordered : low ≤ high)
    (cell : ℤ) (field : ClosedJet dimension) :
    ‖apRowLinear (grade := low) L sigma gamma ell cell field‖ ≤
      apLoweringConstant low * ‖apRowLinear (grade := high) L sigma gamma ell cell field‖ := by
  apply apRow_norm_bound_of_coordinates _ _ (norm_nonneg _)
  intro index
  rw [apRowLinear_apply, norm_smul, Complex.norm_pow, Complex.norm_real, Real.norm_of_nonneg (scaledCellWeight_nonnegative L ell cell)]
  calc
    _ ≤ scaledCellWeight L ell cell ^ (high - derivativeOrder index) *
        ‖closedDerivativeL2 (derivativeMultiIndex index) (apWeightedJet sigma gamma ell cell field)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (scaledCellWeight_one_le L ell cell) (Nat.sub_le_sub_right ordered _)) (norm_nonneg _)
    _ ≤ _ := apWeighted_word_bound L sigma gamma ell cell field (index.property.trans ordered)
      (apIndexWord index)

theorem apLowerFinite_bound {dimension low high : ℕ} (L sigma gamma ell : ℝ) (ordered : low ≤ high)
    (core : ℤ →₀ ClosedJet dimension) :
    ‖apFiniteInto (grade := low) L sigma gamma ell core‖ ≤
      apLoweringConstant low * ‖apFiniteInto (grade := high) L sigma gamma ell core‖ := by
  change ‖apFiniteEmbed (grade := low) L sigma gamma ell core‖ ≤
    apLoweringConstant low * ‖apFiniteEmbed (grade := high) L sigma gamma ell core‖
  calc
    _ ≤ ‖(apLoweringConstant low : ℂ) • apFiniteEmbed (grade := high) L sigma gamma ell core‖ := by
      apply lp.norm_mono (by norm_num)
      intro cell
      change ‖apFiniteEmbed (grade := low) L sigma gamma ell core cell‖ ≤
        ‖(apLoweringConstant low : ℂ) • apFiniteEmbed (grade := high) L sigma gamma ell core cell‖
      rw [apFiniteEmbed_apply, apFiniteEmbed_apply, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (apLoweringConstant_nonnegative low)]
      exact apLowerRow_bound L sigma gamma ell ordered cell (core cell)
    _ = _ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (apLoweringConstant_nonnegative low)]

theorem apLowering_exists {dimension low high : ℕ} (L sigma gamma ell : ℝ) (ordered : low ≤ high) :
    ∃ lowering : apGrade L sigma gamma ell dimension high →L[ℂ] apGrade L sigma gamma ell dimension low,
      (∀ core, lowering (apFiniteInto L sigma gamma ell core) = apFiniteInto L sigma gamma ell core) ∧
      (∀ field, ‖lowering field‖ ≤ apLoweringConstant low * ‖field‖) :=
  apDense_extension (apFiniteInto (grade := high) L sigma gamma ell)
    (apFiniteInto_injective L sigma gamma ell) (apFiniteInto_denseRange L sigma gamma ell)
    (apFiniteInto (grade := low) L sigma gamma ell) (apLoweringConstant low)
    (apLoweringConstant_nonnegative low) (apLowerFinite_bound L sigma gamma ell ordered)

def apLowering {dimension low high : ℕ} (L sigma gamma ell : ℝ) (ordered : low ≤ high) :
    apGrade L sigma gamma ell dimension high →L[ℂ] apGrade L sigma gamma ell dimension low :=
  (apLowering_exists L sigma gamma ell ordered).choose

theorem apLowering_core {dimension low high : ℕ} (L sigma gamma ell : ℝ) (ordered : low ≤ high)
    (core : ℤ →₀ ClosedJet dimension) :
    apLowering L sigma gamma ell ordered (apFiniteInto L sigma gamma ell core) = apFiniteInto L sigma gamma ell core :=
  (apLowering_exists (dimension := dimension) L sigma gamma ell ordered).choose_spec.1 core

theorem apLowering_bound {dimension low high : ℕ} (L sigma gamma ell : ℝ) (ordered : low ≤ high)
    (field : apGrade L sigma gamma ell dimension high) :
    ‖apLowering L sigma gamma ell ordered field‖ ≤ apLoweringConstant low * ‖field‖ :=
  (apLowering_exists L sigma gamma ell ordered).choose_spec.2 field

theorem apLowering_denseRange {dimension low high : ℕ} (L sigma gamma ell : ℝ) (ordered : low ≤ high) :
    DenseRange (apLowering (dimension := dimension) L sigma gamma ell ordered) := by
  apply (apFiniteInto_denseRange (dimension := dimension) (grade := low) L sigma gamma ell).mono
  rintro _ ⟨core, rfl⟩
  exact ⟨apFiniteInto L sigma gamma ell core, apLowering_core L sigma gamma ell ordered core⟩

theorem apLowering_complement {low high : ℕ} (L sigma gamma ell : ℝ) (ordered : low ≤ high)
    (field : apGrade L sigma gamma ell 3 high) :
    apLowering L sigma gamma ell ordered (apComplement L sigma gamma ell high field) =
      apComplement L sigma gamma ell low (apLowering L sigma gamma ell ordered field) := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := 3) (grade := high) L sigma gamma ell)
    (isClosed_eq ((apLowering L sigma gamma ell ordered).continuous.comp (apComplement L sigma gamma ell high).continuous)
      ((apComplement L sigma gamma ell low).continuous.comp (apLowering L sigma gamma ell ordered).continuous)) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apComplement_core, apLowering_core, apLowering_core, apComplement_core]

end Grad.GaugeCoefficients.Physical.RadialLedger
