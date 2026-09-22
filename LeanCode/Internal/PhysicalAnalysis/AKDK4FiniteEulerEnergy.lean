import AKDK3ActualSourceMixedRadialEnergy
import AKDA7ClosedCollarEulerFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped ENNReal
namespace Grad.OriginalTerminalAllocation
open Grad.OriginalCartesianTameEstimate

section Energy
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem boundedScalar_squareEnergy (lower : ℝ) (factor : ℝ → ℝ) (curve : ℝ → E) (constant payment : ℝ)
    (constant0 : 0≤constant) (bound : ∀ radius ∈ Icc lower 1, ‖factor radius‖≤constant)
    (energy : (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖curve radius‖^2)) ≤ ENNReal.ofReal (payment^2)) :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖factor radius • curve radius‖^2)) ≤
      ENNReal.ofReal ((constant*payment)^2) := by
  calc
    _ ≤ ∫⁻ radius in Icc lower 1, ENNReal.ofReal (constant^2)*ENNReal.ofReal (‖curve radius‖^2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
      rw [← ENNReal.ofReal_mul (sq_nonneg _),← mul_pow]
      apply ENNReal.ofReal_le_ofReal
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg constant0 (norm_nonneg _))).mpr
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (bound radius inside) (norm_nonneg _)
    _ = ENNReal.ofReal (constant^2)*(∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖curve radius‖^2)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (constant^2)*ENNReal.ofReal (payment^2) := mul_le_mul' le_rfl energy
    _ = _ := by rw [← ENNReal.ofReal_mul (sq_nonneg _),mul_pow]

def rawEulerEnergyPayment (cost : ℕ → ℝ) : List (ℕ × ℝ) → ℝ :=
  List.rec 0 (fun term _ previous => 2*(|term.2| *cost (term.1+1)+previous))

theorem rawEulerEnergyPayment_nonnegative (cost : ℕ → ℝ) (cost0 : ∀ rank, 0≤cost rank)
    (terms : List (ℕ × ℝ)) : 0≤rawEulerEnergyPayment cost terms := by
  induction terms with
  | nil => exact le_rfl
  | cons term terms previous => exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (abs_nonneg _) (cost0 _)) previous)

theorem rawEulerPolynomial_continuous (jets : ℕ → ℝ → E) (smooth : ∀ rank, Continuous (jets rank))
    (terms : List (ℕ × ℝ)) : Continuous (rawEulerPolynomial jets terms) := by
  induction terms with
  | nil => exact continuous_const
  | cons term terms previous =>
      exact (((continuous_id.pow (term.1+1)).smul (smooth (term.1+1))).const_smul term.2).add previous

theorem rawEulerPolynomial_squareEnergy (lower : ℝ) (positive : 0<lower)
    (jets : ℕ → ℝ → E) (smooth : ∀ rank, Continuous (jets rank))
    (cost : ℕ → ℝ) (cost0 : ∀ rank, 0≤cost rank) (payment : ℝ) (payment0 : 0≤payment)
    (terms : List (ℕ × ℝ))
    (energy : ∀ term ∈ terms,
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖jets (term.1+1) radius‖^2)) ≤ ENNReal.ofReal ((cost (term.1+1)*payment)^2)) :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖rawEulerPolynomial jets terms radius‖^2)) ≤
      ENNReal.ofReal ((rawEulerEnergyPayment cost terms*payment)^2) := by
  induction terms with
  | nil => simp [rawEulerPolynomial,rawEulerEnergyPayment]
  | cons term terms previous =>
      have tail := previous (fun tail member => energy tail (List.mem_cons_of_mem term member))
      have factor (radius : ℝ) (inside : radius ∈ Icc lower 1) : ‖term.2*radius^(term.1+1)‖ ≤ |term.2| := by
        rw [norm_mul,Real.norm_eq_abs term.2,Real.norm_eq_abs]
        rw [abs_of_nonneg (pow_nonneg (positive.le.trans inside.1) _)]
        exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (positive.le.trans inside.1) inside.2)
      have first := boundedScalar_squareEnergy lower (fun radius => term.2*radius^(term.1+1))
        (jets (term.1+1)) |term.2| (cost (term.1+1)*payment) (abs_nonneg _) factor
        (energy term List.mem_cons_self)
      have firstM : Continuous (fun radius => (term.2*radius^(term.1+1)) • jets (term.1+1) radius) :=
        (continuous_const.mul (continuous_id.pow _)).smul (smooth _)
      have assembled := twoInput_squareEnergy (volume.restrict (Icc lower 1))
        (rawEulerPolynomial jets (term::terms))
        (fun radius => (term.2*radius^(term.1+1)) • jets (term.1+1) radius) (rawEulerPolynomial jets terms)
        firstM.aestronglyMeasurable (rawEulerPolynomial_continuous jets smooth terms).aestronglyMeasurable
        1 1 (|term.2| *(cost (term.1+1)*payment)) (rawEulerEnergyPayment cost terms*payment)
        (by norm_num) (by norm_num) (mul_nonneg (abs_nonneg _) (mul_nonneg (cost0 _) payment0))
        (mul_nonneg (rawEulerEnergyPayment_nonnegative cost cost0 terms) payment0)
        (Filter.Eventually.of_forall (fun radius => by
          change ‖term.2 • (radius^(term.1+1) • jets (term.1+1) radius)+rawEulerPolynomial jets terms radius‖ ≤ _
          simpa only [one_mul,smul_smul] using norm_add_le ((term.2*radius^(term.1+1)) • jets (term.1+1) radius) (rawEulerPolynomial jets terms radius)))
        first tail
      exact assembled.trans_eq (by congr 1; dsimp only [rawEulerEnergyPayment]; ring)
end Energy
end Grad.OriginalTerminalAllocation
