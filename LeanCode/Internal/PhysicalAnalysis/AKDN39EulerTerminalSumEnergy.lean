import AKDN35ActualKappaProductEulerAllocation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped ENNReal
namespace Grad.OriginalCartesianTameEstimate

theorem eulerAllocationSum_measurable {Point : Type*} [MeasurableSpace Point]
    (measure : Measure Point) (values : ℕ → ℕ → Point → ℝ) (terms : List (ℕ × ℕ))
    (measurable : ∀ term ∈ terms, AEStronglyMeasurable (values term.1 term.2) measure) :
    AEStronglyMeasurable (fun point => eulerAllocationSum (fun a b => values a b point) terms) measure := by
  induction terms with
  | nil => exact aestronglyMeasurable_const
  | cons term terms previous =>
      have tail := previous (fun index member => measurable index (List.mem_cons_of_mem term member))
      apply ((measurable term List.mem_cons_self).add tail).congr
      exact Filter.Eventually.of_forall (fun _ => rfl)

/-- Finite Euler sums are integrated only after every coefficient/source
term has received its joint one-high payment. -/
theorem eulerAllocationSum_squareEnergy {Point : Type*} [MeasurableSpace Point]
    (measure : Measure Point) (values : ℕ → ℕ → Point → ℝ) (payment : ℝ) (payment0 : 0 ≤ payment)
    (terms : List (ℕ × ℕ))
    (measurable : ∀ term ∈ terms, AEStronglyMeasurable (values term.1 term.2) measure)
    (energy : ∀ term ∈ terms,
      (∫⁻ point, ENNReal.ofReal (‖values term.1 term.2 point‖^2) ∂measure) ≤ ENNReal.ofReal (payment^2)) :
    (∫⁻ point, ENNReal.ofReal (‖eulerAllocationSum (fun a b => values a b point) terms‖^2) ∂measure) ≤
      ENNReal.ofReal (((4:ℝ)^terms.length*payment)^2) := by
  induction terms with
  | nil =>
      change (∫⁻ _ : Point, ENNReal.ofReal (‖(0:ℝ)‖^2) ∂measure) ≤ _
      simp only [norm_zero,zero_pow (by decide : (2:ℕ)≠0),ENNReal.ofReal_zero,lintegral_zero]
      exact bot_le
  | cons term terms previous =>
      have tailMeasurable := fun index member => measurable index (List.mem_cons_of_mem term member)
      have tailEnergy := previous tailMeasurable (fun index member => energy index (List.mem_cons_of_mem term member))
      have previous0 : 0 ≤ (4:ℝ)^terms.length*payment := mul_nonneg (by positivity) payment0
      have actual := twoInput_squareEnergy measure
        (fun point => eulerAllocationSum (fun a b => values a b point) (term::terms))
        (values term.1 term.2) (fun point => eulerAllocationSum (fun a b => values a b point) terms)
        (measurable term List.mem_cons_self) (eulerAllocationSum_measurable measure values terms tailMeasurable)
        1 1 payment ((4:ℝ)^terms.length*payment) zero_le_one zero_le_one payment0 previous0 (by
          apply Filter.Eventually.of_forall
          intro point
          change ‖values term.1 term.2 point+eulerAllocationSum (fun a b => values a b point) terms‖ ≤ _
          simpa only [one_mul] using norm_add_le (values term.1 term.2 point) (eulerAllocationSum (fun a b => values a b point) terms))
        (energy term List.mem_cons_self) tailEnergy
      apply actual.trans
      apply ENNReal.ofReal_le_ofReal
      apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
      rw [List.length_cons,pow_succ]
      have one : (1:ℝ) ≤ 4^terms.length := one_le_pow₀ (by norm_num)
      have paid := mul_le_mul_of_nonneg_right one payment0
      nlinarith only [paid]

end Grad.OriginalCartesianTameEstimate
