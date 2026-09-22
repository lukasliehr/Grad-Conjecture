import AKDN32ActualFiniteEulerInduction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped ENNReal
namespace Grad.OriginalCartesianTameEstimate

/-- One finite energy assembly, with constants depending only on the
finite number of actual terminal terms. No state budget is multiplied here. -/
theorem finiteSum_squareEnergy {Index Point Value : Type*} [MeasurableSpace Point]
    [NormedAddCommGroup Value] (measure : Measure Point) (curves : Index → Point → Value)
    (measurable : ∀ index, AEStronglyMeasurable (curves index) measure)
    (payment : ℝ) (payment0 : 0 ≤ payment)
    (energy : ∀ index, (∫⁻ point, ENNReal.ofReal (‖curves index point‖^2) ∂measure) ≤ ENNReal.ofReal (payment^2))
    (terms : Finset Index) :
    (∫⁻ point, ENNReal.ofReal (‖∑ index ∈ terms, curves index point‖^2) ∂measure) ≤
      ENNReal.ofReal (((4:ℝ)^terms.card*payment)^2) := by
  classical
  have sumMeasurable (terms : Finset Index) :
      AEStronglyMeasurable (fun point => ∑ index ∈ terms, curves index point) measure := by
    induction terms using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : Point => (0:Value)) measure)
    | @insert index terms absent previous =>
        apply ((measurable index).add previous).congr
        apply Filter.Eventually.of_forall
        intro point
        change curves index point+(∑ current ∈ terms, curves current point) =
          ∑ current ∈ insert index terms, curves current point
        rw [Finset.sum_insert absent]
  induction terms using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty,norm_zero,zero_pow (by decide : (2:ℕ)≠0),ENNReal.ofReal_zero,lintegral_zero]
      exact bot_le
  | @insert index terms absent previous =>
      have previous0 : 0 ≤ (4:ℝ)^terms.card*payment := mul_nonneg (by positivity) payment0
      have actual := twoInput_squareEnergy measure
        (fun point => ∑ current ∈ insert index terms, curves current point)
        (curves index) (fun point => ∑ current ∈ terms, curves current point)
        (measurable index) (sumMeasurable terms) 1 1 payment ((4:ℝ)^terms.card*payment)
        zero_le_one zero_le_one payment0 previous0 (by
          apply Filter.Eventually.of_forall
          intro point
          simpa only [Finset.sum_insert absent,one_mul] using
            norm_add_le (curves index point) (∑ current ∈ terms, curves current point))
        (energy index) previous
      apply actual.trans
      apply ENNReal.ofReal_le_ofReal
      apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
      rw [Finset.card_insert_of_notMem absent,pow_succ]
      have one : (1:ℝ) ≤ 4^terms.card := one_le_pow₀ (by norm_num)
      have paid := mul_le_mul_of_nonneg_right one payment0
      nlinarith only [paid]

/-- A nonnegative scalar bound can be integrated directly against a
known terminal energy. This avoids introducing an auxiliary L2 space. -/
theorem dominated_squareEnergy {Point Value : Type*} [MeasurableSpace Point] [NormedAddCommGroup Value]
    (measure : Measure Point) (output : Point → Value) (terminal : Point → ℝ)
    (constant payment : ℝ) (constant0 : 0 ≤ constant)
    (terminal0 : ∀ᵐ point ∂measure, 0 ≤ terminal point)
    (bound : ∀ᵐ point ∂measure, ‖output point‖ ≤ constant*terminal point)
    (energy : (∫⁻ point, ENNReal.ofReal (terminal point^2) ∂measure) ≤ ENNReal.ofReal (payment^2)) :
    (∫⁻ point, ENNReal.ofReal (‖output point‖^2) ∂measure) ≤ ENNReal.ofReal ((constant*payment)^2) := by
  have actual : ∀ᵐ point ∂measure, ENNReal.ofReal (‖output point‖^2) ≤
      ENNReal.ofReal (constant^2)*ENNReal.ofReal (terminal point^2) := by
    filter_upwards [terminal0,bound] with point positive paid
    rw [←ENNReal.ofReal_mul (sq_nonneg _),←mul_pow]
    exact ENNReal.ofReal_le_ofReal ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg constant0 positive)).mpr paid)
  apply (lintegral_mono_ae actual).trans
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact (mul_le_mul' le_rfl energy).trans_eq (by rw [←ENNReal.ofReal_mul (sq_nonneg _),mul_pow])

end Grad.OriginalCartesianTameEstimate
