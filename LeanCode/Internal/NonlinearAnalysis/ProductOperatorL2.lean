import ProductDiskL2

noncomputable section

open scoped BigOperators ENNReal

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState

def weightedOperatorL2Majorant {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (order power : ℕ) : lp (fun _ : ℤ => ℝ) 2 :=
  ∑ word : CartesianWord order,
    ‖spatialPlaneWordCoefficient word‖ • weightedWordL2Sequence parameters field word power

theorem weightedOperatorL2Majorant_value {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (order power : ℕ) (cell : ℤ) :
    weightedOperatorL2Majorant parameters field order power cell =
      ∑ word : CartesianWord order, ‖spatialPlaneWordCoefficient word‖ *
        (cellFrequency cell ^ power * ‖closedContinuousToDiskL2
          (closedDerivative (phaseWeightedJet parameters cell (field.val cell)) order word)‖) := by
  simp only [weightedOperatorL2Majorant, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, weightedWordL2Sequence_value]

theorem weightedOperatorL2Majorant_nonnegative {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (order power : ℕ) (cell : ℤ) :
    0 ≤ weightedOperatorL2Majorant parameters field order power cell := by
  rw [weightedOperatorL2Majorant_value]
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _)
    (mul_nonneg (pow_nonneg (cellFrequency_pos cell).le power) (norm_nonneg _)))

theorem weightedOperatorL2Majorant_norm_bound {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (order power : ℕ) :
    ‖weightedOperatorL2Majorant parameters field order power‖ ≤
      wordOperatorFactor order * originalGradeNorm (order + power) field := by
  apply (norm_sum_le _ _).trans
  calc
    _ = ∑ word : CartesianWord order, ‖spatialPlaneWordCoefficient word‖ *
        ‖weightedWordL2Sequence parameters field word power‖ := by
      apply Finset.sum_congr rfl
      intro word _
      rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _)]
    _ ≤ ∑ word : CartesianWord order, ‖spatialPlaneWordCoefficient word‖ *
        originalGradeNorm (order + power) field :=
      Finset.sum_le_sum (fun word _ => mul_le_mul_of_nonneg_left
        (weightedWordL2Sequence_norm_bound parameters field word power) (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem weightedOperatorL2Majorant_dominates {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (order power : ℕ) (cell : ℤ) :
    cellFrequency cell ^ power *
      ‖closedMapL2 (jetOperatorDerivative order (phaseWeightedJet parameters cell (field.val cell)))‖ ≤
      weightedOperatorL2Majorant parameters field order power cell := by
  rw [weightedOperatorL2Majorant_value]
  calc
    _ ≤ cellFrequency cell ^ power * ∑ word : CartesianWord order,
        ‖spatialPlaneWordCoefficient word‖ * ‖closedContinuousToDiskL2
          (closedDerivative (phaseWeightedJet parameters cell (field.val cell)) order word)‖ :=
      mul_le_mul_of_nonneg_left (jetOperatorDerivative_L2_bound _)
        (pow_nonneg (cellFrequency_pos cell).le power)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

/-- Exact weighted full-derivative L2 sequence of the last input. -/
def weightedOperatorL2Sequence {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (order power : ℕ) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨fun cell => cellFrequency cell ^ power *
      ‖closedMapL2 (jetOperatorDerivative order (phaseWeightedJet parameters cell (field.val cell)))‖, by
    apply (lp.memℓp (weightedOperatorL2Majorant parameters field order power)).mono'
    intro cell
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (cellFrequency_pos cell).le power) (norm_nonneg _)),
      Real.norm_of_nonneg (weightedOperatorL2Majorant_nonnegative parameters field order power cell)]
    exact weightedOperatorL2Majorant_dominates parameters field order power cell⟩

theorem weightedOperatorL2Sequence_nonnegative {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (order power : ℕ) (cell : ℤ) :
    0 ≤ weightedOperatorL2Sequence parameters field order power cell :=
  mul_nonneg (pow_nonneg (cellFrequency_pos cell).le power) (norm_nonneg _)

theorem weightedOperatorL2Sequence_value {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (order power : ℕ) (cell : ℤ) :
    weightedOperatorL2Sequence parameters field order power cell = cellFrequency cell ^ power *
      ‖closedMapL2 (jetOperatorDerivative order (phaseWeightedJet parameters cell (field.val cell)))‖ := rfl

theorem weightedOperatorL2Sequence_norm_bound {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (order power : ℕ) :
    ‖weightedOperatorL2Sequence parameters field order power‖ ≤
      wordOperatorFactor order * originalGradeNorm (order + power) field := by
  apply le_trans _ (weightedOperatorL2Majorant_norm_bound parameters field order power)
  apply lp.norm_mono (by norm_num)
  intro cell
  rw [Real.norm_of_nonneg (weightedOperatorL2Sequence_nonnegative parameters field order power cell),
    Real.norm_of_nonneg (weightedOperatorL2Majorant_nonnegative parameters field order power cell)]
  exact weightedOperatorL2Majorant_dominates parameters field order power cell

end Grad.NonlinearProduct
