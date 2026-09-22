import RadialIntegralL2

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Grad.NonlinearRadial

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.AnalyticWeights.Higher

theorem radial_word_majorant {dimension rank : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (grade : ℕ) (word : CartesianWord rank) (rankBound : rank ≤ grade) :
    ∃ majorant : lp (fun _ : ℤ => ℝ) 2,
      (∀ cell, 0 ≤ majorant cell) ∧
      (∀ cell, cellFrequency cell ^ (grade - rank) *
        radialWordCellBound parameters cell (field.val cell) word = majorant cell) ∧
      ‖majorant‖ ≤ dilationWordConstant rank * originalGradeNorm grade field := by
  classical
  let terms : Finset (Fin rank) → lp (fun _ : ℤ => ℝ) 2 := fun selected =>
    dilationDerivativeConstant selected.card •
      weightedWordL2Sequence parameters field (subword word selectedᶜ) (grade - selectedᶜ.card)
  have cardBound (selected : Finset (Fin rank)) : selectedᶜ.card ≤ grade := by
    have bound := Finset.card_le_univ selectedᶜ
    rw [Fintype.card_fin] at bound
    exact bound.trans rankBound
  have complement (selected : Finset (Fin rank)) : selected.card + selectedᶜ.card = rank := by
    have equality := selected.card_add_card_compl
    rw [Fintype.card_fin] at equality
    exact equality
  have termsNonnegative (selected : Finset (Fin rank)) (cell : ℤ) : 0 ≤ terms selected cell :=
    mul_nonneg (dilationDerivativeConstant_nonnegative _) (weightedWordL2Sequence_nonnegative _ _ _ _ _)
  have value (cell : ℤ) : (∑ selected, terms selected) cell = ∑ selected, terms selected cell := by
    simp only [lp.coeFn_sum, Finset.sum_apply]
  refine ⟨∑ selected, terms selected, ?_, ?_, ?_⟩
  · intro cell
    rw [value]
    exact Finset.sum_nonneg (fun selected _ => termsNonnegative selected cell)
  · intro cell
    rw [radialWordCellBound, value, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro selected _
    change _ = dilationDerivativeConstant selected.card *
      weightedWordL2Sequence parameters field (subword word selectedᶜ) (grade - selectedᶜ.card) cell
    rw [weightedWordL2Sequence_value]
    have power : grade - selectedᶜ.card = grade - rank + selected.card := by
      have := complement selected
      omega
    rw [power, pow_add]
    ring
  · calc
      _ ≤ ∑ selected, ‖terms selected‖ := norm_sum_le _ _
      _ ≤ ∑ selected : Finset (Fin rank),
          dilationDerivativeConstant selected.card * originalGradeNorm grade field := by
        apply Finset.sum_le_sum
        intro selected _
        change ‖dilationDerivativeConstant selected.card •
          weightedWordL2Sequence parameters field (subword word selectedᶜ) (grade - selectedᶜ.card)‖ ≤ _
        rw [norm_smul, Real.norm_of_nonneg (dilationDerivativeConstant_nonnegative _)]
        have bound := weightedWordL2Sequence_norm_bound parameters field (subword word selectedᶜ)
          (grade - selectedᶜ.card)
        rw [Nat.add_sub_of_le (cardBound selected)] at bound
        exact mul_le_mul_of_nonneg_left bound (dilationDerivativeConstant_nonnegative _)
      _ = _ := by rw [← Finset.sum_mul]; rfl

theorem radial_interval_grade_majorant {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) {lower upper : ℝ}
    (lowerNonnegative : 0 ≤ lower) (upperBounded : upper ≤ 1) (grade : ℕ) :
    ∃ majorant : lp (fun _ : ℤ => ℝ) 2,
      (∀ cell, 0 ≤ majorant cell) ∧
      (∀ cell, ‖rawCartesianGradeCoordinates parameters grade
        (fun cell => radialIntervalJet lower upper (field.val cell)) cell‖ ≤ majorant cell) ∧
      ‖majorant‖ ≤ dilationGradeConstant grade * logarithmicMass lower upper * originalGradeNorm grade field := by
  classical
  choose majorants nonnegative pointEqualities normBounds using
    (fun index : GradeMultiIndex grade => radial_word_majorant parameters field grade
      (cartesianMultiIndexWord index.toCartesian) index.property)
  let scaled : GradeMultiIndex grade → lp (fun _ : ℤ => ℝ) 2 :=
    fun index => logarithmicMass lower upper • majorants index
  have massNonnegative := logarithmicMass_nonnegative lowerNonnegative upperBounded
  have scaledNonnegative (index : GradeMultiIndex grade) (cell : ℤ) : 0 ≤ scaled index cell :=
    mul_nonneg massNonnegative (nonnegative index cell)
  have value (cell : ℤ) : (∑ index, scaled index) cell = ∑ index, scaled index cell := by
    simp only [lp.coeFn_sum, Finset.sum_apply]
  refine ⟨∑ index, scaled index, ?_, ?_, ?_⟩
  · intro cell
    rw [value]
    exact Finset.sum_nonneg (fun index _ => scaledNonnegative index cell)
  · intro cell
    rw [value]
    apply finite_row_norm_le_majorants _ _ (fun index => scaledNonnegative index cell)
    intro index
    change ‖(cellFrequency cell : ℂ) ^ (grade - cartesianOrder index.toCartesian) •
      closedContinuousToDiskL2 (closedMultiDerivative
        (phaseWeightedJet parameters cell (radialIntervalJet lower upper (field.val cell))) index.toCartesian)‖ ≤ _
    rw [norm_smul, Complex.norm_pow, Complex.norm_real, Real.norm_of_nonneg (cellFrequency_pos cell).le]
    apply (mul_le_mul_of_nonneg_left (radialIntervalJet_L2_bound parameters cell lowerNonnegative upperBounded
      (field.val cell) (cartesianMultiIndexWord index.toCartesian)) (pow_nonneg (cellFrequency_pos cell).le _)).trans_eq
    change _ = logarithmicMass lower upper * majorants index cell
    rw [← pointEqualities index cell]
    ring
  · calc
      _ ≤ ∑ index, ‖scaled index‖ := norm_sum_le _ _
      _ ≤ ∑ index : GradeMultiIndex grade,
          logarithmicMass lower upper *
            (dilationWordConstant (cartesianOrder index.toCartesian) * originalGradeNorm grade field) := by
        apply Finset.sum_le_sum
        intro index _
        change ‖logarithmicMass lower upper • majorants index‖ ≤ _
        rw [norm_smul, Real.norm_of_nonneg massNonnegative]
        exact mul_le_mul_of_nonneg_left (normBounds index) massNonnegative
      _ = _ := by
        rw [← Finset.mul_sum, ← Finset.sum_mul]
        unfold dilationGradeConstant
        ring

theorem radialInterval_mem_core {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) {lower upper : ℝ}
    (lowerNonnegative : 0 ≤ lower) (upperBounded : upper ≤ 1) :
    (fun cell => radialIntervalJet lower upper (field.val cell)) ∈ originalCoreSubmodule parameters dimension := by
  intro grade
  obtain ⟨majorant, nonnegative, bound, _⟩ :=
    radial_interval_grade_majorant parameters field lowerNonnegative upperBounded grade
  apply (lp.memℓp majorant).mono'
  intro cell
  rw [Real.norm_of_nonneg (nonnegative cell)]
  exact bound cell

def radialIntervalCore {dimension : ℕ} (parameters : PhaseParameters)
    (lower upper : ℝ) (lowerNonnegative : 0 ≤ lower) (upperBounded : upper ≤ 1)
    (field : ACore parameters dimension) : ACore parameters dimension :=
  ⟨fun cell => radialIntervalJet lower upper (field.val cell),
    radialInterval_mem_core parameters field lowerNonnegative upperBounded⟩

theorem radialIntervalCore_bound {dimension : ℕ} (parameters : PhaseParameters)
    (lower upper : ℝ) (lowerNonnegative : 0 ≤ lower) (upperBounded : upper ≤ 1)
    (field : ACore parameters dimension) (grade : ℕ) :
    originalGradeNorm grade (radialIntervalCore parameters lower upper lowerNonnegative upperBounded field) ≤
      dilationGradeConstant grade * logarithmicMass lower upper * originalGradeNorm grade field := by
  obtain ⟨majorant, nonnegative, pointBounds, normBound⟩ :=
    radial_interval_grade_majorant parameters field lowerNonnegative upperBounded grade
  apply le_trans _ normBound
  unfold originalGradeNorm
  rw [gradeCore_norm_eq_cartesianGradeSeminorm, cartesianGradeSeminorm_apply, gradeCoreCoordinates_apply]
  apply lp.norm_mono (by norm_num)
  intro cell
  rw [Real.norm_of_nonneg (nonnegative cell)]
  exact pointBounds cell

theorem radialIntervalJet_add {dimension : ℕ} (lower upper : ℝ)
    (lowerNonnegative : 0 ≤ lower) (upperBounded : upper ≤ 1)
    (first second : ClosedJet dimension) :
    radialIntervalJet lower upper (first + second) =
      radialIntervalJet lower upper first + radialIntervalJet lower upper second := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change radialIntervalValue lower upper (first + second) point.val =
    radialIntervalValue lower upper first point.val + radialIntervalValue lower upper second point.val
  unfold radialIntervalValue
  have integrable (field : ClosedJet dimension) : IntegrableOn
      (fun scale : ℝ => Real.negMulLog scale • Grad.Constraints.smoothClosedExtension field (scale • point.val))
      (Icc lower upper) :=
    (Real.continuous_negMulLog.smul ((Grad.Constraints.smoothClosedExtension_smooth field).continuous.comp
      (continuous_id.smul continuous_const))).continuousOn.integrableOn_Icc
  rw [← integral_add (integrable first) (integrable second)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro scale scaleIn
  dsimp only
  rw [← smul_add]
  congr 1
  let contracted := dilationPoint scale (lowerNonnegative.trans scaleIn.1) (scaleIn.2.trans upperBounded) point
  change Grad.Constraints.smoothClosedExtension (first + second) contracted.val =
    Grad.Constraints.smoothClosedExtension first contracted.val +
      Grad.Constraints.smoothClosedExtension second contracted.val
  rw [Grad.Constraints.smoothClosedExtension_value, Grad.Constraints.smoothClosedExtension_value,
    Grad.Constraints.smoothClosedExtension_value]
  rfl

theorem radialIntervalJet_smul {dimension : ℕ} (lower upper : ℝ)
    (lowerNonnegative : 0 ≤ lower) (upperBounded : upper ≤ 1)
    (scalar : ℂ) (field : ClosedJet dimension) :
    radialIntervalJet lower upper (scalar • field) = scalar • radialIntervalJet lower upper field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change radialIntervalValue lower upper (scalar • field) point.val =
    scalar • radialIntervalValue lower upper field point.val
  unfold radialIntervalValue
  rw [← integral_smul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro scale scaleIn
  dsimp only
  rw [smul_comm scalar]
  congr 1
  let contracted := dilationPoint scale (lowerNonnegative.trans scaleIn.1) (scaleIn.2.trans upperBounded) point
  change Grad.Constraints.smoothClosedExtension (scalar • field) contracted.val =
    scalar • Grad.Constraints.smoothClosedExtension field contracted.val
  rw [Grad.Constraints.smoothClosedExtension_value, Grad.Constraints.smoothClosedExtension_value]
  rfl

def radialIntervalCoreLinear {dimension : ℕ} (parameters : PhaseParameters)
    (lower upper : ℝ) (lowerNonnegative : 0 ≤ lower) (upperBounded : upper ≤ 1) :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension where
  toFun := radialIntervalCore parameters lower upper lowerNonnegative upperBounded
  map_add' first second := by
    apply Subtype.ext
    funext cell
    exact radialIntervalJet_add lower upper lowerNonnegative upperBounded (first.val cell) (second.val cell)
  map_smul' scalar field := by
    apply Subtype.ext
    funext cell
    exact radialIntervalJet_smul lower upper lowerNonnegative upperBounded scalar (field.val cell)

def radialCore {dimension : ℕ} (parameters : PhaseParameters) :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension :=
  radialIntervalCoreLinear parameters 0 1 le_rfl le_rfl

theorem radialCore_actual {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension) :
    IsActualRadialIntegral field (radialCore parameters field) := by
  intro cell point
  exact radialIntervalJet_full_value (field.val cell) point

theorem radialCore_bound {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (field : ACore parameters dimension) :
    originalGradeNorm grade (radialCore parameters field) ≤
      dilationGradeConstant grade * originalGradeNorm grade field := by
  have bound := radialIntervalCore_bound parameters 0 1 le_rfl le_rfl field grade
  rw [logarithmicMass_unit, mul_one] at bound
  exact bound

theorem actual_radial_core : RadialCoreGoal :=
  ⟨dilationGradeConstant, dilationGradeConstant_nonnegative, fun parameters _ =>
    ⟨radialCore parameters, radialCore_actual parameters, radialCore_bound parameters⟩⟩

end Grad.NonlinearRadial
