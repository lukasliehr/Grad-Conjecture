import AKN20OriginalWeakGraphDecode
import ASG12FaithfulFourierBulk

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularSourceGraph

private theorem divisionRow_summable_sq (dimension : ℕ) (lower : ℝ)
    (field : DivisionRow dimension lower) : Summable (fun mode => ‖field mode‖ ^ 2) := by
  have finite := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).mp field.property
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using finite

private theorem divisionRow_norm_sq (dimension : ℕ) (lower : ℝ)
    (field : DivisionRow dimension lower) : ‖field‖ ^ 2 = ∑' mode, ‖field mode‖ ^ 2 := by
  have formula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using formula

/-- The accepted source derivative graph realizes the original AH Fourier
completion with exact value, derivative, and norm. There is no collar-dependent
comparison constant. -/
theorem sourceGraph_realization_exists (parameters : PhaseParameters) (dimension : ℕ)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (value derivative : DivisionRow dimension lower)
    (weak : ∀ mode, HasWeakRadialDerivative lower positive (value mode) (derivative mode)) :
    ∃ field : AnnularSourceH1 parameters dimension lower angular cell,
      annularSourceCoordinate parameters dimension lower angular cell 0 field = value ∧
      annularSourceCoordinate parameters dimension lower angular cell 1 field = derivative ∧
      ‖field‖ ^ 2 = ‖value‖ ^ 2 + ‖derivative‖ ^ 2 := by
  choose modes first second using fun mode =>
    sourceWeakPair_realization dimension lower positive bounded (value mode) (derivative mode) (weak mode)
  have energy (mode : ℤ × ℤ) : ‖modes mode‖ ^ 2 = ‖value mode‖ ^ 2 + ‖derivative mode‖ ^ 2 := by
    rw [weightedRadialH1_norm_sq, first, second]
  have finite := (divisionRow_summable_sq dimension lower value).add
    (divisionRow_summable_sq dimension lower derivative)
  let field : AnnularSourceH1 parameters dimension lower angular cell := ⟨modes, by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
    exact finite.congr (fun mode => (energy mode).symm)⟩
  refine ⟨field, ?_, ?_, ?_⟩
  · apply lp.ext
    funext mode
    exact first mode
  · apply lp.ext
    funext mode
    exact second mode
  · rw [annularSource_norm_sq]
    change (∑' mode : ℤ × ℤ, (‖weightedRadialCoordinate dimension lower 0 (modes mode)‖ ^ 2 +
      ‖weightedRadialCoordinate dimension lower 1 (modes mode)‖ ^ 2)) = _
    simp_rw [first, second]
    rw [(divisionRow_summable_sq dimension lower value).tsum_add
      (divisionRow_summable_sq dimension lower derivative),
      ← divisionRow_norm_sq dimension lower value, ← divisionRow_norm_sq dimension lower derivative]

def sourceGraphRealization (parameters : PhaseParameters) (dimension : ℕ)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (value derivative : DivisionRow dimension lower)
    (weak : ∀ mode, HasWeakRadialDerivative lower positive (value mode) (derivative mode)) :
    AnnularSourceH1 parameters dimension lower angular cell :=
  (sourceGraph_realization_exists parameters dimension lower positive bounded angular cell value derivative weak).choose

theorem sourceGraphRealization_value (parameters : PhaseParameters) (dimension : ℕ)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (value derivative : DivisionRow dimension lower)
    (weak : ∀ mode, HasWeakRadialDerivative lower positive (value mode) (derivative mode)) :
    annularSourceCoordinate parameters dimension lower angular cell 0
      (sourceGraphRealization parameters dimension lower positive bounded angular cell value derivative weak) = value :=
  (sourceGraph_realization_exists parameters dimension lower positive bounded angular cell value derivative weak).choose_spec.1

theorem sourceGraphRealization_derivative (parameters : PhaseParameters) (dimension : ℕ)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (value derivative : DivisionRow dimension lower)
    (weak : ∀ mode, HasWeakRadialDerivative lower positive (value mode) (derivative mode)) :
    annularSourceCoordinate parameters dimension lower angular cell 1
      (sourceGraphRealization parameters dimension lower positive bounded angular cell value derivative weak) = derivative :=
  (sourceGraph_realization_exists parameters dimension lower positive bounded angular cell value derivative weak).choose_spec.2.1

theorem sourceGraphRealization_norm_sq (parameters : PhaseParameters) (dimension : ℕ)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (value derivative : DivisionRow dimension lower)
    (weak : ∀ mode, HasWeakRadialDerivative lower positive (value mode) (derivative mode)) :
    ‖sourceGraphRealization parameters dimension lower positive bounded angular cell value derivative weak‖ ^ 2 =
      ‖value‖ ^ 2 + ‖derivative‖ ^ 2 :=
  (sourceGraph_realization_exists parameters dimension lower positive bounded angular cell value derivative weak).choose_spec.2.2

theorem sourceGraphRealization_bound (parameters : PhaseParameters) (dimension : ℕ)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (value derivative : DivisionRow dimension lower)
    (weak : ∀ mode, HasWeakRadialDerivative lower positive (value mode) (derivative mode)) :
    ‖sourceGraphRealization parameters dimension lower positive bounded angular cell value derivative weak‖ ≤
      ‖value‖ + ‖derivative‖ := by
  have equality := sourceGraphRealization_norm_sq parameters dimension lower positive bounded angular cell value derivative weak
  nlinarith only [equality, norm_nonneg value, norm_nonneg derivative,
    norm_nonneg (sourceGraphRealization parameters dimension lower positive bounded angular cell value derivative weak),
    mul_nonneg (norm_nonneg value) (norm_nonneg derivative)]

end Grad.ExhaustionSourceAllocation
