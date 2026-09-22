import AKCQ10ActualForceEulerMoments

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped ContDiff BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.AnnularVariational Grad.AnnularWeightedSmoothness

/-- Literal Euler derivative of the original phase-conjugated entry. -/
def actualConjugatedEulerEntry {source target : ℕ} (parameters : PhaseParameters)
    (coefficient : ℝ → (ℤ × ℤ) → (ℤ × ℤ) →
      (ComplexEuclidean source →L[ℂ] ComplexEuclidean target))
    (rank : ℕ) (radius : ℝ) (shift input : ℤ × ℤ) :
    ComplexEuclidean source →L[ℂ] ComplexEuclidean target :=
  vectorEulerIteratedDerivative rank (fun point =>
    radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 point •
      coefficient point shift input) radius

/-- Any selector includes both the actual row and column Schur sums.
The phase is already present in the entries; it is not charged twice. -/
def actualEulerDisplacementMoment {source target : ℕ} (parameters : PhaseParameters)
    (coefficient : ℝ → (ℤ × ℤ) → (ℤ × ℤ) →
      (ComplexEuclidean source →L[ℂ] ComplexEuclidean target))
    (rank moment : ℕ) (radius : ℝ) (inputs : (ℤ × ℤ) → (ℤ × ℤ)) : ℝ :=
  ∑' (shift : ℤ × ℤ), Grad.AnnularVariational.annularFrequency shift.1 shift.2 ^ moment *
    ‖actualConjugatedEulerEntry parameters coefficient rank radius shift (inputs shift)‖

/-- Full rank allocation in the actual original-width Schur moment.
The allocated raw Euler rank is rank-index and its moment is moment+index. -/
theorem actualEulerDisplacementMoment_allocated {source target : ℕ} (parameters : PhaseParameters)
    (radius : RadialPoint) (positive : 0 < radius.val)
    (coefficient : ℝ → (ℤ × ℤ) → (ℤ × ℤ) →
      (ComplexEuclidean source →L[ℂ] ComplexEuclidean target))
    (smooth : ∀ shift input, ContDiff ℝ ∞ (fun point => coefficient point shift input))
    (kernels : ℕ → RadialKernel parameters radius source target)
    (same : ∀ rank shift input, (kernels rank).entry shift input =
      vectorEulerIteratedDerivative rank (fun point => coefficient point shift input) radius.val)
    (rank moment : ℕ) (inputs : (ℤ × ℤ) → (ℤ × ℤ)) :
    Summable (fun (shift : ℤ × ℤ) => Grad.AnnularVariational.annularFrequency shift.1 shift.2 ^ moment *
      ‖actualConjugatedEulerEntry parameters coefficient rank radius.val shift (inputs shift)‖) ∧
    actualEulerDisplacementMoment parameters coefficient rank moment radius.val inputs ≤
      ∑ index ∈ Finset.range (rank+1), (rank.choose index : ℝ) * positiveEulerRatioConstant parameters index *
        fullKernelMoment (radialKernelParameters parameters radius) (moment+index) (kernels (rank-index)) := by
  let envelope := fun index (shift : ℤ × ℤ) =>
    (rank.choose index : ℝ) * positiveEulerRatioConstant parameters index *
      (boundaryCoefficientPhaseCost (radialKernelParameters parameters radius) shift *
        Grad.AnnularVariational.annularFrequency shift.1 shift.2 ^ (moment+index) * (kernels (rank-index)).entryNorm shift)
  have envelopeSummable (index : ℕ) : Summable (envelope index) :=
    ((kernels (rank-index)).moments (moment+index)).mul_left
      ((rank.choose index : ℝ) * positiveEulerRatioConstant parameters index)
  have bounded (shift : ℤ × ℤ) : Grad.AnnularVariational.annularFrequency shift.1 shift.2 ^ moment *
      ‖actualConjugatedEulerEntry parameters coefficient rank radius.val shift (inputs shift)‖ ≤
      ∑ index ∈ Finset.range (rank+1), envelope index shift := by
    have entry := vectorEuler_phaseConjugate_norm parameters rank shift (inputs shift) radius positive
      (fun point => coefficient point shift (inputs shift)) (smooth shift (inputs shift))
    apply (mul_le_mul_of_nonneg_left entry (pow_nonneg (annularFrequency_pos shift).le moment)).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro index _
    have ratio := bulkPhase_ratio_le parameters radius shift ((twoFrequencyTranslation shift).symm (inputs shift))
    simp only [Equiv.apply_symm_apply] at ratio
    change radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm (inputs shift)).2
      (inputs shift).2 radius.val ≤ _ at ratio
    rw [← same]
    have paid := mul_le_mul ratio ((kernels (rank-index)).entry_le shift (inputs shift))
      (norm_nonneg _) (boundaryCoefficientPhaseCost_nonnegative _ _)
    have scalar0 : 0 ≤ Grad.AnnularVariational.annularFrequency shift.1 shift.2 ^ moment *
        ((rank.choose index : ℝ) * positiveEulerRatioConstant parameters index) *
          Grad.AnnularVariational.annularFrequency shift.1 shift.2 ^ index :=
      mul_nonneg (mul_nonneg (pow_nonneg (annularFrequency_pos shift).le _)
        (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (positiveEulerRatioConstant_one_le parameters index))))
        (pow_nonneg (annularFrequency_pos shift).le _)
    have multiplied := mul_le_mul_of_nonneg_left paid scalar0
    dsimp only [envelope]
    rw [pow_add]
    convert multiplied using 1 <;>
      dsimp only [Grad.SourceCollarDivision.annularFrequency,Grad.AnnularVariational.annularFrequency] <;> ring
  have totalSummable : Summable (fun (shift : ℤ × ℤ) => ∑ index ∈ Finset.range (rank+1), envelope index shift) :=
    summable_sum (fun index _ => envelopeSummable index)
  have actualSummable := Summable.of_nonneg_of_le
    (fun shift => mul_nonneg (pow_nonneg (annularFrequency_pos shift).le moment) (norm_nonneg _)) bounded totalSummable
  refine ⟨actualSummable, ?_⟩
  have summed := actualSummable.tsum_le_tsum bounded totalSummable
  apply summed.trans_eq
  rw [Summable.tsum_finsetSum (fun index _ => envelopeSummable index)]
  apply Finset.sum_congr rfl
  intro index _
  exact tsum_mul_left

end Grad.OriginalCartesianTameEstimate
