import BKB16NeumannMajorants

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal NNReal

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

def fullKernelNeumannTailEntry {dimension : ℕ}
    {parameters : PhaseParameters}
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (total input : ℤ × ℤ) :
    ComplexEuclidean dimension →L[ℂ] ComplexEuclidean dimension :=
  ∑' exponent : ℕ, (fullKernelPower kernel exponent).entry total input

def fullKernelNeumannTailMajorant {dimension : ℕ}
    {parameters : PhaseParameters}
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (total : ℤ × ℤ) : ℝ :=
  ∑' exponent : ℕ, (fullKernelPower kernel exponent).entryNorm total

theorem fullKernelNeumannTailEntry_norm_le {dimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) (total input : ℤ × ℤ) :
    ‖fullKernelNeumannTailEntry kernel total input‖ ≤
      fullKernelNeumannTailMajorant kernel total := by
  unfold fullKernelNeumannTailEntry fullKernelNeumannTailMajorant
  have entries := fullKernelPower_entry_summable parameters kernel low
    lowBound lowSmall total input
  have norms := fullKernelPower_entryNorm_summable parameters kernel low
    lowBound lowSmall total
  exact (norm_tsum_le_tsum_norm entries.norm).trans
    (entries.norm.tsum_le_tsum
      (fun exponent => (fullKernelPower kernel exponent).entry_le total input) norms)

private theorem bkb17SummableOfEnn {indexType : Type*} {f : indexType → ℝ}
    (nonnegative : ∀ index, 0 ≤ f index)
    (finite : (∑' index, ENNReal.ofReal (f index)) ≠ ⊤) : Summable f := by
  have coeForm : (fun index =>
      ((Real.toNNReal (f index) : ℝ≥0) : ℝ≥0∞)) =
      fun index => ENNReal.ofReal (f index) := rfl
  have nnSummable : Summable (fun index => Real.toNNReal (f index)) := by
    apply ENNReal.tsum_coe_ne_top_iff_summable.mp
    rw [coeForm]
    exact finite
  have realSummable : Summable
      (fun index => ((Real.toNNReal (f index) : ℝ≥0) : ℝ)) :=
    NNReal.summable_coe.mpr nnSummable
  apply realSummable.congr
  intro index
  exact Real.coe_toNNReal (f index) (nonnegative index)

theorem fullKernelNeumannTailMajorant_moment {dimension : ℕ}
    (parameters : PhaseParameters) (moment : ℕ)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) :
    Summable (fun total : ℤ × ℤ =>
      boundaryCoefficientPhaseCost parameters total *
        annularFrequency total.1 total.2 ^ moment *
          fullKernelNeumannTailMajorant kernel total) ∧
    (∑' total : ℤ × ℤ,
      boundaryCoefficientPhaseCost parameters total *
        annularFrequency total.1 total.2 ^ moment *
          fullKernelNeumannTailMajorant kernel total) ≤
      fullKernelNeumannConstant moment low *
        fullKernelMoment parameters moment kernel := by
  let weightedMajorant : ℤ × ℤ → ℝ := fun total =>
    boundaryCoefficientPhaseCost parameters total *
      annularFrequency total.1 total.2 ^ moment *
        fullKernelNeumannTailMajorant kernel total
  have weightedNonnegative : ∀ total, 0 ≤ weightedMajorant total := by
    intro total
    unfold weightedMajorant fullKernelNeumannTailMajorant
    exact mul_nonneg
      (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters total)
        (pow_nonneg (annularFrequency_pos total).le moment))
      (tsum_nonneg fun exponent =>
        fullKernelEntryNorm_nonnegative (fullKernelPower kernel exponent) total)
  have lowNonnegative :=
    (fullKernelMoment_nonnegative parameters 0 kernel).trans lowBound
  have scalarSummable : Summable (fun exponent : ℕ =>
      ((exponent : ℝ) + 1) ^ (moment + 1) * low ^ exponent *
        fullKernelMoment parameters moment kernel) :=
    (fullKernelNeumannMajorant_summable moment low lowNonnegative lowSmall).mul_right _
  have scalarNonnegative : ∀ exponent : ℕ,
      0 ≤ ((exponent : ℝ) + 1) ^ (moment + 1) * low ^ exponent *
        fullKernelMoment parameters moment kernel := by
    intro exponent
    exact mul_nonneg
      (mul_nonneg (pow_nonneg (by positivity) (moment + 1))
        (pow_nonneg lowNonnegative exponent))
      (fullKernelMoment_nonnegative parameters moment kernel)
  have ennBound : (∑' total : ℤ × ℤ,
      ENNReal.ofReal (weightedMajorant total)) ≤
      ENNReal.ofReal (fullKernelNeumannConstant moment low *
        fullKernelMoment parameters moment kernel) := by
    calc
      (∑' total : ℤ × ℤ,
          ENNReal.ofReal (weightedMajorant total)) =
          ∑' total : ℤ × ℤ,
            ennFullKernelWeight parameters moment total *
              ∑' exponent : ℕ,
                ENNReal.ofReal
                  ((fullKernelPower kernel exponent).entryNorm total) := by
        apply tsum_congr
        intro total
        unfold weightedMajorant fullKernelNeumannTailMajorant
        rw [ENNReal.ofReal_mul
          (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters total)
            (pow_nonneg (annularFrequency_pos total).le moment)),
          ENNReal.ofReal_tsum_of_nonneg
            (fun exponent => fullKernelEntryNorm_nonnegative
              (fullKernelPower kernel exponent) total)
            (fullKernelPower_entryNorm_summable parameters kernel low
              lowBound lowSmall total)]
        rfl
      _ = ∑' total : ℤ × ℤ, ∑' exponent : ℕ,
            ennFullKernelWeight parameters moment total *
              ENNReal.ofReal
                ((fullKernelPower kernel exponent).entryNorm total) := by
        apply tsum_congr
        intro total
        rw [ENNReal.tsum_mul_left]
      _ = ∑' exponent : ℕ, ∑' total : ℤ × ℤ,
            ennFullKernelWeight parameters moment total *
              ENNReal.ofReal
                ((fullKernelPower kernel exponent).entryNorm total) :=
        ENNReal.tsum_comm
      _ = ∑' exponent : ℕ,
            ENNReal.ofReal
              (fullKernelMoment parameters moment
                (fullKernelPower kernel exponent)) := by
        apply tsum_congr
        intro exponent
        exact ennFullKernelMoment_eq parameters moment
          (fullKernelPower kernel exponent)
      _ ≤ ∑' exponent : ℕ,
            ENNReal.ofReal
              (((exponent : ℝ) + 1) ^ (moment + 1) * low ^ exponent *
                fullKernelMoment parameters moment kernel) := by
        apply ENNReal.tsum_le_tsum
        intro exponent
        exact ENNReal.ofReal_le_ofReal
          (fullKernelPower_theta_moment_le parameters moment exponent kernel low lowBound)
      _ = ENNReal.ofReal (∑' exponent : ℕ,
            ((exponent : ℝ) + 1) ^ (moment + 1) * low ^ exponent *
              fullKernelMoment parameters moment kernel) :=
        (ENNReal.ofReal_tsum_of_nonneg scalarNonnegative scalarSummable).symm
      _ = ENNReal.ofReal (fullKernelNeumannConstant moment low *
            fullKernelMoment parameters moment kernel) := by
        apply congrArg
        unfold fullKernelNeumannConstant
        rw [tsum_mul_right]
  have finite : (∑' total : ℤ × ℤ,
      ENNReal.ofReal (weightedMajorant total)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ennBound
  have summable := bkb17SummableOfEnn weightedNonnegative finite
  refine ⟨summable, ?_⟩
  have encoded := ENNReal.ofReal_tsum_of_nonneg weightedNonnegative summable
  have transported :
      ENNReal.ofReal (∑' total, weightedMajorant total) ≤
        ENNReal.ofReal (fullKernelNeumannConstant moment low *
          fullKernelMoment parameters moment kernel) := by
    rw [encoded]
    exact ennBound
  have rightNonnegative :
      0 ≤ fullKernelNeumannConstant moment low *
        fullKernelMoment parameters moment kernel := by
    apply mul_nonneg
    · exact tsum_nonneg (fun exponent => by positivity)
    · exact fullKernelMoment_nonnegative parameters moment kernel
  simpa only [weightedMajorant] using
    (ENNReal.ofReal_le_ofReal_iff rightNonnegative).mp transported

/-- The absolutely convergent tail `K + K² + ...`, retained as an exact
full two-frequency kernel with literal input-mode supremum. -/
def fullKernelNeumannTail {dimension : ℕ} (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) :
    FullTwoFrequencyKernel parameters dimension dimension :=
  fullKernelOfEntries parameters
    (fullKernelNeumannTailEntry kernel)
    (fullKernelNeumannTailMajorant kernel)
    (fullKernelNeumannTailEntry_norm_le parameters kernel low lowBound lowSmall)
    (fun moment =>
      (fullKernelNeumannTailMajorant_moment parameters moment kernel low
        lowBound lowSmall).1)

@[simp] theorem fullKernelNeumannTail_entry {dimension : ℕ}
    (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) (total input : ℤ × ℤ) :
    (fullKernelNeumannTail parameters kernel low lowBound lowSmall).entry total input =
      ∑' exponent : ℕ,
        (fullKernelPower kernel exponent).entry total input := rfl

theorem fullKernelNeumannTail_moment_le {dimension : ℕ}
    (parameters : PhaseParameters) (moment : ℕ)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low)
    (lowSmall : low < 1) :
    fullKernelMoment parameters moment
        (fullKernelNeumannTail parameters kernel low lowBound lowSmall) ≤
      fullKernelNeumannConstant moment low *
        fullKernelMoment parameters moment kernel := by
  unfold fullKernelMoment
  have majorantMoment := fullKernelNeumannTailMajorant_moment
    parameters moment kernel low lowBound lowSmall
  exact (((fullKernelNeumannTail parameters kernel low lowBound lowSmall).moments
      moment).tsum_le_tsum
        (fun total => mul_le_mul_of_nonneg_left
          (fullKernelOfEntries_entryNorm_le parameters _ _ _ _ total)
          (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters total)
            (pow_nonneg (annularFrequency_pos total).le moment)))
        majorantMoment.1).trans majorantMoment.2

end Grad.BoundaryKernelAction
