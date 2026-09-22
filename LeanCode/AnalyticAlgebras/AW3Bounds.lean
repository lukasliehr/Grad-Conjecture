import AW3Formulas

noncomputable section

open Grad.PDEBootstrap Grad.GenericCarriers Grad.AnalyticWeights.Calculus
open scoped ContDiff BigOperators

namespace Grad.AnalyticWeights.Higher

universe valueUniverse

def commonConstant (rank : ℕ) : ℝ :=
  if rank = 0 then 1 else
    1 + (2 : ℝ) ^ rank *
      (profileConstant rank + profileConstant (rank + 1) + spectralConstant rank +
        partitionProductConstant rank + ratioNormConstant rank)

theorem commonConstant_zero : commonConstant 0 = 1 := by simp [commonConstant]

theorem commonConstant_pos (rank : ℕ) : 0 < commonConstant rank := by
  rcases rank with _ | rank
  · simp [commonConstant]
  · simp only [commonConstant, if_neg (Nat.succ_ne_zero rank)]
    have profileFirst := profileConstant_nonnegative (rank + 1)
    have profileNext := profileConstant_nonnegative (rank + 1 + 1)
    have spectral := spectralConstant_nonnegative (rank + 1)
    have partition := partitionProductConstant_nonnegative (rank + 1)
    have ratio := ratioNormConstant_nonnegative (rank + 1)
    positivity

theorem profileConstant_le_common (rank : ℕ) (positiveRank : 1 ≤ rank) :
    profileConstant rank ≤ commonConstant rank := by
  have oneLePower : 1 ≤ (2 : ℝ) ^ rank := one_le_pow₀ (by norm_num)
  have first := profileConstant_nonnegative rank
  have next := profileConstant_nonnegative (rank + 1)
  have spectral := spectralConstant_nonnegative rank
  have partition := partitionProductConstant_nonnegative rank
  have ratio := ratioNormConstant_nonnegative rank
  simp only [commonConstant, if_neg (Nat.ne_of_gt positiveRank)]
  nlinarith

theorem nextProfileConstant_le_common (rank : ℕ) (positiveRank : 1 ≤ rank) :
    profileConstant (rank + 1) ≤ commonConstant rank := by
  have oneLePower : 1 ≤ (2 : ℝ) ^ rank := one_le_pow₀ (by norm_num)
  have first := profileConstant_nonnegative rank
  have next := profileConstant_nonnegative (rank + 1)
  have spectral := spectralConstant_nonnegative rank
  have partition := partitionProductConstant_nonnegative rank
  have ratio := ratioNormConstant_nonnegative rank
  simp only [commonConstant, if_neg (Nat.ne_of_gt positiveRank)]
  nlinarith

theorem scaledProfileConstant_le_common (rank : ℕ) (positiveRank : 1 ≤ rank) :
    (2 : ℝ) ^ rank * profileConstant rank ≤ commonConstant rank := by
  have power := pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) rank
  have first := profileConstant_nonnegative rank
  have next := profileConstant_nonnegative (rank + 1)
  have spectral := spectralConstant_nonnegative rank
  have partition := partitionProductConstant_nonnegative rank
  have ratio := ratioNormConstant_nonnegative rank
  simp only [commonConstant, if_neg (Nat.ne_of_gt positiveRank)]
  nlinarith

theorem scaledSpectralConstant_le_common (rank : ℕ) (positiveRank : 1 ≤ rank) :
    (2 : ℝ) ^ rank * spectralConstant rank ≤ commonConstant rank := by
  have power := pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) rank
  have first := profileConstant_nonnegative rank
  have next := profileConstant_nonnegative (rank + 1)
  have spectral := spectralConstant_nonnegative rank
  have partition := partitionProductConstant_nonnegative rank
  have ratio := ratioNormConstant_nonnegative rank
  simp only [commonConstant, if_neg (Nat.ne_of_gt positiveRank)]
  nlinarith

theorem scaledPartitionConstant_le_common (rank : ℕ) (positiveRank : 1 ≤ rank) :
    (2 : ℝ) ^ rank * partitionProductConstant rank ≤ commonConstant rank := by
  have power := pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) rank
  have first := profileConstant_nonnegative rank
  have next := profileConstant_nonnegative (rank + 1)
  have spectral := spectralConstant_nonnegative rank
  have partition := partitionProductConstant_nonnegative rank
  have ratio := ratioNormConstant_nonnegative rank
  simp only [commonConstant, if_neg (Nat.ne_of_gt positiveRank)]
  nlinarith

theorem scaledRatioConstant_le_common (rank : ℕ) (positiveRank : 1 ≤ rank) :
    (2 : ℝ) ^ rank * ratioNormConstant rank ≤ commonConstant rank := by
  have power := pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) rank
  have first := profileConstant_nonnegative rank
  have next := profileConstant_nonnegative (rank + 1)
  have spectral := spectralConstant_nonnegative rank
  have partition := partitionProductConstant_nonnegative rank
  have ratio := ratioNormConstant_nonnegative rank
  simp only [commonConstant, if_neg (Nat.ne_of_gt positiveRank)]
  nlinarith

theorem partitionConstant_le_common (rank : ℕ) (positiveRank : 1 ≤ rank) :
    partitionProductConstant rank ≤ commonConstant rank :=
  (le_mul_of_one_le_left (partitionProductConstant_nonnegative rank)
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))).trans
      (scaledPartitionConstant_le_common rank positiveRank)

theorem ratioConstant_le_common (rank : ℕ) (positiveRank : 1 ≤ rank) :
    ratioNormConstant rank ≤ commonConstant rank :=
  (le_mul_of_one_le_left (ratioNormConstant_nonnegative rank)
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))).trans
      (scaledRatioConstant_le_common rank positiveRank)

theorem DerivativeBound.mono {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] {rank : ℕ} {function : Spatial → Value} {point : Spatial}
    {first second : ℝ} (bound : DerivativeBound rank function point first)
    (comparison : first ≤ second) : DerivativeBound rank function point second :=
  ⟨bound.1.trans comparison, bound.2.trans comparison⟩

theorem profileGoal : ProfileGoal commonConstant := by
  refine ⟨profile_contDiff, ?_⟩
  intro rank positiveRank point
  refine ⟨(profile_iterated_norm_decay rank positiveRank point).trans ?_,
    (profile_radial_iterated_norm_decay rank positiveRank point).trans ?_⟩
  · exact div_le_div_of_nonneg_right (profileConstant_le_common rank positiveRank)
      (pow_nonneg (Real.sqrt_nonneg _) _)
  · exact div_le_div_of_nonneg_right (nextProfileConstant_le_common rank positiveRank)
      (pow_nonneg (Real.sqrt_nonneg _) _)

theorem phaseGoal : PhaseGoal commonConstant := by
  intro sigma gamma scale gammaNonnegative scaleNonnegative rank positiveRank output input point
  constructor
  · apply (derivativeBound_of_norm_le rank _ point _
      (physicalPhase_iterated_norm_bound sigma gamma scale output gammaNonnegative scaleNonnegative
        rank positiveRank point)).mono
    have factorNonnegative :
        0 ≤ gamma * scale ^ rank * Grad.CellWeights.cellWeight output ^ rank :=
      mul_nonneg (mul_nonneg gammaNonnegative (pow_nonneg scaleNonnegative rank))
        (pow_nonneg (Grad.CellWeights.cellWeight_pos output).le rank)
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (scaledProfileConstant_le_common rank positiveRank)
        factorNonnegative
  · apply (derivativeBound_of_norm_le rank _ point _
      (phaseDifference_iterated_norm_bound sigma gamma scale output input gammaNonnegative scaleNonnegative
        rank positiveRank point)).mono
    have factorNonnegative :
        0 ≤ gamma * scale ^ rank * |((output - input : ℤ) : ℝ)| *
          (Grad.CellWeights.cellWeight input + |((output - input : ℤ) : ℝ)|) ^ (rank - 1) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg gammaNonnegative (pow_nonneg scaleNonnegative rank))
          (abs_nonneg _))
        (pow_nonneg (add_nonneg (Grad.CellWeights.cellWeight_pos input).le (abs_nonneg _)) _)
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (scaledSpectralConstant_le_common rank positiveRank)
        factorNonnegative

theorem exponentialGoal : ExponentialGoal commonConstant := by
  intro sigma gamma scale gammaNonnegative scaleNonnegative rank positiveRank output input point
  apply (derivativeBound_of_norm_le rank _ point _
    (weightRatio_iterated_norm_bound sigma gamma scale output input gammaNonnegative scaleNonnegative
      rank positiveRank point)).mono
  have costNonnegative : 0 ≤ weightCost rank gamma scale := by
    simp only [weightCost, if_neg (Nat.ne_of_gt positiveRank)]
    positivity
  have ratioNonnegative : 0 ≤ weightRatio sigma gamma scale output input point :=
    (ratioGoal sigma gamma scale output input point).1.le
  have allocationNonnegative : 0 ≤ allocationPolynomial rank output input := by
    unfold allocationPolynomial
    exact Finset.sum_nonneg fun displacementOrder _ =>
      mul_nonneg
        (pow_nonneg (Grad.CellWeights.cellWeight_pos (output - input)).le displacementOrder)
        (pow_nonneg (Grad.CellWeights.cellWeight_pos input).le (rank - displacementOrder))
  have factorNonnegative :
      0 ≤ weightCost rank gamma scale * weightRatio sigma gamma scale output input point *
        allocationPolynomial rank output input := by positivity
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right (scaledRatioConstant_le_common rank positiveRank)
      factorNonnegative

theorem weightGoal : WeightGoal commonConstant := by
  intro sigma gamma scale gammaNonnegative scaleNonnegative rank positiveRank cell point
  constructor
  · apply (derivativeBound_of_norm_le rank _ point _
      (physicalWeight_iterated_norm_bound sigma gamma scale cell gammaNonnegative scaleNonnegative
        rank positiveRank point)).mono
    have costNonnegative : 0 ≤ weightCost rank gamma scale := by
      simp only [weightCost, if_neg (Nat.ne_of_gt positiveRank)]
      positivity
    have weightNonnegative : 0 ≤ physicalWeight sigma gamma scale cell point := by
      rw [physicalWeight_exp]
      exact (Real.exp_pos _).le
    have factorNonnegative :
        0 ≤ weightCost rank gamma scale * physicalWeight sigma gamma scale cell point *
          Grad.CellWeights.cellWeight cell ^ rank :=
      mul_nonneg (mul_nonneg costNonnegative weightNonnegative)
        (pow_nonneg (Grad.CellWeights.cellWeight_pos cell).le rank)
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (scaledPartitionConstant_le_common rank positiveRank)
        factorNonnegative
  · apply (derivativeBound_of_norm_le rank _ point _
      (inverseWeight_iterated_norm_bound sigma gamma scale cell gammaNonnegative scaleNonnegative
        rank positiveRank point)).mono
    have costNonnegative : 0 ≤ weightCost rank gamma scale := by
      simp only [weightCost, if_neg (Nat.ne_of_gt positiveRank)]
      positivity
    have weightNonnegative : 0 ≤ inverseWeight sigma gamma scale cell point := by
      rw [inverseWeight_exp]
      exact (Real.exp_pos _).le
    have factorNonnegative :
        0 ≤ weightCost rank gamma scale * inverseWeight sigma gamma scale cell point *
          Grad.CellWeights.cellWeight cell ^ rank :=
      mul_nonneg (mul_nonneg costNonnegative weightNonnegative)
        (pow_nonneg (Grad.CellWeights.cellWeight_pos cell).le rank)
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (scaledPartitionConstant_le_common rank positiveRank)
        factorNonnegative

theorem diagonalBoundGoal : DiagonalBoundGoal commonConstant := by
  intro Value _ _ sigma gamma scale gammaNonnegative scaleNonnegative cell rank word selected
    function point
  by_cases zeroSelected : selected.card = 0
  · have inverseIdentity :=
      (Grad.AnalyticWeights.Calculus.formulaGoal sigma gamma scale cell point).2.2.2.2
    have selectedEmpty : selected = ∅ := Finset.card_eq_zero.mp zeroSelected
    subst selected
    change ‖(physicalWeight sigma gamma scale cell point *
        inverseWeight sigma gamma scale cell point) • selectedDerivative word ∅ᶜ function point‖ ≤
      commonConstant 0 * weightCost 0 gamma scale *
        ‖(Grad.CellWeights.cellWeight cell ^ 0) • selectedDerivative word ∅ᶜ function point‖
    rw [inverseIdentity]
    simp [commonConstant_zero, weightCost]
  · have positiveSelected : 1 ≤ selected.card := Nat.one_le_iff_ne_zero.mpr zeroSelected
    have weightPositive : 0 < physicalWeight sigma gamma scale cell point := by
      rw [physicalWeight_exp]
      exact Real.exp_pos _
    have inverseNonnegative : 0 ≤ inverseWeight sigma gamma scale cell point := by
      rw [inverseWeight_exp]
      exact (Real.exp_pos _).le
    have costNonnegative : 0 ≤ weightCost selected.card gamma scale := by
      simp only [weightCost, if_neg zeroSelected]
      positivity
    have cellPowerNonnegative :
        0 ≤ Grad.CellWeights.cellWeight cell ^ selected.card :=
      pow_nonneg (Grad.CellWeights.cellWeight_pos cell).le selected.card
    have selectedBound :
        ‖selectedDerivative word selected (inverseWeight sigma gamma scale cell) point‖ ≤
          partitionProductConstant selected.card * weightCost selected.card gamma scale *
            inverseWeight sigma gamma scale cell point *
              Grad.CellWeights.cellWeight cell ^ selected.card :=
      (orderedDerivative_norm_le selected.card (subword word selected)
        (inverseWeight sigma gamma scale cell) point).trans
        (inverseWeight_iterated_norm_bound sigma gamma scale cell gammaNonnegative scaleNonnegative
          selected.card positiveSelected point)
    have inverseIdentity :=
      (Grad.AnalyticWeights.Calculus.formulaGoal sigma gamma scale cell point).2.2.2.2
    have scalarBound :
        ‖physicalWeight sigma gamma scale cell point *
            selectedDerivative word selected (inverseWeight sigma gamma scale cell) point‖ ≤
          commonConstant selected.card * weightCost selected.card gamma scale *
            Grad.CellWeights.cellWeight cell ^ selected.card := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos weightPositive]
      calc
        _ ≤ physicalWeight sigma gamma scale cell point *
              (partitionProductConstant selected.card * weightCost selected.card gamma scale *
                inverseWeight sigma gamma scale cell point *
                  Grad.CellWeights.cellWeight cell ^ selected.card) :=
          mul_le_mul_of_nonneg_left selectedBound weightPositive.le
        _ = partitionProductConstant selected.card * weightCost selected.card gamma scale *
              Grad.CellWeights.cellWeight cell ^ selected.card := by
          calc
            _ = (physicalWeight sigma gamma scale cell point *
                  inverseWeight sigma gamma scale cell point) *
                (partitionProductConstant selected.card * weightCost selected.card gamma scale *
                  Grad.CellWeights.cellWeight cell ^ selected.card) := by ring
            _ = _ := by rw [inverseIdentity, one_mul]
        _ ≤ commonConstant selected.card * weightCost selected.card gamma scale *
              Grad.CellWeights.cellWeight cell ^ selected.card := by
          have factorNonnegative :
              0 ≤ weightCost selected.card gamma scale *
                Grad.CellWeights.cellWeight cell ^ selected.card :=
            mul_nonneg costNonnegative cellPowerNonnegative
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_right
              (partitionConstant_le_common selected.card positiveSelected) factorNonnegative
    rw [norm_smul, norm_smul, Real.norm_of_nonneg cellPowerNonnegative]
    have scaled := mul_le_mul_of_nonneg_right scalarBound
      (norm_nonneg (selectedDerivative word selectedᶜ function point))
    simpa only [mul_assoc] using scaled

theorem coefficientBoundGoal : CoefficientBoundGoal commonConstant := by
  intro inputDimension outputDimension sigma gamma scale gammaNonnegative scaleNonnegative output input
    phaseRank coefficientRank inputRank positivePhase phaseWord coefficientWord inputWord
    coefficient function point
  let coefficientDerivative :=
    orderedDerivative coefficientRank coefficientWord coefficient point
  let inputDerivative :=
    orderedDerivative inputRank inputWord (fun source => function source input) point
  have ratioBound :
      ‖orderedDerivative phaseRank phaseWord (weightRatio sigma gamma scale output input) point‖ ≤
        ratioNormConstant phaseRank * weightCost phaseRank gamma scale *
          weightRatio sigma gamma scale output input point *
            allocationPolynomial phaseRank output input :=
    (orderedDerivative_norm_le phaseRank phaseWord
      (weightRatio sigma gamma scale output input) point).trans
      (weightRatio_iterated_norm_bound sigma gamma scale output input gammaNonnegative scaleNonnegative
        phaseRank positivePhase point)
  have appliedBound : ‖coefficientDerivative inputDerivative‖ ≤
      ‖coefficientDerivative‖ * ‖inputDerivative‖ :=
    coefficientDerivative.le_opNorm inputDerivative
  have costNonnegative : 0 ≤ weightCost phaseRank gamma scale := by
    simp only [weightCost, if_neg (Nat.ne_of_gt positivePhase)]
    positivity
  have ratioNonnegative : 0 ≤ weightRatio sigma gamma scale output input point :=
    (ratioGoal sigma gamma scale output input point).1.le
  have allocationNonnegative : 0 ≤ allocationPolynomial phaseRank output input := by
    unfold allocationPolynomial
    exact Finset.sum_nonneg fun displacementOrder _ =>
      mul_nonneg
        (pow_nonneg (Grad.CellWeights.cellWeight_pos (output - input)).le displacementOrder)
        (pow_nonneg (Grad.CellWeights.cellWeight_pos input).le (phaseRank - displacementOrder))
  have ratioUpperNonnegative :
      0 ≤ ratioNormConstant phaseRank * weightCost phaseRank gamma scale *
        weightRatio sigma gamma scale output input point *
          allocationPolynomial phaseRank output input := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (ratioNormConstant_nonnegative phaseRank) costNonnegative)
        ratioNonnegative)
      allocationNonnegative
  have normProductBound :
      ‖orderedDerivative phaseRank phaseWord (weightRatio sigma gamma scale output input) point‖ *
          ‖coefficientDerivative inputDerivative‖ ≤
        (ratioNormConstant phaseRank * weightCost phaseRank gamma scale *
          weightRatio sigma gamma scale output input point *
            allocationPolynomial phaseRank output input) *
          (‖coefficientDerivative‖ * ‖inputDerivative‖) :=
    (mul_le_mul_of_nonneg_right ratioBound (norm_nonneg (coefficientDerivative inputDerivative))).trans
      (mul_le_mul_of_nonneg_left appliedBound ratioUpperNonnegative)
  have commonProductBound :
      (ratioNormConstant phaseRank * weightCost phaseRank gamma scale *
          weightRatio sigma gamma scale output input point *
            allocationPolynomial phaseRank output input) *
          (‖coefficientDerivative‖ * ‖inputDerivative‖) ≤
        (commonConstant phaseRank * weightCost phaseRank gamma scale *
          weightRatio sigma gamma scale output input point *
            allocationPolynomial phaseRank output input) *
          (‖coefficientDerivative‖ * ‖inputDerivative‖) := by
    have factorNonnegative :
        0 ≤ weightCost phaseRank gamma scale *
          weightRatio sigma gamma scale output input point *
            allocationPolynomial phaseRank output input *
              (‖coefficientDerivative‖ * ‖inputDerivative‖) := by positivity
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (ratioConstant_le_common phaseRank positivePhase)
        factorNonnegative
  have allocationNormIdentity :
      (∑ displacementOrder ∈ Finset.Icc 1 phaseRank,
          Grad.CellWeights.cellWeight (output - input) ^ displacementOrder *
            ‖(Grad.CellWeights.cellWeight input ^ (phaseRank - displacementOrder)) •
              inputDerivative‖) =
        allocationPolynomial phaseRank output input * ‖inputDerivative‖ := by
    unfold allocationPolynomial
    simp_rw [norm_smul, Real.norm_of_nonneg
      (pow_nonneg (Grad.CellWeights.cellWeight_pos input).le _)]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro displacementOrder _
    ring
  rw [norm_smul]
  change ‖orderedDerivative phaseRank phaseWord (weightRatio sigma gamma scale output input) point‖ *
      ‖coefficientDerivative inputDerivative‖ ≤ _
  refine normProductBound.trans (commonProductBound.trans ?_)
  rw [allocationNormIdentity]
  simp only [coefficientDerivative]
  ring_nf
  exact le_refl _

end Grad.AnalyticWeights.Higher
