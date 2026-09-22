import AW3Allocation

noncomputable section

open Grad.PDEBootstrap Grad.AnalyticWeights.Calculus
open scoped ContDiff BigOperators

namespace Grad.AnalyticWeights.Higher

def phaseDerivativeConstant (rank : ℕ) : ℝ :=
  max (profileConstant rank) (spectralConstant rank)

theorem phaseDerivativeConstant_nonnegative (rank : ℕ) : 0 ≤ phaseDerivativeConstant rank :=
  le_max_of_le_left (profileConstant_nonnegative rank)

theorem profileConstant_le_phaseDerivativeConstant (rank : ℕ) :
    profileConstant rank ≤ phaseDerivativeConstant rank := le_max_left _ _

theorem spectralConstant_le_phaseDerivativeConstant (rank : ℕ) :
    spectralConstant rank ≤ phaseDerivativeConstant rank := le_max_right _ _

def partitionProductConstant (rank : ℕ) : ℝ :=
  ∑ partition : OrderedFinpartition rank,
    ∏ block, phaseDerivativeConstant (partition.partSize block)

theorem partitionProductConstant_nonnegative (rank : ℕ) : 0 ≤ partitionProductConstant rank := by
  unfold partitionProductConstant
  exact Finset.sum_nonneg fun _ _ =>
    Finset.prod_nonneg fun block _ => phaseDerivativeConstant_nonnegative _

theorem exp_iteratedFDeriv (rank : ℕ) (argument : ℝ) :
    iteratedFDeriv ℝ rank Real.exp argument =
      ContinuousMultilinearMap.piFieldEquiv ℝ (Fin rank) ℝ (Real.exp argument) := by
  rw [iteratedFDeriv_eq_equiv_comp, Function.comp_apply]
  have identity := congrFun (iteratedDeriv_exp_const_mul rank 1) argument
  simpa using identity

theorem exp_comp_expansion (function : Spatial → ℝ) (smooth : ContDiff ℝ ∞ function)
    (rank : ℕ) (point : Spatial) :
    iteratedFDeriv ℝ rank (fun source => Real.exp (function source)) point =
      ∑ partition : OrderedFinpartition rank,
        partition.compAlongOrderedFinpartition
          (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin partition.length) ℝ
            (Real.exp (function point)))
          (fun block => iteratedFDeriv ℝ (partition.partSize block) function point) := by
  rw [show (fun source => Real.exp (function source)) = Real.exp ∘ function from rfl,
    iteratedFDeriv_comp Real.contDiff_exp.contDiffAt smooth.contDiffAt (by exact_mod_cast le_top)]
  simp only [FormalMultilinearSeries.taylorComp, FormalMultilinearSeries.compAlongOrderedFinpartition,
    ftaylorSeries]
  apply Finset.sum_congr rfl
  intro partition _
  rw [exp_iteratedFDeriv]

theorem partition_pred_sum {rank : ℕ} (partition : OrderedFinpartition rank) :
    ∑ block, (partition.partSize block - 1) = rank - partition.length := by
  apply Nat.cast_injective (R := ℤ)
  push_cast
  simp_rw [Nat.cast_sub (partition.partSize_pos _)]
  rw [Finset.sum_sub_distrib]
  rw [Nat.cast_sub partition.length_le]
  congr 1
  · exact_mod_cast partition_size_sum partition
  · simp

theorem gamma_partition_power_bound {rank : ℕ} (positiveRank : 1 ≤ rank)
    (gamma : ℝ) (gammaNonnegative : 0 ≤ gamma) (partition : OrderedFinpartition rank) :
    gamma ^ partition.length ≤ gamma * (1 + gamma) ^ (rank - 1) := by
  have positiveLength := partition.length_pos (by omega)
  rw [show gamma ^ partition.length = gamma * gamma ^ (partition.length - 1) by
    calc
      gamma ^ partition.length = gamma ^ (partition.length - 1 + 1) := by
        congr 1
        omega
      _ = gamma ^ (partition.length - 1) * gamma := pow_succ _ _
      _ = gamma * gamma ^ (partition.length - 1) := mul_comm _ _]
  apply mul_le_mul_of_nonneg_left _ gammaNonnegative
  calc
    gamma ^ (partition.length - 1) ≤ (1 + gamma) ^ (partition.length - 1) :=
      pow_le_pow_left₀ gammaNonnegative (by linarith) _
    _ ≤ (1 + gamma) ^ (rank - 1) :=
      pow_le_pow_right₀ (by linarith) (Nat.sub_le_sub_right partition.length_le 1)

theorem physicalPhase_partition_bound (sigma gamma scale : ℝ) (cell : ℤ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    (rank : ℕ) (_positiveRank : 1 ≤ rank) (point : Spatial)
    (partition : OrderedFinpartition rank) :
    ‖partition.compAlongOrderedFinpartition
        (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin partition.length) ℝ
          (Real.exp (physicalPhase sigma gamma scale cell point)))
        (fun block => iteratedFDeriv ℝ (partition.partSize block)
          (physicalPhase sigma gamma scale cell) point)‖ ≤
      Real.exp (physicalPhase sigma gamma scale cell point) *
        ((∏ block, phaseDerivativeConstant (partition.partSize block)) * gamma ^ partition.length *
          scale ^ rank * Grad.CellWeights.cellWeight cell ^ rank) := by
  calc
    _ ≤ ‖ContinuousMultilinearMap.piFieldEquiv ℝ (Fin partition.length) ℝ
          (Real.exp (physicalPhase sigma gamma scale cell point))‖ *
        ∏ block, ‖iteratedFDeriv ℝ (partition.partSize block)
          (physicalPhase sigma gamma scale cell) point‖ :=
      partition.norm_compAlongOrderedFinpartition_le _ _
    _ ≤ Real.exp (physicalPhase sigma gamma scale cell point) *
        ∏ block, phaseDerivativeConstant (partition.partSize block) *
          (gamma * (scale ^ partition.partSize block *
            Grad.CellWeights.cellWeight cell ^ partition.partSize block)) := by
      rw [LinearIsometryEquiv.norm_map,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun block _ => by
        apply (physicalPhase_iterated_norm_bound sigma gamma scale cell gammaNonnegative scaleNonnegative
          (partition.partSize block) (partition.partSize_pos block) point).trans
        let common := gamma * (scale ^ partition.partSize block *
          Grad.CellWeights.cellWeight cell ^ partition.partSize block)
        have commonNonnegative : 0 ≤ common := mul_nonneg gammaNonnegative
          (mul_nonneg (pow_nonneg scaleNonnegative _)
            (pow_nonneg (Grad.CellWeights.cellWeight_pos cell).le _))
        have bound : profileConstant (partition.partSize block) * common ≤
            phaseDerivativeConstant (partition.partSize block) * common :=
          mul_le_mul_of_nonneg_right (profileConstant_le_phaseDerivativeConstant _) commonNonnegative
        simpa only [common, mul_assoc] using bound)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
        partition_size_sum]
      ring

theorem physicalWeight_iterated_norm_bound (sigma gamma scale : ℝ) (cell : ℤ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    (rank : ℕ) (positiveRank : 1 ≤ rank) (point : Spatial) :
    ‖iteratedFDeriv ℝ rank (physicalWeight sigma gamma scale cell) point‖ ≤
      partitionProductConstant rank * weightCost rank gamma scale *
        physicalWeight sigma gamma scale cell point * Grad.CellWeights.cellWeight cell ^ rank := by
  rw [show physicalWeight sigma gamma scale cell =
      fun source => Real.exp (physicalPhase sigma gamma scale cell source) from
    funext (physicalWeight_exp sigma gamma scale cell)]
  rw [exp_comp_expansion _ (physicalPhase_contDiff sigma gamma scale cell) rank point]
  calc
    _ ≤ ∑ partition : OrderedFinpartition rank, _ := norm_sum_le _ _
    _ ≤ ∑ partition : OrderedFinpartition rank,
        Real.exp (physicalPhase sigma gamma scale cell point) *
          ((∏ block, phaseDerivativeConstant (partition.partSize block)) *
            (gamma * (1 + gamma) ^ (rank - 1)) * scale ^ rank *
              Grad.CellWeights.cellWeight cell ^ rank) :=
      Finset.sum_le_sum (fun partition _ =>
        (physicalPhase_partition_bound sigma gamma scale cell gammaNonnegative scaleNonnegative
          rank positiveRank point partition).trans (by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
            apply mul_le_mul_of_nonneg_right _
              (pow_nonneg (Grad.CellWeights.cellWeight_pos cell).le _)
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg scaleNonnegative _)
            exact mul_le_mul_of_nonneg_left
              (gamma_partition_power_bound positiveRank gamma gammaNonnegative partition)
              (Finset.prod_nonneg fun block _ => phaseDerivativeConstant_nonnegative _)))
    _ = _ := by
      simp only [weightCost, if_neg (Nat.ne_of_gt positiveRank), partitionProductConstant]
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro partition _
      ring

theorem neg_physicalPhase_iterated_norm_bound (sigma gamma scale : ℝ) (cell : ℤ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    (rank : ℕ) (positiveRank : 1 ≤ rank) (point : Spatial) :
    ‖iteratedFDeriv ℝ rank (-physicalPhase sigma gamma scale cell) point‖ ≤
      profileConstant rank * gamma * scale ^ rank * Grad.CellWeights.cellWeight cell ^ rank := by
  rw [iteratedFDeriv_neg_apply, norm_neg]
  exact physicalPhase_iterated_norm_bound sigma gamma scale cell gammaNonnegative scaleNonnegative
    rank positiveRank point

theorem neg_physicalPhase_partition_bound (sigma gamma scale : ℝ) (cell : ℤ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    (rank : ℕ) (_positiveRank : 1 ≤ rank) (point : Spatial)
    (partition : OrderedFinpartition rank) :
    ‖partition.compAlongOrderedFinpartition
        (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin partition.length) ℝ
          (Real.exp (-physicalPhase sigma gamma scale cell point)))
        (fun block => iteratedFDeriv ℝ (partition.partSize block)
          (-physicalPhase sigma gamma scale cell) point)‖ ≤
      Real.exp (-physicalPhase sigma gamma scale cell point) *
        ((∏ block, phaseDerivativeConstant (partition.partSize block)) * gamma ^ partition.length *
          scale ^ rank * Grad.CellWeights.cellWeight cell ^ rank) := by
  calc
    _ ≤ ‖ContinuousMultilinearMap.piFieldEquiv ℝ (Fin partition.length) ℝ
          (Real.exp (-physicalPhase sigma gamma scale cell point))‖ *
        ∏ block, ‖iteratedFDeriv ℝ (partition.partSize block)
          (-physicalPhase sigma gamma scale cell) point‖ :=
      partition.norm_compAlongOrderedFinpartition_le _ _
    _ ≤ Real.exp (-physicalPhase sigma gamma scale cell point) *
        ∏ block, phaseDerivativeConstant (partition.partSize block) *
          (gamma * (scale ^ partition.partSize block *
            Grad.CellWeights.cellWeight cell ^ partition.partSize block)) := by
      rw [LinearIsometryEquiv.norm_map,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun block _ => by
        apply (neg_physicalPhase_iterated_norm_bound sigma gamma scale cell gammaNonnegative scaleNonnegative
          (partition.partSize block) (partition.partSize_pos block) point).trans
        let common := gamma * (scale ^ partition.partSize block *
          Grad.CellWeights.cellWeight cell ^ partition.partSize block)
        have commonNonnegative : 0 ≤ common := mul_nonneg gammaNonnegative
          (mul_nonneg (pow_nonneg scaleNonnegative _)
            (pow_nonneg (Grad.CellWeights.cellWeight_pos cell).le _))
        have bound : profileConstant (partition.partSize block) * common ≤
            phaseDerivativeConstant (partition.partSize block) * common :=
          mul_le_mul_of_nonneg_right (profileConstant_le_phaseDerivativeConstant _) commonNonnegative
        simpa only [common, mul_assoc] using bound)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
        partition_size_sum]
      ring

theorem inverseWeight_iterated_norm_bound (sigma gamma scale : ℝ) (cell : ℤ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    (rank : ℕ) (positiveRank : 1 ≤ rank) (point : Spatial) :
    ‖iteratedFDeriv ℝ rank (inverseWeight sigma gamma scale cell) point‖ ≤
      partitionProductConstant rank * weightCost rank gamma scale *
        inverseWeight sigma gamma scale cell point * Grad.CellWeights.cellWeight cell ^ rank := by
  rw [show inverseWeight sigma gamma scale cell =
      fun source => Real.exp (-physicalPhase sigma gamma scale cell source) from
    funext (inverseWeight_exp sigma gamma scale cell)]
  have negativeSmooth : ContDiff ℝ ∞ (-physicalPhase sigma gamma scale cell) :=
    (physicalPhase_contDiff sigma gamma scale cell).neg
  change ‖iteratedFDeriv ℝ rank
      (fun source => Real.exp ((-physicalPhase sigma gamma scale cell) source)) point‖ ≤
    partitionProductConstant rank * weightCost rank gamma scale *
      Real.exp ((-physicalPhase sigma gamma scale cell) point) *
        Grad.CellWeights.cellWeight cell ^ rank
  rw [exp_comp_expansion _ negativeSmooth rank point]
  calc
    _ ≤ ∑ partition : OrderedFinpartition rank, _ := norm_sum_le _ _
    _ ≤ ∑ partition : OrderedFinpartition rank,
        Real.exp (-physicalPhase sigma gamma scale cell point) *
          ((∏ block, phaseDerivativeConstant (partition.partSize block)) *
            (gamma * (1 + gamma) ^ (rank - 1)) * scale ^ rank *
              Grad.CellWeights.cellWeight cell ^ rank) :=
      Finset.sum_le_sum (fun partition _ =>
        (neg_physicalPhase_partition_bound sigma gamma scale cell gammaNonnegative scaleNonnegative
          rank positiveRank point partition).trans (by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
            apply mul_le_mul_of_nonneg_right _
              (pow_nonneg (Grad.CellWeights.cellWeight_pos cell).le _)
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg scaleNonnegative _)
            exact mul_le_mul_of_nonneg_left
              (gamma_partition_power_bound positiveRank gamma gammaNonnegative partition)
              (Finset.prod_nonneg fun block _ => phaseDerivativeConstant_nonnegative _)))
    _ = _ := by
      simp only [weightCost, if_neg (Nat.ne_of_gt positiveRank), partitionProductConstant]
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro partition _
      simp only [Pi.neg_apply]
      ring

def displacementExpansionConstant (rank : ℕ) : ℝ :=
  (rank + 1 : ℕ) * (rank : ℝ) ^ rank

theorem displacementExpansionConstant_nonnegative (rank : ℕ) :
    0 ≤ displacementExpansionConstant rank := by
  unfold displacementExpansionConstant
  positivity

theorem allocation_term_le (rank displacementOrder : ℕ) (output input : ℤ)
    (membership : displacementOrder ∈ Finset.Icc 1 rank) :
    Grad.CellWeights.cellWeight (output - input) ^ displacementOrder *
        Grad.CellWeights.cellWeight input ^ (rank - displacementOrder) ≤
      allocationPolynomial rank output input := by
  unfold allocationPolynomial
  exact Finset.single_le_sum
    (s := Finset.Icc 1 rank)
    (f := fun order => Grad.CellWeights.cellWeight (output - input) ^ order *
      Grad.CellWeights.cellWeight input ^ (rank - order))
    (fun order _ => mul_nonneg
      (pow_nonneg (Grad.CellWeights.cellWeight_pos (output - input)).le _)
      (pow_nonneg (Grad.CellWeights.cellWeight_pos input).le _)) membership

theorem choose_cast_le_rank_power (rank blocks index : ℕ) (positiveRank : 1 ≤ rank)
    (indexBound : index ≤ rank - blocks) :
    ((rank - blocks).choose index : ℝ) ≤ (rank : ℝ) ^ rank := by
  have naturalBound : (rank - blocks).choose index ≤ rank ^ rank :=
    (Nat.choose_le_pow _ _).trans
      ((pow_le_pow_left₀ (Nat.zero_le _) (Nat.sub_le rank blocks) index).trans
        (pow_le_pow_right₀ positiveRank (indexBound.trans (Nat.sub_le rank blocks))))
  exact_mod_cast naturalBound

theorem displacement_binomial_bound (rank blocks : ℕ) (positiveRank : 1 ≤ rank)
    (positiveBlocks : 1 ≤ blocks) (blocksBound : blocks ≤ rank) (output input : ℤ) :
    |((output - input : ℤ) : ℝ)| ^ blocks *
        (Grad.CellWeights.cellWeight input + |((output - input : ℤ) : ℝ)|) ^ (rank - blocks) ≤
      displacementExpansionConstant rank * allocationPolynomial rank output input := by
  let delta := |((output - input : ℤ) : ℝ)|
  let inputWeight := Grad.CellWeights.cellWeight input
  let displacementWeight := Grad.CellWeights.cellWeight (output - input)
  have deltaNonnegative : 0 ≤ delta := abs_nonneg _
  have inputNonnegative : 0 ≤ inputWeight := (Grad.CellWeights.cellWeight_pos input).le
  have displacementNonnegative : 0 ≤ displacementWeight :=
    (Grad.CellWeights.cellWeight_pos (output - input)).le
  have deltaBound : delta ≤ displacementWeight := by
    exact Grad.AnalyticWeights.cellWeight_bounds (output - input) |>.1
  rw [show inputWeight + delta = delta + inputWeight by ring, add_pow, Finset.mul_sum]
  calc
    _ ≤ ∑ index ∈ Finset.range (rank - blocks + 1),
        (rank : ℝ) ^ rank * allocationPolynomial rank output input := by
      apply Finset.sum_le_sum
      intro index membership
      have indexBound : index ≤ rank - blocks := by
        have := Finset.mem_range.mp membership
        omega
      have totalBound : blocks + index ≤ rank := by omega
      have totalPositive : 1 ≤ blocks + index := by omega
      have remaining : rank - blocks - index = rank - (blocks + index) := by omega
      have allocationMembership : blocks + index ∈ Finset.Icc 1 rank := by
        simp only [Finset.mem_Icc]
        exact ⟨totalPositive, totalBound⟩
      have powerBound : delta ^ (blocks + index) ≤ displacementWeight ^ (blocks + index) :=
        pow_le_pow_left₀ deltaNonnegative deltaBound _
      have allocationBound := allocation_term_le rank (blocks + index) output input allocationMembership
      calc
        delta ^ blocks * (delta ^ index * inputWeight ^ (rank - blocks - index) *
            ((rank - blocks).choose index : ℝ)) =
            ((rank - blocks).choose index : ℝ) *
            (delta ^ (blocks + index) * inputWeight ^ (rank - (blocks + index))) := by
              rw [pow_add, remaining]
              ring
        _ ≤ (rank : ℝ) ^ rank *
            (displacementWeight ^ (blocks + index) * inputWeight ^ (rank - (blocks + index))) := by
              apply mul_le_mul
              · exact choose_cast_le_rank_power rank blocks index positiveRank indexBound
              · exact mul_le_mul_of_nonneg_right powerBound (pow_nonneg inputNonnegative _)
              · positivity
              · positivity
        _ ≤ (rank : ℝ) ^ rank * allocationPolynomial rank output input :=
          mul_le_mul_of_nonneg_left allocationBound (by positivity)
    _ = ((rank - blocks + 1 : ℕ) : ℝ) *
        ((rank : ℝ) ^ rank * allocationPolynomial rank output input) := by simp
    _ ≤ ((rank + 1 : ℕ) : ℝ) *
        ((rank : ℝ) ^ rank * allocationPolynomial rank output input) := by
      apply mul_le_mul_of_nonneg_right _
        (mul_nonneg (by positivity) (by unfold allocationPolynomial; positivity))
      exact_mod_cast Nat.add_le_add_right (Nat.sub_le rank blocks) 1
    _ = displacementExpansionConstant rank * allocationPolynomial rank output input := by
      unfold displacementExpansionConstant
      push_cast
      ring

theorem phaseDifference_partition_bound (sigma gamma scale : ℝ) (output input : ℤ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    (rank : ℕ) (_positiveRank : 1 ≤ rank) (point : Spatial)
    (partition : OrderedFinpartition rank) :
    ‖partition.compAlongOrderedFinpartition
        (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin partition.length) ℝ
          (Real.exp (phaseDifference sigma gamma scale output input point)))
        (fun block => iteratedFDeriv ℝ (partition.partSize block)
          (phaseDifference sigma gamma scale output input) point)‖ ≤
      Real.exp (phaseDifference sigma gamma scale output input point) *
        ((∏ block, phaseDerivativeConstant (partition.partSize block)) * gamma ^ partition.length *
          scale ^ rank * |((output - input : ℤ) : ℝ)| ^ partition.length *
            (Grad.CellWeights.cellWeight input + |((output - input : ℤ) : ℝ)|) ^
              (rank - partition.length)) := by
  let delta := |((output - input : ℤ) : ℝ)|
  let base := Grad.CellWeights.cellWeight input + delta
  have baseNonnegative : 0 ≤ base :=
    add_nonneg (Grad.CellWeights.cellWeight_pos input).le (abs_nonneg _)
  calc
    _ ≤ ‖ContinuousMultilinearMap.piFieldEquiv ℝ (Fin partition.length) ℝ
          (Real.exp (phaseDifference sigma gamma scale output input point))‖ *
        ∏ block, ‖iteratedFDeriv ℝ (partition.partSize block)
          (phaseDifference sigma gamma scale output input) point‖ :=
      partition.norm_compAlongOrderedFinpartition_le _ _
    _ ≤ Real.exp (phaseDifference sigma gamma scale output input point) *
        ∏ block, phaseDerivativeConstant (partition.partSize block) *
          (gamma * (scale ^ partition.partSize block *
            (delta * base ^ (partition.partSize block - 1)))) := by
      rw [LinearIsometryEquiv.norm_map,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun block _ => by
        apply (phaseDifference_iterated_norm_bound sigma gamma scale output input gammaNonnegative
          scaleNonnegative (partition.partSize block) (partition.partSize_pos block) point).trans
        let common := gamma * (scale ^ partition.partSize block *
          (delta * base ^ (partition.partSize block - 1)))
        have commonNonnegative : 0 ≤ common := mul_nonneg gammaNonnegative
          (mul_nonneg (pow_nonneg scaleNonnegative _)
            (mul_nonneg (abs_nonneg _) (pow_nonneg baseNonnegative _)))
        have bound : spectralConstant (partition.partSize block) * common ≤
            phaseDerivativeConstant (partition.partSize block) * common :=
          mul_le_mul_of_nonneg_right (spectralConstant_le_phaseDerivativeConstant _) commonNonnegative
        simpa only [common, delta, base, mul_assoc] using bound)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, Finset.prod_pow_eq_pow_sum,
        partition_size_sum, partition_pred_sum]
      simp only [delta, base]
      ring

def ratioNormConstant (rank : ℕ) : ℝ :=
  partitionProductConstant rank * displacementExpansionConstant rank

theorem ratioNormConstant_nonnegative (rank : ℕ) : 0 ≤ ratioNormConstant rank :=
  mul_nonneg (partitionProductConstant_nonnegative rank)
    (displacementExpansionConstant_nonnegative rank)

theorem weightRatio_iterated_norm_bound (sigma gamma scale : ℝ) (output input : ℤ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    (rank : ℕ) (positiveRank : 1 ≤ rank) (point : Spatial) :
    ‖iteratedFDeriv ℝ rank (weightRatio sigma gamma scale output input) point‖ ≤
      ratioNormConstant rank * weightCost rank gamma scale *
        weightRatio sigma gamma scale output input point * allocationPolynomial rank output input := by
  rw [show weightRatio sigma gamma scale output input =
      fun source => Real.exp (phaseDifference sigma gamma scale output input source) from
    funext (fun point => by
      rw [weightRatio, physicalWeight_exp, inverseWeight_exp, ← Real.exp_add]
      rfl)]
  have differenceSmooth : ContDiff ℝ ∞ (phaseDifference sigma gamma scale output input) :=
    (physicalPhase_contDiff sigma gamma scale output).sub
      (physicalPhase_contDiff sigma gamma scale input)
  rw [exp_comp_expansion _ differenceSmooth rank point]
  calc
    _ ≤ ∑ partition : OrderedFinpartition rank, _ := norm_sum_le _ _
    _ ≤ ∑ partition : OrderedFinpartition rank,
        Real.exp (phaseDifference sigma gamma scale output input point) *
          ((∏ block, phaseDerivativeConstant (partition.partSize block)) *
            (gamma * (1 + gamma) ^ (rank - 1)) * scale ^ rank *
              displacementExpansionConstant rank * allocationPolynomial rank output input) :=
      Finset.sum_le_sum (fun partition _ =>
        (phaseDifference_partition_bound sigma gamma scale output input gammaNonnegative scaleNonnegative
          rank positiveRank point partition).trans (by
            have gammaBound := gamma_partition_power_bound positiveRank gamma gammaNonnegative partition
            have displacementBound := displacement_binomial_bound rank partition.length positiveRank
              (partition.length_pos (by omega)) partition.length_le output input
            have constantNonnegative :
                0 ≤ ∏ block, phaseDerivativeConstant (partition.partSize block) :=
              Finset.prod_nonneg
                (fun block _ => phaseDerivativeConstant_nonnegative (partition.partSize block))
            have scalePowerNonnegative := pow_nonneg scaleNonnegative rank
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
            calc
              _ ≤ (∏ block, phaseDerivativeConstant (partition.partSize block)) *
                  (gamma * (1 + gamma) ^ (rank - 1)) * scale ^ rank *
                    (|((output - input : ℤ) : ℝ)| ^ partition.length *
                      (Grad.CellWeights.cellWeight input + |((output - input : ℤ) : ℝ)|) ^
                        (rank - partition.length)) := by
                    have gammaScaled :
                        (∏ block, phaseDerivativeConstant (partition.partSize block)) *
                            gamma ^ partition.length * scale ^ rank ≤
                          (∏ block, phaseDerivativeConstant (partition.partSize block)) *
                            (gamma * (1 + gamma) ^ (rank - 1)) * scale ^ rank :=
                      mul_le_mul_of_nonneg_right
                        (mul_le_mul_of_nonneg_left gammaBound constantNonnegative)
                        scalePowerNonnegative
                    have displacementNonnegative : 0 ≤
                        |((output - input : ℤ) : ℝ)| ^ partition.length *
                          (Grad.CellWeights.cellWeight input + |((output - input : ℤ) : ℝ)|) ^
                            (rank - partition.length) :=
                      mul_nonneg (pow_nonneg (abs_nonneg _) _)
                        (pow_nonneg (add_nonneg (Grad.CellWeights.cellWeight_pos input).le
                          (abs_nonneg _)) _)
                    simpa only [mul_assoc] using
                      mul_le_mul_of_nonneg_right gammaScaled displacementNonnegative
              _ ≤ (∏ block, phaseDerivativeConstant (partition.partSize block)) *
                  (gamma * (1 + gamma) ^ (rank - 1)) * scale ^ rank *
                    (displacementExpansionConstant rank * allocationPolynomial rank output input) :=
                  mul_le_mul_of_nonneg_left displacementBound
                    (mul_nonneg
                      (mul_nonneg constantNonnegative
                        (mul_nonneg gammaNonnegative (pow_nonneg (by linarith) _)))
                      scalePowerNonnegative)
              _ = _ := by ring))
    _ = _ := by
      simp only [weightCost, if_neg (Nat.ne_of_gt positiveRank), ratioNormConstant,
        partitionProductConstant]
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro partition _
      ring

end Grad.AnalyticWeights.Higher
