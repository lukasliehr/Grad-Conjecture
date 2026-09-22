import MainAssemblySkeleton
import SampledAxisChartData

noncomputable section

open Set

namespace Grad.MainAssembly

open Grad.MainTarget
open Grad.MainAssembly.PhysicalSimilarityRigidity
open Grad.MainAssembly.SampledPhysicalSimilarityRigidity
open Grad.MainAssembly.SampledAxisChartData

/-- Exact terminal skeleton for the integer-resampled two-harmonic normal
shape. -/
theorem packMainWitnessFromSampledNormalShapeData
    (cellLength rho delta alpha lower upper : ℝ) (firstPeriod : ℕ)
    (cellLengthPositive : 0 < cellLength)
    (rhoPositive : 0 < rho) (rhoSmall : rho < 1 / 4)
    (deltaNonzero : delta ≠ 0)
    (alphaNonresonant : ∀ multiple : ℤ,
      alpha ≠ (Real.pi / 2) * multiple)
    (lowerPositive : 0 < lower) (intervalNontrivial : lower < upper)
    (upperSmall : upper < 1 / 2) (firstPeriodPositive : 1 ≤ firstPeriod)
    (family : ℕ → Set.Icc lower upper → Representative)
    (smoothAndPhysical :
      ∀ period : ℕ, firstPeriod ≤ period →
        SmoothRepresentatives (Set.Icc lower upper) (family period) ∧
        ∀ parameter,
          PhysicalConclusions (family period parameter) cellLength period)
    (normalShapes :
      ∀ period : ℕ, firstPeriod ≤ period →
        ∀ parameter : Set.Icc lower upper,
          HasPrescribedNormalShape (family period parameter)
            (period * cellLength) rho
            (sampledAlphaAngle period alpha delta parameter.val)) :
    ∃ (rho delta alpha lower upper : ℝ) (firstPeriod : ℕ),
      0 < rho ∧ rho < 1 / 4 ∧ delta ≠ 0 ∧
      (∀ multiple : ℤ, alpha ≠ (Real.pi / 2) * multiple) ∧
      0 < lower ∧ lower < upper ∧ upper < 1 / 2 ∧ 1 ≤ firstPeriod ∧
      ∃ family : ℕ → Set.Icc lower upper → Representative,
        ∀ period : ℕ, firstPeriod ≤ period →
          SmoothRepresentatives (Set.Icc lower upper) (family period) ∧
          (∀ parameter,
            PhysicalConclusions (family period parameter) cellLength period) ∧
          (∀ regularity, regularity.admissible →
            ModuliCurve regularity (Set.Icc lower upper) (family period)) := by
  apply packMainWitnessFromCriticalData cellLength rho delta alpha lower upper
    firstPeriod rhoPositive rhoSmall deltaNonzero alphaNonresonant lowerPositive
    intervalNontrivial upperSmall firstPeriodPositive family smoothAndPhysical
  intro period periodLarge first second similarity
  have periodPositive : 0 < period :=
    lt_of_lt_of_le (Nat.zero_lt_one.trans_le firstPeriodPositive) periodLarge
  have axisRadiusPositive : 0 < (period : ℝ) * cellLength :=
    mul_pos (Nat.cast_pos.mpr periodPositive) cellLengthPositive
  have firstParameterPositive : 0 < first.val :=
    lt_of_lt_of_le lowerPositive first.property.1
  have secondParameterPositive : 0 < second.val :=
    lt_of_lt_of_le lowerPositive second.property.1
  have alphaNotLattice : ∀ integer : ℤ,
      2 * alpha ≠ (integer : ℝ) * Real.pi := by
    intro integer equality
    apply alphaNonresonant integer
    calc
      alpha = (2 * alpha) / 2 := by ring
      _ = ((integer : ℝ) * Real.pi) / 2 := by rw [equality]
      _ = (Real.pi / 2) * (integer : ℝ) := by ring
  apply Subtype.ext
  exact (parameter_eq_of_sampled_physicalSimilarity
    (family period first) (family period second) cellLength period
    rho alpha delta first.val second.val axisRadiusPositive rhoPositive
    firstParameterPositive secondParameterPositive deltaNonzero alphaNotLattice
    (normalShapes period periodLarge first)
    (normalShapes period periodLarge second) similarity).symm

/-- Exact terminal skeleton whose remaining construction input is the sampled
axis-chart package for each representative. -/
theorem packMainWitnessFromSampledAxisChartData
    (cellLength rho delta alpha lower upper : ℝ) (firstPeriod : ℕ)
    (cellLengthPositive : 0 < cellLength)
    (rhoPositive : 0 < rho) (rhoSmall : rho < 1 / 4)
    (deltaNonzero : delta ≠ 0)
    (alphaNonresonant : ∀ multiple : ℤ,
      alpha ≠ (Real.pi / 2) * multiple)
    (lowerPositive : 0 < lower) (intervalNontrivial : lower < upper)
    (upperSmall : upper < 1 / 2) (firstPeriodPositive : 1 ≤ firstPeriod)
    (family : ℕ → Set.Icc lower upper → Representative)
    (smoothAndPhysical :
      ∀ period : ℕ, firstPeriod ≤ period →
        SmoothRepresentatives (Set.Icc lower upper) (family period) ∧
        ∀ parameter,
          PhysicalConclusions (family period parameter) cellLength period)
    (axisChartData :
      ∀ period : ℕ, firstPeriod ≤ period →
        ∀ parameter : Set.Icc lower upper,
          HasSampledAxisChartSeedData (family period parameter)
            (period * cellLength) period rho alpha delta parameter.val) :
    ∃ (rho delta alpha lower upper : ℝ) (firstPeriod : ℕ),
      0 < rho ∧ rho < 1 / 4 ∧ delta ≠ 0 ∧
      (∀ multiple : ℤ, alpha ≠ (Real.pi / 2) * multiple) ∧
      0 < lower ∧ lower < upper ∧ upper < 1 / 2 ∧ 1 ≤ firstPeriod ∧
      ∃ family : ℕ → Set.Icc lower upper → Representative,
        ∀ period : ℕ, firstPeriod ≤ period →
          SmoothRepresentatives (Set.Icc lower upper) (family period) ∧
          (∀ parameter,
            PhysicalConclusions (family period parameter) cellLength period) ∧
          (∀ regularity, regularity.admissible →
            ModuliCurve regularity (Set.Icc lower upper) (family period)) := by
  apply packMainWitnessFromSampledNormalShapeData cellLength rho delta alpha
    lower upper firstPeriod cellLengthPositive rhoPositive rhoSmall
    deltaNonzero alphaNonresonant lowerPositive intervalNontrivial upperSmall
    firstPeriodPositive family smoothAndPhysical
  intro period periodLarge parameter
  have periodPositive : 0 < period :=
    lt_of_lt_of_le (Nat.zero_lt_one.trans_le firstPeriodPositive) periodLarge
  have radiusPositive : 0 < (period : ℝ) * cellLength :=
    mul_pos (Nat.cast_pos.mpr periodPositive) cellLengthPositive
  have rhoLower : -1 < rho := lt_trans (by norm_num) rhoPositive
  have rhoUpper : rho < 1 := lt_trans rhoSmall (by norm_num)
  exact hasPrescribedNormalShape_of_sampledAxisChartSeedData
    (family period parameter) (period * cellLength) period rho alpha delta
    parameter.val radiusPositive rhoLower rhoUpper
    (axisChartData period periodLarge parameter)

end Grad.MainAssembly
