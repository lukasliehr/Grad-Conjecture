import ModuliCurveAssembly
import SmoothRepresentativeContinuityConsumer
import PhysicalSimilarityConsumer
import PhysicalSimilarityRigidity
import PhysicalNormalHessianConsumer

noncomputable section

open Set

namespace Grad.MainAssembly

open Grad.MainTarget
open Grad.MainAssembly.ModuliCurveAssembly
open Grad.MainAssembly.SmoothRepresentativeContinuity.Consumer
open Grad.MainAssembly.TargetPhysicalSimilarity
open Grad.MainAssembly.TargetPhysicalSimilarity.Consumer
open Grad.MainAssembly.PhysicalSimilarityRigidity
open Grad.MainAssembly.PhysicalNormalHessian.Consumer

/-!
This is the exact terminal packaging step for `mainTheoremStatement`.
It deliberately proves no analytic, nonlinear, geometric, or topology premise:
those arguments must be supplied by the concrete upstream construction.

The helper fixes the required quantifier order in a warning-clean Lean declaration:
all scalar data, the period threshold, and one common family are chosen before the
period, parameter, and regularity conclusions.
-/

theorem packMainWitness
    (cellLength rho delta alpha lower upper : ℝ) (firstPeriod : ℕ)
    (rhoPositive : 0 < rho) (rhoSmall : rho < 1 / 4)
    (deltaNonzero : delta ≠ 0)
    (alphaNonresonant : ∀ multiple : ℤ, alpha ≠ (Real.pi / 2) * multiple)
    (lowerPositive : 0 < lower) (intervalNontrivial : lower < upper)
    (upperSmall : upper < 1 / 2) (firstPeriodPositive : 1 ≤ firstPeriod)
    (family : ℕ → Set.Icc lower upper → Representative)
    (familyConclusions :
      ∀ period : ℕ, firstPeriod ≤ period →
        SmoothRepresentatives (Set.Icc lower upper) (family period) ∧
        (∀ parameter, PhysicalConclusions (family period parameter) cellLength period) ∧
        (∀ regularity, regularity.admissible →
          ModuliCurve regularity (Set.Icc lower upper) (family period))) :
    ∃ (rho delta alpha lower upper : ℝ) (firstPeriod : ℕ),
      0 < rho ∧ rho < 1 / 4 ∧ delta ≠ 0 ∧
      (∀ multiple : ℤ, alpha ≠ (Real.pi / 2) * multiple) ∧
      0 < lower ∧ lower < upper ∧ upper < 1 / 2 ∧ 1 ≤ firstPeriod ∧
      ∃ family : ℕ → Set.Icc lower upper → Representative,
        ∀ period : ℕ, firstPeriod ≤ period →
          SmoothRepresentatives (Set.Icc lower upper) (family period) ∧
          (∀ parameter, PhysicalConclusions (family period parameter) cellLength period) ∧
          (∀ regularity, regularity.admissible →
            ModuliCurve regularity (Set.Icc lower upper) (family period)) := by
  exact ⟨rho, delta, alpha, lower, upper, firstPeriod,
    rhoPositive, rhoSmall, deltaNonzero, alphaNonresonant,
    lowerPositive, intervalNontrivial, upperSmall, firstPeriodPositive,
    family, familyConclusions⟩

/-- Exact terminal skeleton with all already discharged target bookkeeping
removed. The only remaining quotient-separation input is the concrete physical
family's rigidity under the literal similarity comparison. Arbitrary target
reference maps disappear in `physicalSimilarity_of_related`; smooth
representatives supply configuration-curve continuity, and
`moduliCurve_of_physicalConclusions` supplies every other field. -/
theorem packMainWitnessFromCriticalData
    (cellLength rho delta alpha lower upper : ℝ) (firstPeriod : ℕ)
    (rhoPositive : 0 < rho) (rhoSmall : rho < 1 / 4)
    (deltaNonzero : delta ≠ 0)
    (alphaNonresonant : ∀ multiple : ℤ, alpha ≠ (Real.pi / 2) * multiple)
    (lowerPositive : 0 < lower) (intervalNontrivial : lower < upper)
    (upperSmall : upper < 1 / 2) (firstPeriodPositive : 1 ≤ firstPeriod)
    (family : ℕ → Set.Icc lower upper → Representative)
    (smoothAndPhysical :
      ∀ period : ℕ, firstPeriod ≤ period →
        SmoothRepresentatives (Set.Icc lower upper) (family period) ∧
        ∀ parameter,
          PhysicalConclusions (family period parameter) cellLength period)
    (similarityRigidity :
      ∀ (period : ℕ) (_periodLarge : firstPeriod ≤ period),
        ∀ first second : Set.Icc lower upper,
          PhysicalSimilarity (family period first) (family period second)
            cellLength period →
          first = second) :
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
  apply packMainWitness cellLength rho delta alpha lower upper firstPeriod
    rhoPositive rhoSmall deltaNonzero alphaNonresonant lowerPositive
    intervalNontrivial upperSmall firstPeriodPositive family
  intro period periodLarge
  refine ⟨(smoothAndPhysical period periodLarge).1,
    (smoothAndPhysical period periodLarge).2, ?_⟩
  intro regularity admissible
  exact moduliCurve_of_physicalConclusions regularity (family period)
    cellLength period (smoothAndPhysical period periodLarge).2
    (configurationCurve_of_smoothPhysical lower upper (family period)
      cellLength period (smoothAndPhysical period periodLarge).1
      (smoothAndPhysical period periodLarge).2 regularity)
    (relatedCancellation_of_similarityRigidity (family period) cellLength period
      (smoothAndPhysical period periodLarge).2
      (similarityRigidity period periodLarge) regularity)

/-- Terminal skeleton after the geometric rigidity chain has also been
discharged.  The only construction-specific inputs left are one common smooth
physical family and its exact prescribed normal-Hessian formula. -/
theorem packMainWitnessFromNormalShapeData
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
            (HarmonicRigidity.alphaAngle alpha delta parameter.val)) :
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
  exact (parameter_eq_of_physicalSimilarity
    (family period first) (family period second) cellLength period
    rho alpha delta first.val second.val axisRadiusPositive rhoPositive
    firstParameterPositive secondParameterPositive deltaNonzero alphaNotLattice
    (normalShapes period periodLarge first)
    (normalShapes period periodLarge second) similarity).symm

/-- Exact terminal skeleton with NG_R01--NG_R03 integrated.  The remaining
construction-specific inputs are one common smooth physical family and the
literal axis-chart seed data for every member. -/
theorem packMainWitnessFromAxisChartData
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
          HasAxisChartSeedData (family period parameter)
            (period * cellLength) rho alpha delta parameter.val) :
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
  apply packMainWitnessFromNormalShapeData cellLength rho delta alpha lower upper
    firstPeriod cellLengthPositive rhoPositive rhoSmall deltaNonzero
    alphaNonresonant lowerPositive intervalNontrivial upperSmall
    firstPeriodPositive family smoothAndPhysical
  intro period periodLarge parameter
  have periodPositive : 0 < period :=
    lt_of_lt_of_le (Nat.zero_lt_one.trans_le firstPeriodPositive) periodLarge
  have radiusPositive : 0 < (period : ℝ) * cellLength :=
    mul_pos (Nat.cast_pos.mpr periodPositive) cellLengthPositive
  have rhoLower : -1 < rho := lt_trans (by norm_num) rhoPositive
  have rhoUpper : rho < 1 := lt_trans rhoSmall (by norm_num)
  exact hasPrescribedNormalShape_of_axisChartSeedData
    (family period parameter) (period * cellLength) rho alpha delta parameter.val
    radiusPositive rhoLower rhoUpper (axisChartData period periodLarge parameter)

end Grad.MainAssembly
