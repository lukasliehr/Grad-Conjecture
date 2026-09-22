import SamplingThreshold
import SampledSmoothFamilyConsumer

noncomputable section

open Set

namespace Grad.PhysicalFamily.SampledThresholdFamily

open Grad.MainTarget
open Grad.PhysicalFamily
open Grad.PhysicalFamily.IntegerSampling
open Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SamplingThreshold

noncomputable def firstSampledPeriod (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) : ℕ :=
  Classical.choose (exists_samplingThreshold cellLength family)

theorem firstSampledPeriod_positive (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) :
    1 ≤ firstSampledPeriod cellLength family :=
  (Classical.choose_spec (exists_samplingThreshold cellLength family)).1

theorem sampledEpsilon_mem_after_firstPeriod (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (periodAfter : firstSampledPeriod cellLength family ≤ period) :
    sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero :=
  (Classical.choose_spec (exists_samplingThreshold cellLength family)).2
    period periodAfter

/-- A total period-indexed family with the exact sampled representative at
every period after the canonical threshold. -/
noncomputable def exactSampledTargetFamily (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) :
    ℕ → Set.Icc family.lower family.upper → Representative :=
  fun period => if periodAfter : firstSampledPeriod cellLength family ≤ period then
    sampledRepresentativeFamily cellLength family period
      (sampledEpsilon_mem_after_firstPeriod cellLength family period periodAfter) 0
  else
    sampledRepresentativeFamily cellLength family
      (firstSampledPeriod cellLength family)
      (sampledEpsilon_mem_after_firstPeriod cellLength family
        (firstSampledPeriod cellLength family) le_rfl) 0

theorem exactSampledTargetFamily_eq (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (periodAfter : firstSampledPeriod cellLength family ≤ period) :
    exactSampledTargetFamily cellLength family period =
      sampledRepresentativeFamily cellLength family period
        (sampledEpsilon_mem_after_firstPeriod cellLength family period
          periodAfter) 0 := by
  simp [exactSampledTargetFamily, periodAfter]

theorem exactSampledTargetFamily_smooth (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (periodAfter : firstSampledPeriod cellLength family ≤ period) :
    SmoothRepresentatives (Set.Icc family.lower family.upper)
      (exactSampledTargetFamily cellLength family period) := by
  rw [exactSampledTargetFamily_eq cellLength family period periodAfter]
  exact sampled_smoothRepresentatives cellLength family period
    (sampledEpsilon_mem_after_firstPeriod cellLength family period periodAfter) 0

/-- The exact same sampled representatives for every integer after one
threshold, packaged in the quantifier order required by the main theorem.
Only target smoothness and the literal formulas are concluded here; physical
geometry is supplied by the later G06--G31 consumer of these same maps. -/
theorem exists_exactSampledSmoothTargetFamily (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) :
    ∃ (firstPeriod : ℕ)
        (targetFamily : ℕ →
          Set.Icc family.lower family.upper → Representative),
      1 ≤ firstPeriod ∧
      ∀ period : ℕ, firstPeriod ≤ period →
        SmoothRepresentatives (Set.Icc family.lower family.upper)
            (targetFamily period) ∧
          ∀ (parameter : Set.Icc family.lower family.upper)
              (point : ClosedDisk) (time : ℝ),
            let representative := targetFamily period parameter
            representative.position (point, (time : CellCircle)) =
                sampledPositionLift cellLength family period parameter.val
                  point.val time ∧
              representative.magnetic (point, (time : CellCircle)) =
                sampledMagneticLift cellLength family period parameter.val
                  point.val time ∧
              representative.pressure (point, (time : CellCircle)) =
                sampledPressureLift 0 point.val time := by
  obtain ⟨firstPeriod, firstPositive, epsilonAfter⟩ :=
    exists_samplingThreshold cellLength family
  let targetFamily : ℕ →
      Set.Icc family.lower family.upper → Representative :=
    fun period => if periodAfter : firstPeriod ≤ period then
      sampledRepresentativeFamily cellLength family period
        (epsilonAfter period periodAfter) 0
    else
      sampledRepresentativeFamily cellLength family firstPeriod
        (epsilonAfter firstPeriod le_rfl) 0
  refine ⟨firstPeriod, targetFamily, firstPositive, ?_⟩
  intro period periodAfter
  have familyEquality : targetFamily period =
      sampledRepresentativeFamily cellLength family period
        (epsilonAfter period periodAfter) 0 := by
    simp [targetFamily, periodAfter]
  rw [familyEquality]
  exact Grad.PhysicalFamily.SampledSmoothFamily.Consumer.exactSampledSmoothFamily
    cellLength family period (epsilonAfter period periodAfter) 0

end Grad.PhysicalFamily.SampledThresholdFamily
