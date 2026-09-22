import SampledSeminormBoundsConsumer
import SampledNormalizedFactorBounds
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section

open Set Filter

namespace Grad.PhysicalFamily.SampledAllTimeBounds

open Grad.MainTarget
open Grad.PhysicalFamily
open Grad.PhysicalFamily.IntegerSampling
open Grad.PhysicalFamily.SampledSeminormBounds.Consumer
open Grad.PhysicalFamily.SampledNormalizedFactorBounds

def fundamentalTime (time : ℝ) : ℝ :=
  time - (⌊time / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)

theorem fundamentalTime_mem_Ico (time : ℝ) :
    fundamentalTime time ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
  exact ⟨Int.sub_floor_div_mul_nonneg time (mul_pos (by norm_num) Real.pi_pos),
    Int.sub_floor_div_mul_lt time (mul_pos (by norm_num) Real.pi_pos)⟩

theorem periodic_eq_fundamentalTime {Target : Type*} (mapping : ℝ → Target)
    (periodic : Function.Periodic mapping (2 * Real.pi)) (time : ℝ) :
    mapping time = mapping (fundamentalTime time) := by
  let count : ℤ := ⌊time / (2 * Real.pi)⌋
  have shifted := (periodic.int_mul count) (fundamentalTime time)
  have timeIdentity :
      fundamentalTime time + (count : ℝ) * (2 * Real.pi) = time := by
    simp [fundamentalTime, count]
  rw [timeIdentity] at shifted
  exact shifted

theorem remainder_value_norm_le_physicalBound_allTime
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ) :
    ‖family.remainder epsilon parameter.val point time‖ ≤
      family.bound * |epsilon| := by
  have periodic : Function.Periodic
      (family.remainder epsilon parameter.val point) (2 * Real.pi) :=
    family.remainderPeriodic epsilon epsilonIn parameter.val
      (parameter_mem_open cellLength family parameter) point
      (closed_disk_mem_collar cellLength family point pointIn)
  rw [periodic_eq_fundamentalTime _ periodic time]
  exact remainder_value_norm_le_physicalBound cellLength family epsilon
    epsilonIn parameter point pointIn (fundamentalTime time)
      ⟨(fundamentalTime_mem_Ico time).1,
        (fundamentalTime_mem_Ico time).2.le⟩

theorem tilt_value_norm_le_physicalBound_allTime
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) (time : ℝ) :
    ‖family.tilt epsilon parameter.val time‖ ≤
      family.bound * |epsilon| := by
  have periodic : Function.Periodic (family.tilt epsilon parameter.val)
      (2 * Real.pi) :=
    family.tiltPeriodic epsilon epsilonIn parameter.val
      (parameter_mem_open cellLength family parameter)
  rw [periodic_eq_fundamentalTime _ periodic time]
  exact tilt_value_norm_le_physicalBound cellLength family epsilon epsilonIn
    parameter (fundamentalTime time) ⟨(fundamentalTime_mem_Ico time).1,
      (fundamentalTime_mem_Ico time).2.le⟩

theorem abs_normalizedFactor_sub_one_le_physicalBound_allTime
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) (time : ℝ) :
    |normalizedFactor (family.tilt epsilon parameter.val time) - 1| ≤
      (family.bound * |epsilon|) ^ 2 / 2 := by
  have periodic : Function.Periodic (family.tilt epsilon parameter.val)
      (2 * Real.pi) :=
    family.tiltPeriodic epsilon epsilonIn parameter.val
      (parameter_mem_open cellLength family parameter)
  rw [periodic_eq_fundamentalTime _ periodic time]
  exact sampled_abs_normalizedFactor_sub_one_le cellLength family epsilon
    epsilonIn parameter (fundamentalTime time)
      ⟨(fundamentalTime_mem_Ico time).1,
        (fundamentalTime_mem_Ico time).2.le⟩

/-- Differentiating the exact periodic identity in the disk variables gives
periodicity of the ambient disk derivative, without choosing an angle-chart
representative. -/
theorem remainder_disk_fderiv_periodic
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) :
    Function.Periodic
      (fun time => fderiv ℝ
        (fun argument : Plane =>
          family.remainder epsilon parameter.val argument time) point)
      (2 * Real.pi) := by
  intro time
  have pointCollar := closed_disk_mem_collar cellLength family point pointIn
  have collarNeighborhood :
      Metric.ball (0 : Plane) family.collarRadius ∈ nhds point :=
    Metric.isOpen_ball.mem_nhds pointCollar
  have localEquality :
      (fun argument : Plane => family.remainder epsilon parameter.val argument
        (time + 2 * Real.pi)) =ᶠ[nhds point]
      (fun argument : Plane =>
        family.remainder epsilon parameter.val argument time) := by
    filter_upwards [collarNeighborhood] with argument argumentIn
    exact family.remainderPeriodic epsilon epsilonIn parameter.val
      (parameter_mem_open cellLength family parameter) argument argumentIn time
  exact localEquality.fderiv_eq

theorem remainder_disk_fderiv_eq_fundamentalTime
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ) :
    fderiv ℝ
        (fun argument : Plane =>
          family.remainder epsilon parameter.val argument time) point =
      fderiv ℝ
        (fun argument : Plane => family.remainder epsilon parameter.val
          argument (fundamentalTime time)) point := by
  exact periodic_eq_fundamentalTime _
    (remainder_disk_fderiv_periodic cellLength family epsilon epsilonIn
      parameter point pointIn) time

end Grad.PhysicalFamily.SampledAllTimeBounds
