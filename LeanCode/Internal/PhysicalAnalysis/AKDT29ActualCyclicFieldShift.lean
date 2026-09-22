import AKDT28FiniteRotationIndex

noncomputable section
open Set

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily

/-- The literal ambient rotations compose with the exact target convention. -/
theorem physical_rotation_add (first second : ℝ) (point : Vec) :
    rotation (first + second) point = rotation first (rotation second point) := by
  ext coordinate
  fin_cases coordinate <;> simp [rotation, vector, Real.cos_add, Real.sin_add] <;> ring

variable (length : ℝ) (family : CellSolutionFamily length) (period : ℕ)
  (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
  (potential : ℝ) (parameter : Icc family.lower family.upper)

theorem actual_reference_lift_values (point : ClosedDisk) (time : ℝ) :
    let configuration := sampledRepresentativeFamily length family period epsilonIn potential parameter
    configuration.position (referenceCover (point, time)) = sampledPositionLift length family period parameter.val point.val time ∧
    configuration.magnetic (referenceCover (point, time)) = sampledMagneticLift length family period parameter.val point.val time ∧
    configuration.pressure (referenceCover (point, time)) = sampledPressureLift potential point.val time := by
  have identity : sampledRepresentativeFamily length family period epsilonIn potential parameter =
      sampledRepresentativeOpen length family period epsilonIn parameter.val (parameter_mem_open length family parameter) potential := by
    simp only [sampledRepresentativeFamily, sampledRepresentativeExtension,
      dif_pos (parameter_mem_open length family parameter)]
  rw [identity]
  exact ⟨rfl, rfl, rfl⟩

/-- Cell periodicity gives both position and magnetic cyclic covariance for
this SAME family, with pressure unchanged. No seed-symmetry premise is used. -/
theorem actual_reference_cyclic_shift (periodPositive : 0 < period) (index : ℕ) (point : ClosedDisk) (time : ℝ) :
    let configuration := sampledRepresentativeFamily length family period epsilonIn potential parameter
    let shift := 2 * Real.pi * index / period
    configuration.position (referenceCover (point, time + shift)) = rotation shift (configuration.position (referenceCover (point, time))) ∧
    configuration.magnetic (referenceCover (point, time + shift)) = rotation shift (configuration.magnetic (referenceCover (point, time))) ∧
    configuration.pressure (referenceCover (point, time + shift)) = configuration.pressure (referenceCover (point, time)) := by
  let shift := 2 * Real.pi * index / period
  have periodNonzero : (period : ℝ) ≠ 0 := (Nat.cast_pos.mpr periodPositive).ne'
  have sampledTime : (period : ℝ) * (time + shift) = (period : ℝ) * time + 2 * Real.pi * index := by
    dsimp only [shift]
    field_simp
  have pointIn := closed_disk_mem_collar length family point.val point.property
  have parameterIn := parameter_mem_open length family parameter
  have values := actual_reference_lift_values length family period epsilonIn potential parameter point time
  have shifted := actual_reference_lift_values length family period epsilonIn potential parameter point (time + shift)
  refine ⟨?_, ?_, ?_⟩
  · rw [shifted.1, values.1]
    unfold sampledPositionLift
    rw [sampledTime, periodic_nat_mul (family.v (sampledEpsilon period) parameter.val point.val)
      (family.vPeriodic (sampledEpsilon period) epsilonIn parameter.val parameterIn point.val pointIn) index ((period : ℝ) * time)]
    rw [add_comm time shift, physical_rotation_add]
  · rw [shifted.2.1, values.2.1]
    unfold sampledMagneticLift
    rw [sampledTime, diskAngular_periodic_nat length family (sampledEpsilon period) parameter.val
      epsilonIn parameterIn point.val pointIn index ((period : ℝ) * time)]
    rw [add_comm time shift, physical_rotation_add]
  · rw [shifted.2.2, values.2.2]
    rfl

end Grad.PhysicalGeometry
