import AKDT2ActualBodyInterior

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledConfigurationRegularity Grad.PhysicalFamily.SampledFullGeometry
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian
open Grad.MainAssembly.CircleIsometryClassification
open Grad.PhysicalFamily.SampledGlobalEmbedding

variable (length : ℝ) (family : CellSolutionFamily length) (period : ℕ)
  (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
  (potential : ℝ) (parameter : Icc family.lower family.upper)

/-- The actual normalized family maps its zero disk onto the exact round axis. -/
theorem actual_position_axis (time : ℝ) :
    (sampledRepresentativeFamily length family period epsilonIn potential parameter).position
      (referenceCover (⟨0, by simp⟩, time)) = ((period : ℝ) * length) • axisRadial time := by
  rw [← (sampled_actual_lifts_values length family period epsilonIn potential parameter (⟨0, by simp⟩, time)).1]
  change sampledPositionJointLift length family period (parameter.val, coordinateDirection 0 time) = _
  rw [sampledPositionJointLift_eq, planarPart_coordinateDirection]
  have timeCoordinate : (coordinateDirection (0 : Plane) time) 2 = time := by simp [coordinateDirection, vector]
  change sampledPositionLift length family period parameter.val (0 : Plane) ((coordinateDirection (0 : Plane) time) 2) = _
  rw [timeCoordinate]
  exact sampledPosition_axis length family period epsilonIn parameter time

/-- Actual embedded positions have the exact disk interior and boundary. -/
theorem actual_position_interior_frontier
    (valid : IsConfiguration .smooth (sampledRepresentativeFamily length family period epsilonIn potential parameter))
    (injective : ∀ (point : Plane), ‖point‖ ≤ 1 → ∀ time : ℝ,
      Function.Injective (fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val)
        (coordinateDirection point time))) (argument : ClosedDisk × ℝ) :
    let configuration := sampledRepresentativeFamily length family period epsilonIn potential parameter
    (configuration.position (referenceCover argument) ∈ interior (range configuration.position) ↔ ‖argument.1.val‖ < 1) ∧
    (configuration.position (referenceCover argument) ∈ frontier (range configuration.position) ↔ ‖argument.1.val‖ = 1) := by
  have same := fun argument => (sampled_actual_lifts_values length family period epsilonIn potential parameter argument).1
  have smooth := (sampled_actual_lifts_smooth length family period epsilonIn potential parameter).1
  exact ⟨position_mem_interior_iff _ valid.1.2.1 _ (sampledAmbientCollar family)
    (sampledAmbientCollar_isOpen family) (sampledAmbientCollar_contains family) smooth same argument
    (injective argument.1.val argument.1.property argument.2),
    position_mem_frontier_iff _ valid.1.2.1 _ (sampledAmbientCollar family)
    (sampledAmbientCollar_isOpen family) (sampledAmbientCollar_contains family) smooth same argument
    (injective argument.1.val argument.1.property argument.2)⟩

theorem actual_position_mem_axis_iff
    (valid : IsConfiguration .smooth (sampledRepresentativeFamily length family period epsilonIn potential parameter))
    (argument : ClosedDisk × ℝ) :
    (sampledRepresentativeFamily length family period epsilonIn potential parameter).position (referenceCover argument) ∈
      roundAxis ((period : ℝ) * length) ↔ argument.1.val = 0 := by
  constructor
  · rintro ⟨angle, equal⟩
    have axisValue := actual_position_axis length family period epsilonIn potential parameter angle
    have axisVector : ((period : ℝ) * length) • axisRadial angle =
        vector (((period : ℝ) * length) * Real.cos angle) (((period : ℝ) * length) * Real.sin angle) 0 := by
      ext coordinate
      fin_cases coordinate <;> simp [axisRadial, vector]
    rw [axisVector] at axisValue
    have referenceSame := valid.1.2.1.injective (axisValue.trans equal)
    have diskSame := congrArg (fun point : Reference => point.1.val) referenceSame
    exact diskSame.symm
  · intro zero
    have argumentSame : argument = (⟨0, by simp⟩, argument.2) := by
      apply Prod.ext
      · exact Subtype.ext zero
      · rfl
    rw [argumentSame, actual_position_axis]
    refine ⟨argument.2, ?_⟩
    ext coordinate
    fin_cases coordinate <;> simp [axisRadial, vector]

theorem actual_axis_subset_interior
    (valid : IsConfiguration .smooth (sampledRepresentativeFamily length family period epsilonIn potential parameter))
    (injective : ∀ (point : Plane), ‖point‖ ≤ 1 → ∀ time : ℝ,
      Function.Injective (fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val)
        (coordinateDirection point time))) :
    roundAxis ((period : ℝ) * length) ⊆
      interior (range (sampledRepresentativeFamily length family period epsilonIn potential parameter).position) := by
  rintro point ⟨time, rfl⟩
  have inside := (actual_position_interior_frontier length family period epsilonIn potential parameter
    valid injective (⟨0, by simp⟩, time)).1.mpr (by simp)
  rw [actual_position_axis] at inside
  have axisVector : ((period : ℝ) * length) • axisRadial time =
      vector (((period : ℝ) * length) * Real.cos time) (((period : ℝ) * length) * Real.sin time) 0 := by
    ext coordinate
    fin_cases coordinate <;> simp [axisRadial, vector]
  rwa [axisVector] at inside

end Grad.PhysicalGeometry
