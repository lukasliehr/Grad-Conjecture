import AKDT6ActualBoundaryTangency

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient Grad.PhysicalEquilibrium
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledConfigurationRegularity Grad.PhysicalFamily.SampledFullGeometry
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian

/-- Both exact zero-set clauses of the unchanged physical target, on the SAME
body and with the original round axis. -/
theorem actual_field_zero_sets (length : ℝ) (family : CellSolutionFamily length) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Icc family.lower family.upper)
    (valid : IsConfiguration .smooth (sampledRepresentativeFamily length family period epsilonIn potential parameter))
    (injective : ∀ (point : Plane), ‖point‖ ≤ 1 → ∀ time : ℝ,
      Function.Injective (fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val)
        (coordinateDirection point time)))
    (magnetic : Vec → Vec) (pressure : Vec → ℝ)
    (magneticSmooth : ContDiff ℝ ∞ magnetic) (pressureSmooth : ContDiff ℝ ∞ pressure)
    (same : ∀ argument,
      magnetic ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
        (sampledRepresentativeFamily length family period epsilonIn potential parameter).magnetic argument ∧
      pressure ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
        (sampledRepresentativeFamily length family period epsilonIn potential parameter).pressure argument) :
    let configuration := sampledRepresentativeFamily length family period epsilonIn potential parameter
    {point | point ∈ range configuration.position ∧ fderiv ℝ pressure point = 0} = roundAxis ((period : ℝ) * length) ∧
    ∀ point ∈ range configuration.position, magnetic point = 0 ↔ point ∈ roundAxis ((period : ℝ) * length) := by
  let configuration := sampledRepresentativeFamily length family period epsilonIn potential parameter
  have atCover (argument : ClosedDisk × ℝ) :
      (fderiv ℝ pressure (configuration.position (referenceCover argument)) = 0 ↔ argument.1.val = 0) ∧
      (magnetic (configuration.position (referenceCover argument)) = 0 ↔ argument.1.val = 0) := by
    have critical := actual_pressure_critical_iff length family period epsilonIn potential parameter magnetic pressure
      magneticSmooth pressureSmooth same argument.1.val argument.1.property argument.2
      (injective argument.1.val argument.1.property argument.2)
    have magneticZero := actual_magnetic_zero_iff length family period epsilonIn potential parameter magnetic pressure
      magneticSmooth pressureSmooth same argument.1.val argument.1.property argument.2
      (injective argument.1.val argument.1.property argument.2)
    have positionSame := (sampled_actual_lifts_values length family period epsilonIn potential parameter argument).1
    change sampledPositionCoordinateValue length family period parameter.val
      (coordinateDirection argument.1.val argument.2) = configuration.position (referenceCover argument) at positionSame
    rw [positionSame] at critical magneticZero
    exact ⟨critical, magneticZero⟩
  have bodyCritical (point : Vec) (pointIn : point ∈ range configuration.position) :
      fderiv ℝ pressure point = 0 ↔ point ∈ roundAxis ((period : ℝ) * length) := by
    obtain ⟨reference, rfl⟩ := pointIn
    obtain ⟨argument, rfl⟩ := referenceCover_surjective reference
    exact (atCover argument).1.trans
      (actual_position_mem_axis_iff length family period epsilonIn potential parameter valid argument).symm
  constructor
  · ext point
    constructor
    · rintro ⟨pointIn, critical⟩
      exact (bodyCritical point pointIn).mp critical
    · intro axisIn
      have bodyIn := interior_subset
        (actual_axis_subset_interior length family period epsilonIn potential parameter valid injective axisIn)
      exact ⟨bodyIn, (bodyCritical point bodyIn).mpr axisIn⟩
  · intro point pointIn
    obtain ⟨reference, rfl⟩ := pointIn
    obtain ⟨argument, rfl⟩ := referenceCover_surjective reference
    exact (atCover argument).2.trans
      (actual_position_mem_axis_iff length family period epsilonIn potential parameter valid argument).symm

end Grad.PhysicalGeometry
