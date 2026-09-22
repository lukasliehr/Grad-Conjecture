import AKDT18ActualPressureTori

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian

/-- The literal regular-level convention is exactly the range 0<r≤1;
nonempty levels outside it are never called tori. -/
theorem actual_regular_pressure_levels (length : ℝ) (family : CellSolutionFamily length) (period : ℕ)
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
    let body := range (sampledRepresentativeFamily length family period epsilonIn potential parameter).position
    (∀ radius : Ioc (0 : ℝ) 1, IsRegularLevel body pressure (potential - radius.val ^ 2)) ∧
    (∀ value, (pressureLevel body pressure value).Nonempty → IsRegularLevel body pressure value →
      ∃ radius : Ioc (0 : ℝ) 1, value = potential - radius.val ^ 2) ∧
    (∀ point ∈ body \ roundAxis ((period : ℝ) * length), IsRegularLevel body pressure (pressure point)) := by
  let configuration := sampledRepresentativeFamily length family period epsilonIn potential parameter
  have criticalSet := (actual_field_zero_sets length family period epsilonIn potential parameter valid injective
    magnetic pressure magneticSmooth pressureSmooth same).1
  have critical (reference : Reference) : fderiv ℝ pressure (configuration.position reference) = 0 ↔ reference.1.val = 0 := by
    have axis : fderiv ℝ pressure (configuration.position reference) = 0 ↔ configuration.position reference ∈ roundAxis ((period : ℝ) * length) := by
      constructor
      · intro derivative
        rw [← criticalSet]
        exact ⟨⟨reference, rfl⟩, derivative⟩
      · intro axisIn
        rw [← criticalSet] at axisIn
        exact axisIn.2
    exact axis.trans (actual_reference_axis_iff length family period epsilonIn potential parameter valid reference)
  have formula := actual_pressure_reference length family period epsilonIn potential parameter pressure (fun argument => (same argument).2)
  have regular (radius : Ioc (0 : ℝ) 1) : IsRegularLevel (range configuration.position) pressure (potential - radius.val ^ 2) := by
    rintro point ⟨⟨reference, rfl⟩, value⟩ zero
    have diskZero := (critical reference).mp zero
    rw [formula, diskZero, norm_zero, zero_pow (by norm_num), sub_zero] at value
    nlinarith [radius.property.1]
  refine ⟨regular, ?_, ?_⟩
  · intro value nonempty isRegular
    obtain ⟨point, ⟨⟨reference, rfl⟩, valueSame⟩⟩ := nonempty
    have nonzero : reference.1.val ≠ 0 := by
      intro zero
      exact isRegular _ ⟨⟨reference, rfl⟩, valueSame⟩ ((critical reference).mpr zero)
    refine ⟨⟨‖reference.1.val‖, norm_pos_iff.mpr nonzero, reference.1.property⟩, ?_⟩
    exact valueSame.symm.trans (formula reference)
  · rintro point ⟨⟨reference, rfl⟩, outside⟩
    have nonzero : reference.1.val ≠ 0 := by
      rwa [actual_reference_axis_iff length family period epsilonIn potential parameter valid] at outside
    rw [formula]
    exact regular ⟨‖reference.1.val‖, norm_pos_iff.mpr nonzero, reference.1.property⟩

end Grad.PhysicalGeometry
