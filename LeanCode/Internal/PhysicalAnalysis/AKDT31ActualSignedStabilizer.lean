import AKDT30ActualCyclicStabilizer

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalFamily
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily

/-- The complete signed stabilizer of these SAME canonical fields is exactly
 the finite cyclic group in the unchanged main statement. -/
theorem actual_signed_stabilizer (length : ℝ) (positive : 0 < length)
    (family : CellSolutionFamily length) (period : ℕ) (periodPositive : 0 < period)
    (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Icc family.lower family.upper)
    (valid : IsConfiguration .smooth (sampledRepresentativeFamily length family period epsilonIn potential parameter))
    (injective : ∀ (point : Plane), ‖point‖ ≤ 1 → ∀ time : ℝ,
      Function.Injective (fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val)
        (coordinateDirection point time)))
    (magnetic : Vec → Vec) (pressure : Vec → ℝ)
    (magneticSmooth : ContDiff ℝ ∞ magnetic) (pressureSmooth : ContDiff ℝ ∞ pressure)
    (pressureNear : SmoothNear (range (sampledRepresentativeFamily length family period epsilonIn potential parameter).position) pressure)
    (same : ∀ argument,
      magnetic ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
        (sampledRepresentativeFamily length family period epsilonIn potential parameter).magnetic argument ∧
      pressure ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
        (sampledRepresentativeFamily length family period epsilonIn potential parameter).pressure argument)
    (orthogonal : Vec ≃ₗᵢ[ℝ] Vec) (translation : Vec) :
    SignedStabilizes (range (sampledRepresentativeFamily length family period epsilonIn potential parameter).position)
      magnetic pressure orthogonal translation ↔
      ∃ index : ℕ, index < period ∧ ∀ point : Vec,
        orthogonal point + translation = rotation (2 * Real.pi * index / period) point := by
  constructor
  · intro stabilizes
    have shape := actual_prescribed_normal_shape length positive family period periodPositive epsilonIn potential parameter
      valid injective magnetic pressure magneticSmooth pressureSmooth same
    have axisInterior := actual_axis_subset_interior length family period epsilonIn potential parameter valid injective
    have zeroSet := (actual_field_zero_sets length family period epsilonIn potential parameter valid injective
      magnetic pressure magneticSmooth pressureSmooth same).2
    have alphaNotLattice : ∀ integer : ℤ, 2 * family.alpha ≠ (integer : ℝ) * Real.pi := by
      intro integer equality
      apply family.alphaNonresonant integer
      linarith
    obtain ⟨integer, motion⟩ := signed_stabilizer_integral_rotation _ _ _ _ _ _ period
      (mul_pos (Nat.cast_pos.mpr periodPositive) positive) periodPositive family.rhoPositive
      (family.lowerPositive.trans_le parameter.property.1) family.deltaNonzero alphaNotLattice shape
      magnetic pressure pressureNear (fun argument => (same argument).2) axisInterior zeroSet orthogonal translation stabilizes
    obtain ⟨index, indexBound, rotationSame⟩ := integral_rotation_finite_index period periodPositive integer
    exact ⟨index, indexBound, fun point => (motion point).trans (rotationSame point)⟩
  · rintro ⟨index, _, motion⟩
    exact actual_cyclic_rotation_stabilizes length family period periodPositive epsilonIn potential parameter
      magnetic pressure same index orthogonal translation motion

end Grad.PhysicalGeometry
