import AKDT26RotationFromFrame

noncomputable section
open Set

namespace Grad.PhysicalGeometry
open Grad.MainTarget
open Grad.MainAssembly.PhysicalSimilarityRigidity Grad.MainAssembly.SampledPhysicalSimilarityRigidity
open Grad.MainAssembly.CircleIsometryClassification Grad.MainAssembly.HarmonicRigidity

/-- The upper stabilizer inclusion uses the genuine pressure tensor and the
full two-sign harmonic rigidity. The magnetic sign is never restricted. -/
theorem signed_stabilizer_integral_rotation
    (configuration : Representative) (radius rho alpha delta parameter : ℝ) (period : ℕ)
    (radiusPositive : 0 < radius) (periodPositive : 0 < period) (rhoPositive : 0 < rho)
    (parameterPositive : 0 < parameter) (deltaNonzero : delta ≠ 0)
    (alphaNotLattice : ∀ integer : ℤ, 2 * alpha ≠ (integer : ℝ) * Real.pi)
    (shape : HasPrescribedNormalShape configuration radius rho (sampledAlphaAngle period alpha delta parameter))
    (magnetic : Vec → Vec) (pressure : Vec → ℝ)
    (pressureNear : SmoothNear (range configuration.position) pressure)
    (represents : ∀ reference, pressure (configuration.position reference) = configuration.pressure reference)
    (axisInterior : roundAxis radius ⊆ interior (range configuration.position))
    (zeroSet : ∀ point ∈ range configuration.position, magnetic point = 0 ↔ point ∈ roundAxis radius)
    (orthogonal : Vec ≃ₗᵢ[ℝ] Vec) (translation : Vec)
    (stabilizes : SignedStabilizes (range configuration.position) magnetic pressure orthogonal translation) :
    ∃ integer : ℤ, ∀ point : Vec, orthogonal point + translation = rotation (2 * Real.pi * integer / period) point := by
  have axisEquality := signedStabilizes_preserves_axis (range configuration.position) (roundAxis radius)
    magnetic pressure (fun _ membership => interior_subset (axisInterior membership)) zeroSet orthogonal translation stabilizes
  obtain ⟨translationZero, tangentSign, verticalSign, shift, tangentSignValue, verticalSignValue,
    radialAction, tangentAction, verticalAction, _⟩ :=
    circleIsometryClassification radius orthogonal translation radiusPositive axisEquality
  subst translation
  have pressurePreserved : ∀ point ∈ range configuration.position, pressure (orthogonal point) = pressure point := by
    simpa only [add_zero] using stabilizes.2.1
  have angleCongruence := preserved_normal_shape_angle_congruence configuration radius rho alpha delta parameter period
    rhoPositive shape pressure pressureNear represents axisInterior orthogonal pressurePreserved
    tangentSign verticalSign shift verticalSignValue radialAction verticalAction
  have periodNonzero : (period : ℝ) ≠ 0 := (Nat.cast_pos.mpr periodPositive).ne'
  have rescaled : ∀ time, ∃ integer : ℤ,
      alphaAngle alpha delta parameter (tangentSign * time + (period : ℝ) * shift) -
        verticalSign * alphaAngle alpha delta parameter time = (integer : ℝ) * Real.pi := by
    intro time
    obtain ⟨integer, equality⟩ := angleCongruence (time / (period : ℝ))
    refine ⟨integer, ?_⟩
    unfold sampledAlphaAngle at equality
    convert equality using 1
    field_simp
  obtain ⟨verticalOne, tangentOne, ⟨integer, shiftMultiple⟩, _⟩ :=
    Grad.MainAssembly.HarmonicRigidity.Consumer.full_two_parameter_two_sign_harmonic_rigidity
      alpha delta parameter parameter tangentSign verticalSign ((period : ℝ) * shift)
      parameterPositive parameterPositive deltaNonzero alphaNotLattice tangentSignValue verticalSignValue rescaled
  have shiftSame : shift = 2 * Real.pi * integer / period := by
    apply (eq_div_iff periodNonzero).mpr
    calc
      shift * (period : ℝ) = (period : ℝ) * shift := mul_comm _ _
      _ = (integer : ℝ) * (2 * Real.pi) := shiftMultiple
      _ = _ := by ring
  have rotationSame := orthogonal_eq_rotation_of_axis_frame orthogonal shift
    (by simpa only [tangentOne, one_mul, mul_zero, zero_add] using radialAction 0)
    (by simpa only [tangentOne, one_mul, mul_zero, zero_add, one_smul] using tangentAction 0)
    (by simpa only [verticalOne, one_smul] using verticalAction)
  refine ⟨integer, ?_⟩
  intro point
  rw [add_zero, rotationSame, shiftSame]

end Grad.PhysicalGeometry
