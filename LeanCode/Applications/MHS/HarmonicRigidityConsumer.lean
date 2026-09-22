import HarmonicRigidityProof

noncomputable section

namespace Grad.MainAssembly.HarmonicRigidity.Consumer

open Grad.MainAssembly.HarmonicRigidity

/-- Combined exact G23 consumer on the shortest path to `NG_R17`. -/
theorem full_two_parameter_two_sign_harmonic_rigidity
    (alpha delta firstParameter secondParameter tangentSign normalSign shift : ℝ)
    (firstPositive : 0 < firstParameter)
    (secondPositive : 0 < secondParameter)
    (deltaNonzero : delta ≠ 0)
    (alphaNotLattice : ∀ integer : ℤ,
      2 * alpha ≠ (integer : ℝ) * Real.pi)
    (tangentSignValue : tangentSign = 1 ∨ tangentSign = -1)
    (normalSignValue : normalSign = 1 ∨ normalSign = -1)
    (angleCongruence : ∀ time, ∃ integer : ℤ,
      alphaAngle alpha delta secondParameter (tangentSign * time + shift) -
          normalSign * alphaAngle alpha delta firstParameter time =
        (integer : ℝ) * Real.pi) :
    normalSign = 1 ∧ tangentSign = 1 ∧
      (∃ integer : ℤ, shift = (integer : ℝ) * (2 * Real.pi)) ∧
      secondParameter = firstParameter := by
  have normalConclusion := harmonic_normal_sign_and_lattice_zero
    alpha delta firstParameter secondParameter tangentSign normalSign shift
    deltaNonzero alphaNotLattice tangentSignValue normalSignValue angleCongruence
  have angleIdentity : ∀ time,
      alphaAngle alpha delta secondParameter (tangentSign * time + shift) -
        alphaAngle alpha delta firstParameter time = 0 := by
    simpa [normalConclusion.1] using normalConclusion.2
  have period := first_harmonic_forces_integral_period
    alpha delta firstParameter secondParameter tangentSign shift deltaNonzero
    tangentSignValue angleIdentity
  have parameterConclusion := second_harmonic_forces_parameter_and_tangent_sign
    alpha delta firstParameter secondParameter tangentSign shift firstPositive
    secondPositive deltaNonzero tangentSignValue period angleIdentity
  exact ⟨normalConclusion.1, parameterConclusion.1, period,
    parameterConclusion.2⟩

end Grad.MainAssembly.HarmonicRigidity.Consumer
