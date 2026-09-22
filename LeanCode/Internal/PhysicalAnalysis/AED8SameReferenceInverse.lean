import AED7ExactForcingTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.AnnularTiltedReference
open Grad.AnnularVariational Grad.AnnularHighTilt Grad.CartesianState

section Solution
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- The constructed tilted inverse is exactly the accepted original reference
inverse after actual source and incoming transport. No new differential
solution or regularity hypothesis is introduced. -/
theorem annularTiltSolution_same_reference (source : AnnularForcing lower) (incoming : AnnularBoundary) :
    highEnergyUnweight lower length positive bounded.le
      (annularTiltVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source incoming) =
    annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength
      (highForcingUnweight lower positive bounded.le source)
      (((lower ^ highTiltExponent : ℝ) : ℂ) • incoming) := by
  apply annularVariationalSolution_unique parameters lower length positive bounded lengthPositive widthHalf widthLength
  · rw [highEnergyUnweight_innerTrace, annularTiltVariationalSolution_inner]
  · intro test
    let tiltedTest : annularInnerZero lower length positive bounded lengthPositive :=
      ⟨highEnergyUnweight lower length positive bounded.le test.val,
        highEnergyUnweight_innerZero lower length positive bounded lengthPositive test⟩
    have testIdentity : highEnergyWeight lower length positive bounded.le tiltedTest.val = test.val :=
      highEnergy_weight_unweight lower length positive bounded.le test.val
    have form := annularTiltForm_transport parameters lower length positive bounded.le lengthPositive widthHalf widthLength
      (annularTiltVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source incoming)
      tiltedTest.val
    have forcing := annularTiltFunctional_transport parameters lower length positive bounded lengthPositive widthHalf widthLength
      source tiltedTest.val
    rw [testIdentity] at form forcing
    exact form.trans ((annularTiltVariationalSolution_weak parameters lower length positive bounded lengthPositive
      widthHalf widthLength source incoming tiltedTest).trans forcing.symm)

/-- The reverse identity fixes the actual new solution by the existing inverse. -/
theorem annularTiltSolution_from_reference (source : AnnularForcing lower) (incoming : AnnularBoundary) :
    annularTiltVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source incoming =
    highEnergyWeight lower length positive bounded.le
      (annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength
        (highForcingUnweight lower positive bounded.le source)
        (((lower ^ highTiltExponent : ℝ) : ℂ) • incoming)) := by
  have equality := congrArg (highEnergyWeight lower length positive bounded.le)
    (annularTiltSolution_same_reference parameters lower length positive bounded lengthPositive widthHalf widthLength source incoming)
  exact (highEnergy_weight_unweight lower length positive bounded.le _).symm.trans equality

/-- Exact bounded-inverse consumer on the independent normalized data product. -/
theorem annularTiltInverse_same_reference (data : AnnularForcing lower × AnnularBoundary) :
    highEnergyUnweight lower length positive bounded.le
      (annularTiltVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength data) =
    annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength
      (highForcingUnweight lower positive bounded.le data.1, (((lower ^ highTiltExponent : ℝ) : ℂ) • data.2)) :=
  annularTiltSolution_same_reference parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2

end Solution
end Grad.AnnularTiltedReference
