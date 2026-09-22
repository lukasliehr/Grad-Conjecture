import AED6ExactSourceTestCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.AnnularTiltedReference
open Grad.AnnularVariational Grad.AnnularHighTilt Grad.AnnularReconstruction Grad.CartesianState

/-- The same three bulk source slots acquire r^alpha; the actual outer datum
is unchanged. This is a bounded map on the independent original forcing product. -/
def highForcingUnweight (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    AnnularForcing lower →L[ℂ] AnnularForcing lower :=
  (highBulkUnweight lower positive bounded).prodMap
    ((highBulkUnweight lower positive bounded).prodMap
      ((highBulkUnweight lower positive bounded).prodMap (ContinuousLinearMap.id ℂ AnnularBoundary)))

section Functional
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem highEnergyWeight_sourceTest (test : annularEnergySpace lower length positive) :
    annularSourceTest parameters lower length positive lengthPositive widthHalf widthLength
      (highEnergyWeight lower length positive bounded.le test) =
    highBulkWeight lower positive bounded.le
      (annularTiltSourceTest parameters lower length positive lengthPositive widthHalf widthLength test) := by
  change (annularEnergyDerivative lower length positive (highEnergyWeight lower length positive bounded.le test) +
    annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength
      (highEnergyWeight lower length positive bounded.le test)) +
    annularEnergyRadial lower length positive (highEnergyWeight lower length positive bounded.le test) =
    highBulkWeight lower positive bounded.le
      ((annularEnergyDerivative lower length positive test +
        annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test) +
      annularEnergyRadial lower length positive test)
  have phase := highEnergyWeight_phaseDerivative parameters lower length positive bounded.le
    lengthPositive widthHalf widthLength test
  have radial := highEnergyWeight_radial lower length positive bounded.le test
  exact (congrArg₂ (fun first second : AnnularBulk lower => first + second) phase radial).trans
    ((highBulkWeight lower positive bounded.le).map_add _ _).symm

/-- Exact functional transport; all independent source slots and the true
outer trace are retained. -/
theorem annularTiltFunctional_transport (source : AnnularForcing lower)
    (test : annularEnergySpace lower length positive) :
    annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength
      (highForcingUnweight lower positive bounded.le source)
      (highEnergyWeight lower length positive bounded.le test) =
    annularTiltFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source test := by
  have first := (congrArg (fun value : AnnularBulk lower =>
      inner ℂ value (highBulkUnweight lower positive bounded.le source.1))
    (highEnergyWeight_sourceTest parameters lower length positive bounded lengthPositive widthHalf widthLength test)).trans
      (highBulk_inverse_inner lower positive bounded.le
        (annularTiltSourceTest parameters lower length positive lengthPositive widthHalf widthLength test) source.1)
  have second := (congrArg (fun value : AnnularBulk lower =>
      inner ℂ value (highBulkUnweight lower positive bounded.le source.2.1))
    (highEnergyWeight_d lower length positive bounded.le test)).trans
      (highBulk_inverse_inner lower positive bounded.le (annularEnergyD lower length positive test) source.2.1)
  have third := (congrArg (fun value : AnnularBulk lower =>
      inner ℂ value (highBulkUnweight lower positive bounded.le source.2.2.1))
    (highEnergyWeight_cell lower length positive bounded.le test)).trans
      (highBulk_inverse_inner lower positive bounded.le (annularEnergyCell lower length positive test) source.2.2.1)
  have fourth := congrArg (fun value : AnnularBoundary => inner ℂ value source.2.2.2)
    (highEnergyWeight_outerTrace lower length positive bounded lengthPositive test)
  exact congrArg₂ (fun first second : ℂ => first - second)
    (congrArg₂ (fun first second : ℂ => first - second)
      (congrArg₂ (fun first second : ℂ => first - second) first second) third) fourth

end Functional
end Grad.AnnularTiltedReference
