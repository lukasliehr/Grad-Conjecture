import AED3ExactPhaseDerivativeTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.AnnularTiltedReference
open Grad.AnnularVariational Grad.AnnularHighTilt Grad.CartesianState

/-- The literal new form is the old physical form under opposite actual radial
powers. This is a completed-space identity, with the outer term retained. -/
theorem annularTiltForm_transport (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (field test : annularEnergySpace lower length positive) :
    annularFormValue parameters lower length positive lengthPositive widthHalf widthLength
      (highEnergyUnweight lower length positive bounded field)
      (highEnergyWeight lower length positive bounded test) =
    annularTiltFormValue parameters lower length positive lengthPositive widthHalf widthLength field test := by
  have derivative := congrArg₂ (fun first second : AnnularBulk lower => inner ℂ first second)
    (highEnergyWeight_phaseDerivative parameters lower length positive bounded lengthPositive widthHalf widthLength test)
    (highEnergyUnweight_phaseDerivative parameters lower length positive bounded lengthPositive widthHalf widthLength field)
  have derivativePair := derivative.trans (highBulk_inverse_inner lower positive bounded
    (annularEnergyDerivative lower length positive test +
      annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test)
    (annularEnergyDerivative lower length positive field -
      annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field))
  have mass := congrArg₂ (fun first second : AnnularBulk lower => inner ℂ first second)
    (highEnergyWeight_mass lower length positive bounded test)
    (highEnergyUnweight_mass lower length positive bounded field)
  have massPair := mass.trans (highBulk_inverse_inner lower positive bounded
    (annularEnergyMass lower length positive test) (annularEnergyMass lower length positive field))
  have outerPair := congrArg₂ (fun first second : AnnularBoundary => inner ℂ first second)
    (highEnergyWeight_outer lower length positive bounded test)
    (highEnergyUnweight_outer lower length positive bounded field)
  exact (annularForm_factorized parameters lower length positive lengthPositive widthHalf widthLength
    (highEnergyUnweight lower length positive bounded field)
    (highEnergyWeight lower length positive bounded test)).trans
      ((congrArg₂ (fun first second : ℂ => first + second)
        (congrArg₂ (fun first second : ℂ => first + second) derivativePair massPair) outerPair).trans
          (annularTiltForm_factorized parameters lower length positive lengthPositive widthHalf widthLength field test).symm)

end Grad.AnnularTiltedReference
