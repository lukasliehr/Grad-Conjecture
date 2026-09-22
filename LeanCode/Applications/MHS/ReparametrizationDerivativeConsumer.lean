import ReparametrizationDerivative

noncomputable section

open Set
open scoped ContDiff

namespace Grad.MainAssembly.TargetReparametrization.Consumer

open Grad.MainTarget

/-- The exact rank consequence consumed by target embedding preservation. -/
theorem localLift_fderiv_injective
    (regularity : Regularity) (admissible : regularity.admissible)
    (reparametrization : Reference ≃ Reference)
    (isReparametrization : IsReparametrization regularity reparametrization)
    (point : Vec) (pointInCylinder : point ∈ cylinder)
    (forwardNeighborhood : Set Vec) (forwardOpen : IsOpen forwardNeighborhood)
    (pointInForward : point ∈ forwardNeighborhood) (forwardLift : Vec → Vec)
    (forwardSmooth : ContDiffOn ℝ regularity.order forwardLift forwardNeighborhood)
    (forwardAgreement : ∀ argument ∈ forwardNeighborhood,
      ∀ membership : argument ∈ cylinder,
        ∃ imageMembership : forwardLift argument ∈ cylinder,
          quotientPoint (forwardLift argument) imageMembership =
            reparametrization (quotientPoint argument membership)) :
    Function.Injective (fderiv ℝ forwardLift point) := by
  obtain ⟨_normalizedInverse, derivativeEquiv, _inverseDifferentiable,
      forwardDerivative, _inverseDerivative⟩ :=
    localLiftDerivativeEquiv regularity admissible reparametrization
      isReparametrization point pointInCylinder forwardNeighborhood forwardOpen
      pointInForward forwardLift forwardSmooth forwardAgreement
  rw [← forwardDerivative]
  exact derivativeEquiv.injective

end Grad.MainAssembly.TargetReparametrization.Consumer
