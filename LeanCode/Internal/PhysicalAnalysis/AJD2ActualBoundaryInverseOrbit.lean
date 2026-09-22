import AJD1RealToComplexOperatorRetraction
import AJA17ActualFullJetOneHigh

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.AnnularReconstruction Grad.AnnularKernelOrbit Grad.AnnularHighInverseOrbit
open Grad.AnnularCoupledOrbit

private def precomposeOperator {X E F : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (inclusion : X →L[ℂ] E) : (E →L[ℂ] F) →L[ℝ] (X →L[ℂ] F) :=
  ((ContinuousLinearMap.compL ℂ X E F).flip inclusion).restrictScalars ℝ

variable (parameters : PhaseParameters)

/-- Translation of the original high negative-half boundary datum. -/
def highBoundaryTranslation (tau : OrbitParameter) :
    HighBoundaryPrimitive parameters 0 0 →L[ℂ] HighBoundaryPrimitive parameters 0 0 :=
  ((orbitLpAction (ComplexEuclidean 1) tau).comp (highAngularSubmodule parameters 0 0 1).subtypeL).codRestrict
    (highAngularSubmodule parameters 0 0 1) (fun field => by
      change IsHighAngularTrace parameters 0 0 (orbitLpAction (ComplexEuclidean 1) tau field.val)
      intro mode low
      rw [negativeCoefficient_translation, field.property mode low, smul_zero])

theorem highBoundaryTranslation_val (tau : OrbitParameter) (field : HighBoundaryPrimitive parameters 0 0) :
    (highBoundaryTranslation parameters tau field).val = orbitLpAction (ComplexEuclidean 1) tau field.val := rfl

theorem highBoundaryTranslation_norm (tau : OrbitParameter) (field : HighBoundaryPrimitive parameters 0 0) :
    ‖highBoundaryTranslation parameters tau field‖ = ‖field‖ :=
  (orbitLpEquivalence (ComplexEuclidean 1) tau).norm_map field.val

theorem highBoundaryTranslation_inverse (tau : OrbitParameter) (field : HighBoundaryPrimitive parameters 0 0) :
    highBoundaryTranslation parameters tau (highBoundaryTranslation parameters (-tau) field) = field := by
  apply Subtype.ext
  exact orbitLpAction_inverse (ComplexEuclidean 1) tau field.val

def highBoundaryTranslationEquivalence (tau : OrbitParameter) :
    HighBoundaryPrimitive parameters 0 0 ≃ₗᵢ[ℂ] HighBoundaryPrimitive parameters 0 0 where
  toLinearEquiv :=
    { (highBoundaryTranslation parameters tau).toLinearMap with
      invFun := highBoundaryTranslation parameters (-tau)
      left_inv := by
        intro field
        change highBoundaryTranslation parameters (-tau) (highBoundaryTranslation parameters tau field) = field
        simpa only [neg_neg] using highBoundaryTranslation_inverse parameters (-tau) field
      right_inv := highBoundaryTranslation_inverse parameters tau }
  norm_map' := highBoundaryTranslation_norm parameters tau

variable (L compact : ℝ) (state : RetainedInverseState parameters L compact)

def actualBoundaryInverseOrbitJet (angular cell : ℕ) (tau : OrbitParameter) :
    HighBoundaryPrimitive parameters 0 0 →L[ℂ] NegativeTrace parameters 0 0 1 :=
  (boundaryOrbitJetAction parameters 0 0
    (actualHighBoundaryInverse state.outerInverseState.val state.outerInverseState.property) tau angular cell).comp
      (highAngularSubmodule parameters 0 0 1).subtypeL

theorem actualBoundaryInverseOrbitJet_hasFDerivAt (angular cell : ℕ) (tau : OrbitParameter) :
    HasFDerivAt (actualBoundaryInverseOrbitJet parameters L compact state angular cell)
      (orbitColumns (actualBoundaryInverseOrbitJet parameters L compact state (angular + 1) cell tau)
        (actualBoundaryInverseOrbitJet parameters L compact state angular (cell + 1) tau)) tau := by
  let restriction : (NegativeTrace parameters 0 0 1 →L[ℂ] NegativeTrace parameters 0 0 1) →L[ℝ]
      (HighBoundaryPrimitive parameters 0 0 →L[ℂ] NegativeTrace parameters 0 0 1) :=
    precomposeOperator (F := NegativeTrace parameters 0 0 1) (highAngularSubmodule parameters 0 0 1).subtypeL
  have derivative := HasFDerivAt.comp (𝕜 := ℝ) (E := OrbitParameter)
    (F := NegativeTrace parameters 0 0 1 →L[ℂ] NegativeTrace parameters 0 0 1)
    (G := HighBoundaryPrimitive parameters 0 0 →L[ℂ] NegativeTrace parameters 0 0 1) tau
    (ContinuousLinearMap.hasFDerivAt
      (E := NegativeTrace parameters 0 0 1 →L[ℂ] NegativeTrace parameters 0 0 1)
      (F := HighBoundaryPrimitive parameters 0 0 →L[ℂ] NegativeTrace parameters 0 0 1) restriction)
    (boundaryOrbitJetAction_hasFDerivAt parameters 0 0
      (actualHighBoundaryInverse state.outerInverseState.val state.outerInverseState.property) tau angular cell)
  apply derivative.congr_fderiv
  exact orbitDifferential_comp (E := NegativeTrace parameters 0 0 1 →L[ℂ] NegativeTrace parameters 0 0 1)
    (F := HighBoundaryPrimitive parameters 0 0 →L[ℂ] NegativeTrace parameters 0 0 1) restriction _ _

theorem actualBoundaryInverseOrbitJet_contDiff (angular cell : ℕ) :
    ContDiff ℝ ∞ (actualBoundaryInverseOrbitJet parameters L compact state angular cell) :=
  orbitTower_contDiff _ (actualBoundaryInverseOrbitJet_hasFDerivAt parameters L compact state) angular cell

/-- The SAME BCI inverse, acting on the genuinely translated high datum. -/
theorem actualBoundaryInverseOrbit_apply (tau : OrbitParameter) (datum : HighBoundaryPrimitive parameters 0 0) :
    actualBoundaryInverseOrbitJet parameters L compact state 0 0 tau datum =
      orbitLpAction (ComplexEuclidean 1) tau
        (actualBoundaryInverseOnHigh state.outerInverseState 0 0 (highBoundaryTranslation parameters (-tau) datum)).val := by
  unfold actualBoundaryInverseOrbitJet boundaryOrbitJetAction
  rw [kernelOrbitJet_zero, fullNegativeKernelAction_orbit]
  rfl

end Grad.AnnularCrossOrbit
