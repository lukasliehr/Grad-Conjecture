import AEB13ExactTiltedReferenceConsumer
import AAQ3NormalizedRadialMaps

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.AnnularTiltedReference
open Grad.AnnularVariational Grad.AnnularReconstruction Grad.SourceCollarDivision
open Grad.CartesianState Grad.CircularHighRegularity

/-- Exact orthogonal coordinate pairing on the completed high energy space. -/
theorem annularEnergy_inner_coordinates (lower length : ℝ) (positive : 0 < lower)
    (test field : annularEnergySpace lower length positive) :
    inner ℂ test field =
      inner ℂ (annularEnergyDerivative lower length positive test)
        (annularEnergyDerivative lower length positive field) +
      inner ℂ (annularEnergyMass lower length positive test)
        (annularEnergyMass lower length positive field) +
      inner ℂ (annularEnergyOuter lower length positive test)
        (annularEnergyOuter lower length positive field) := by
  have derivative := lp.summable_inner (𝕜 := ℂ)
    (annularEnergyDerivative lower length positive test) (annularEnergyDerivative lower length positive field)
  have mass := lp.summable_inner (𝕜 := ℂ)
    (annularEnergyMass lower length positive test) (annularEnergyMass lower length positive field)
  have outer := lp.summable_inner (𝕜 := ℂ)
    (annularEnergyOuter lower length positive test) (annularEnergyOuter lower length positive field)
  change inner ℂ test.val field.val = _
  simp only [lp.inner_eq_tsum]
  change (∑' mode, (inner ℂ (annularEnergyDerivative lower length positive test mode)
      (annularEnergyDerivative lower length positive field mode) +
    (inner ℂ (annularEnergyMass lower length positive test mode)
      (annularEnergyMass lower length positive field mode) +
    inner ℂ (annularEnergyOuter lower length positive test mode)
      (annularEnergyOuter lower length positive field mode)))) = _
  rw [derivative.tsum_add (mass.add outer), mass.tsum_add outer, add_assoc]

/-- The original form is the literal product of opposite phase derivatives,
plus potential and the original outer term. -/
theorem annularForm_factorized (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (field test : annularEnergySpace lower length positive) :
    annularFormValue parameters lower length positive lengthPositive widthHalf widthLength field test =
      inner ℂ (annularEnergyDerivative lower length positive test +
        annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test)
        (annularEnergyDerivative lower length positive field -
        annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field) +
      inner ℂ (annularEnergyMass lower length positive test) (annularEnergyMass lower length positive field) +
      inner ℂ (annularEnergyOuter lower length positive test) (annularEnergyOuter lower length positive field) := by
  rw [annularFormValue, annularEnergy_inner_coordinates]
  simp only [inner_add_left, inner_sub_right]
  abel

/-- The new tilt changes only the exact phase slope in the same physical form. -/
theorem annularTiltForm_factorized (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (field test : annularEnergySpace lower length positive) :
    annularTiltFormValue parameters lower length positive lengthPositive widthHalf widthLength field test =
      inner ℂ (annularEnergyDerivative lower length positive test +
        annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test)
        (annularEnergyDerivative lower length positive field -
        annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field) +
      inner ℂ (annularEnergyMass lower length positive test) (annularEnergyMass lower length positive field) +
      inner ℂ (annularEnergyOuter lower length positive test) (annularEnergyOuter lower length positive field) := by
  rw [annularTiltFormValue, annularEnergy_inner_coordinates]
  simp only [inner_add_left, inner_sub_right]
  abel

/-- Real scalar radial multiplication is self-adjoint on the actual r dr storage. -/
theorem scalarRadialMap_inner (lower : ℝ) (coefficient : C(ℝ, ℝ)) (bound : ℝ)
    (bounded : ∀ radius ∈ Icc lower 1, |coefficient radius| ≤ bound)
    (test field : RadialL2 1 lower) :
    inner ℂ (scalarRadialMap lower coefficient bound bounded test) field =
      inner ℂ test (scalarRadialMap lower coefficient bound bounded field) := by
  rw [Grad.AnnularFluxTrace.scalarRadialMap_eq_collarScalar,
    Grad.AnnularFluxTrace.scalarRadialMap_eq_collarScalar, collarScalar_inner]

end Grad.AnnularTiltedReference
