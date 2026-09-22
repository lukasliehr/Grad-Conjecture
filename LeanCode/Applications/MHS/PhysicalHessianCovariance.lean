import PhysicalSimilarity
import RoundAxisSimilarity
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section

open Set Filter
open scoped ContDiff

namespace Grad.MainAssembly.PhysicalHessianCovariance

open Grad.MainTarget

/-- The ambient second Fréchet derivative of a reconstructed pressure. -/
def pressureHessian (pressure : Vec → ℝ) (point : Vec) :
    Vec [×2]→L[ℝ] ℝ :=
  iteratedFDeriv ℝ 2 pressure point

/-- Two ambient pressure fields representing the same target pressure have
identical Hessians at every interior body point. -/
theorem pressureHessian_eq_of_represents
    (representative : Representative) (firstPressure secondPressure : Vec → ℝ)
    (firstRepresents : ∀ point : Reference,
      firstPressure (representative.position point) = representative.pressure point)
    (secondRepresents : ∀ point : Reference,
      secondPressure (representative.position point) = representative.pressure point)
    (point : Vec) (pointInterior : point ∈ interior (Set.range representative.position)) :
    pressureHessian firstPressure point = pressureHessian secondPressure point := by
  have localEquality : firstPressure =ᶠ[nhds point] secondPressure := by
    filter_upwards [isOpen_interior.mem_nhds pointInterior] with argument argumentInterior
    rcases interior_subset argumentInterior with ⟨reference, rfl⟩
    rw [firstRepresents reference, secondRepresents reference]
  exact (localEquality.iteratedFDeriv ℝ 2).eq_of_nhds

/-- The invertible linear part of a positive Euclidean similarity. -/
def scaledOrthogonal (spatialScale : ℝ) (scaleNonzero : spatialScale ≠ 0)
    (orthogonal : Vec ≃ₗᵢ[ℝ] Vec) : Vec ≃L[ℝ] Vec :=
  orthogonal.toContinuousLinearEquiv.trans
    (ContinuousLinearEquiv.smulLeft (Units.mk0 spatialScale scaleNonzero))

@[simp]
theorem scaledOrthogonal_apply (spatialScale : ℝ)
    (scaleNonzero : spatialScale ≠ 0)
    (orthogonal : Vec ≃ₗᵢ[ℝ] Vec) (point : Vec) :
    scaledOrthogonal spatialScale scaleNonzero orthogonal point =
      spatialScale • orthogonal point := rfl

private theorem iteratedFDeriv_two_affine_precomposition
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    (function : Space → ℝ) (linear : Space ≃L[ℝ] Space)
    (translation point : Space) :
    iteratedFDeriv ℝ 2
        (fun argument => function (linear argument + translation)) point =
      (iteratedFDeriv ℝ 2 function (linear point + translation)).compContinuousLinearMap
        (fun _ => linear.toContinuousLinearMap) := by
  let shifted := fun argument : Space => function (argument + translation)
  change iteratedFDeriv ℝ 2 (shifted ∘ linear) point = _
  have composed := linear.iteratedFDerivWithin_comp_right shifted
    uniqueDiffOn_univ (mem_univ (linear point)) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at composed
  dsimp only [shifted] at composed
  rw [iteratedFDeriv_comp_add_right] at composed
  exact composed

private theorem iteratedFDeriv_two_affine_output
    (pressure : Vec → ℝ) (amplitude pressureOffset : ℝ) (point : Vec)
    (smooth : ContDiffAt ℝ 2 pressure point) :
    iteratedFDeriv ℝ 2
        (fun argument => amplitude ^ 2 * pressure argument + pressureOffset) point =
      amplitude ^ 2 • iteratedFDeriv ℝ 2 pressure point := by
  change iteratedFDeriv ℝ 2
      ((amplitude ^ 2) • pressure + fun _ : Vec => pressureOffset) point = _
  calc
    _ = iteratedFDeriv ℝ 2 ((amplitude ^ 2) • pressure) point +
        iteratedFDeriv ℝ 2 (fun _ : Vec => pressureOffset) point :=
      iteratedFDeriv_add_apply (smooth.const_smul (amplitude ^ 2)) contDiffAt_const
    _ = _ := by
      rw [iteratedFDeriv_const_smul_apply smooth]
      simp [iteratedFDeriv_const_of_ne]

/-- Exact ambient Hessian covariance following from the pressure clause of a
physical similarity.  Equality only on the physical body is sufficient because
the source point is in its interior.  The pressure offset differentiates away,
and neither orientation preservation nor a positive magnetic amplitude is
assumed. -/
theorem pressureHessian_scaled_covariance
    (firstBody : Set Vec) (firstPressure secondPressure : Vec → ℝ)
    (spatialScale amplitude : ℝ) (orthogonal : Vec ≃ₗᵢ[ℝ] Vec)
    (translation : Vec) (pressureOffset : ℝ)
    (scalePositive : 0 < spatialScale)
    (firstSmooth : SmoothNear firstBody firstPressure)
    (pressureRelation : ∀ point ∈ firstBody,
      secondPressure (spatialScale • orthogonal point + translation) =
        amplitude ^ 2 * firstPressure point + pressureOffset)
    (point : Vec) (pointInterior : point ∈ interior firstBody) :
    (pressureHessian secondPressure
        (spatialScale • orthogonal point + translation)).compContinuousLinearMap
        (fun _ =>
          (scaledOrthogonal spatialScale scalePositive.ne' orthogonal).toContinuousLinearMap) =
      amplitude ^ 2 • pressureHessian firstPressure point := by
  rcases firstSmooth with
    ⟨neighborhood, neighborhoodOpen, bodyInNeighborhood, pressureSmooth⟩
  have pointInNeighborhood : point ∈ neighborhood :=
    bodyInNeighborhood (interior_subset pointInterior)
  have smoothAt : ContDiffAt ℝ 2 firstPressure point :=
    (pressureSmooth.contDiffAt
      (neighborhoodOpen.mem_nhds pointInNeighborhood)).of_le
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have localRelation :
      (fun argument =>
          secondPressure (spatialScale • orthogonal argument + translation)) =ᶠ[nhds point]
        (fun argument =>
          amplitude ^ 2 * firstPressure argument + pressureOffset) := by
    filter_upwards [isOpen_interior.mem_nhds pointInterior] with argument argumentInterior
    exact pressureRelation argument (interior_subset argumentInterior)
  have derivativeRelation :=
    (localRelation.iteratedFDeriv ℝ 2).eq_of_nhds
  rw [iteratedFDeriv_two_affine_output firstPressure amplitude pressureOffset point
    smoothAt] at derivativeRelation
  have affineDerivative := iteratedFDeriv_two_affine_precomposition
    secondPressure
    (scaledOrthogonal spatialScale scalePositive.ne' orthogonal)
    translation point
  rw [scaledOrthogonal_apply] at affineDerivative
  exact affineDerivative.symm.trans derivativeRelation

/-- The round-axis clause removes the translation and spatial scale from the
physical Hessian law.  The returned ambient pressures are the smooth fields
that literally represent the two target representatives. -/
theorem fixed_pressureHessian_covariance_of_physicalSimilarity
    (first second : Representative) (cellLength : ℝ) (period : ℕ)
    (axisRadiusPositive : 0 < period * cellLength)
    (similarity : TargetPhysicalSimilarity.PhysicalSimilarity
      first second cellLength period) :
    ∃ (amplitude : ℝ) (orthogonal : Vec ≃ₗᵢ[ℝ] Vec)
      (firstPressure secondPressure : Vec → ℝ),
      amplitude ≠ 0 ∧
      SmoothNear (Set.range first.position) firstPressure ∧
      SmoothNear (Set.range second.position) secondPressure ∧
      (∀ point : Reference,
        firstPressure (first.position point) = first.pressure point) ∧
      (∀ point : Reference,
        secondPressure (second.position point) = second.pressure point) ∧
      orthogonal '' Set.range first.position = Set.range second.position ∧
      ∀ point ∈ interior (Set.range first.position),
        (pressureHessian secondPressure (orthogonal point)).compContinuousLinearMap
            (fun _ => orthogonal.toContinuousLinearMap) =
          amplitude ^ 2 • pressureHessian firstPressure point := by
  rcases similarity with
    ⟨spatialScale, amplitude, orthogonal, translation, pressureOffset,
      firstMagnetic, secondMagnetic, firstPressure, secondPressure,
      scalePositive, amplitudeNonzero,
      firstMagneticSmooth, firstPressureSmooth,
      secondMagneticSmooth, secondPressureSmooth,
      firstRepresents, secondRepresents,
      firstAxisInterior, secondAxisInterior,
      bodyEquality, axisEquality, magneticEquality, pressureEquality⟩
  have fixed := RoundAxisSimilarity.roundAxis_similarity_same_radius
    (period * cellLength) spatialScale orthogonal translation
    axisRadiusPositive scalePositive axisEquality
  rcases fixed with ⟨scaleOne, translationZero⟩
  subst spatialScale
  subst translation
  refine ⟨amplitude, orthogonal, firstPressure, secondPressure,
    amplitudeNonzero, firstPressureSmooth, secondPressureSmooth,
    fun point => (firstRepresents point).2,
    fun point => (secondRepresents point).2, ?_, ?_⟩
  · simpa using bodyEquality
  · intro point pointInterior
    have scaledOne :
        (scaledOrthogonal 1 one_ne_zero orthogonal).toContinuousLinearMap =
          orthogonal.toContinuousLinearMap := by
      ext direction
      simp
    simpa only [one_smul, zero_add, add_zero, scaledOne] using
      pressureHessian_scaled_covariance
      (Set.range first.position) firstPressure secondPressure
      1 amplitude orthogonal 0 pressureOffset zero_lt_one firstPressureSmooth
      (by simpa using pressureEquality) point pointInterior

end Grad.MainAssembly.PhysicalHessianCovariance
