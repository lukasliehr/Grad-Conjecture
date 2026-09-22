import AKDT5BoundaryOrbit

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient Grad.PhysicalEquilibrium
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledConfigurationRegularity Grad.PhysicalFamily.SampledFullGeometry
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian
open Grad.PhysicalFamily.SampledGlobalEmbedding Grad.NonlinearQuotient

variable (length : ℝ) (family : CellSolutionFamily length) (period : ℕ)
  (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
  (potential : ℝ) (parameter : Icc family.lower family.upper)
  (valid : IsConfiguration .smooth (sampledRepresentativeFamily length family period epsilonIn potential parameter))
  (injective : ∀ (point : Plane), ‖point‖ ≤ 1 → ∀ time : ℝ,
    Function.Injective (fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val)
      (coordinateDirection point time)))
  (magnetic : Vec → Vec)
  (same : ∀ argument,
    magnetic ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
      (sampledRepresentativeFamily length family period epsilonIn potential parameter).magnetic argument)

include valid injective same

/-- A full smooth rotation orbit in the actual physical frontier realizes the
canonical magnetic vector as the tangent required by the literal target. -/
theorem actual_boundary_tangent_cover (argument : ClosedDisk × ℝ) (onBoundary : ‖argument.1.val‖ = 1) :
    let configuration := sampledRepresentativeFamily length family period epsilonIn potential parameter
    TangentTo (frontier (range configuration.position)) (configuration.position (referenceCover argument))
      (magnetic (configuration.position (referenceCover argument))) := by
  let position := sampledPositionCoordinateValue length family period parameter.val
  let curve : ℝ → Vec := fun angle => position (coordinateDirection (planeRotationAction angle argument.1.val) argument.2)
  have positionSmooth := (sampled_actual_lifts_smooth length family period epsilonIn potential parameter).1
  have orbitIn (angle : ℝ) : coordinateDirection (planeRotationAction angle argument.1.val) argument.2 ∈ sampledAmbientCollar family := by
    apply sampledAmbientCollar_contains family
    change ‖planarPart (coordinateDirection _ _)‖ ≤ 1
    rw [planarPart_coordinateDirection, diskOrbit_norm]
    exact argument.1.property
  have curveSmooth : ContDiff ℝ ∞ curve := by
    apply contDiff_iff_contDiffAt.mpr
    intro angle
    have outer : ContDiffAt ℝ ∞ position (coordinateDirection (planeRotationAction angle argument.1.val) argument.2) :=
      positionSmooth.contDiffAt ((sampledAmbientCollar_isOpen family).mem_nhds (orbitIn angle))
    have composed := outer.comp angle (physicalDiskOrbit_smooth argument.1.val argument.2).contDiffAt
    exact composed
  have positionSame := (sampled_actual_lifts_values length family period epsilonIn potential parameter argument).1
  have curveZero : curve 0 = (sampledRepresentativeFamily length family period epsilonIn potential parameter).position (referenceCover argument) := by
    change position (coordinateDirection (planeRotationAction 0 argument.1.val) argument.2) = _
    rw [planeRotationAction_zero]
    exact positionSame
  refine ⟨curve, curveSmooth, curveZero, ?_, ?_⟩
  · intro angle
    let orbitArgument : ClosedDisk × ℝ :=
      (⟨planeRotationAction angle argument.1.val, by rw [diskOrbit_norm]; exact argument.1.property⟩, argument.2)
    have boundary := (actual_position_interior_frontier length family period epsilonIn potential parameter
      valid injective orbitArgument).2.mpr (by change ‖planeRotationAction angle argument.1.val‖ = 1; rw [diskOrbit_norm, onBoundary])
    have orbitSame := (sampled_actual_lifts_values length family period epsilonIn potential parameter orbitArgument).1
    change position (referenceCoverPoint orbitArgument) = _ at orbitSame
    change position (referenceCoverPoint orbitArgument) ∈ _
    rwa [orbitSame]
  · have positionDerivative : HasFDerivAt position
        (fderiv ℝ position (coordinateDirection argument.1.val argument.2))
        (coordinateDirection (planeRotationAction 0 argument.1.val) argument.2) := by
      rw [planeRotationAction_zero]
      exact ((positionSmooth.contDiffAt ((sampledAmbientCollar_isOpen family).mem_nhds
        (sampledAmbientCollar_contains family (referenceCoverPoint_mem argument)))).differentiableAt (by simp)).hasFDerivAt
    have derivative := positionDerivative.comp_hasDerivAt 0
      (physicalDiskOrbit_hasDerivAt argument.1.val argument.2)
    have value : fderiv ℝ position (coordinateDirection argument.1.val argument.2)
        (coordinateDirection (planeQuarterTurn argument.1.val) 0) =
        magnetic ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position (referenceCover argument)) := by
      rw [actualMagneticLift_pushforward length family period epsilonIn parameter argument.1.val argument.1.property argument.2]
      rw [show coordinateDirection argument.1.val argument.2 = referenceCoverPoint argument from rfl,
        actualMagneticLift_values length family period epsilonIn potential parameter argument, same]
    rw [value] at derivative
    simpa only [curve, Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      congrArg (fun linear : ℝ →L[ℝ] Vec => linear 1) derivative.hasFDerivAt.fderiv

/-- Literal boundary tangency at every point of the SAME compact body. -/
theorem actual_boundary_tangent :
    let configuration := sampledRepresentativeFamily length family period epsilonIn potential parameter
    ∀ point ∈ frontier (range configuration.position), TangentTo (frontier (range configuration.position)) point (magnetic point) := by
  dsimp only
  intro point pointIn
  have bodyClosed : IsClosed (range (sampledRepresentativeFamily length family period epsilonIn potential parameter).position) := by
    simpa only [image_univ] using (reference_isCompact.image valid.1.2.1.continuous).isClosed
  have bodyIn := frontier_subset_closure pointIn
  rw [bodyClosed.closure_eq] at bodyIn
  obtain ⟨reference, rfl⟩ := bodyIn
  obtain ⟨argument, rfl⟩ := referenceCover_surjective reference
  have boundary := (actual_position_interior_frontier length family period epsilonIn potential parameter valid injective argument).2.mp pointIn
  exact actual_boundary_tangent_cover length family period epsilonIn potential parameter valid injective magnetic same argument boundary

end Grad.PhysicalGeometry
