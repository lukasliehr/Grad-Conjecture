import SampledConfigurationRegularity
import SampledAxisBasics
import Mathlib.Analysis.Calculus.TangentCone.Real

noncomputable section

open Set
open scoped ContDiff

namespace Grad.PhysicalFamily.SampledPositionDerivative

open Grad.MainTarget
open Grad.PhysicalFamily
open Grad.PhysicalFamily.IntegerSampling
open Grad.PhysicalFamily.SampledSmoothFamily
open Grad.MainAssembly.SampledAxisBasics

/-- The stored normalized-chart identity may be differentiated on the exact
closed disk, including at its boundary, using the relative derivative. -/
theorem v_fderivWithin_closedDisk_eq_normalizedChart
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (time : ℝ) (point : Plane) (pointIn : ‖point‖ ≤ 1) :
    fderivWithin ℝ (fun argument : Plane =>
        family.v epsilon parameter.val argument time)
      (Metric.closedBall 0 1) point =
    fderivWithin ℝ (fun argument : Plane =>
        normalizedFactor (family.tilt epsilon parameter.val time) •
            planeEmbedding
              (seedAction family.rho family.alpha family.delta parameter.val
                time argument) +
          planeDot (family.tilt epsilon parameter.val time) argument •
            tangentDirection +
          family.remainder epsilon parameter.val argument time)
      (Metric.closedBall 0 1) point := by
  apply fderivWithin_congr'
  intro argument argumentIn
  apply family.normalizedChart epsilon epsilonIn parameter.val
    parameter.property argument
  simpa [Metric.mem_closedBall, dist_zero_right] using argumentIn
  simpa [Metric.mem_closedBall, dist_zero_right] using pointIn

/-- The ambient disk derivative of the exact cell chart is its literal linear
normalized seed/tilt part plus the ambient derivative of the remainder.  The
closed-disk hypothesis is sufficient even at the boundary because the stored
functions are smooth on a common open collar and the closed ball is a unique
differentiability set. -/
theorem v_fderiv_closedDisk_eq_axis_add_remainder
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (time : ℝ) (point : Plane) (pointIn : ‖point‖ ≤ 1) :
    fderiv ℝ (fun argument : Plane =>
        family.v epsilon parameter.val argument time) point =
      cellAxisCLM family.rho family.alpha family.delta parameter.val time
          (normalizedFactor (family.tilt epsilon parameter.val time))
          (family.tilt epsilon parameter.val time) +
        fderiv ℝ (fun argument : Plane =>
          family.remainder epsilon parameter.val argument time) point := by
  let diskSection : Plane → CellArgument := fun argument =>
    (epsilon, (parameter.val, coordinatePoint argument time))
  have inputIn : diskSection point ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
        (Set.Ioo family.parameterLower family.parameterUpper ×ˢ
          coordinateCollar family.collarRadius) := by
    refine ⟨epsilonIn, parameter_mem_open cellLength family parameter, ?_⟩
    change ‖coordinateDisk (coordinatePoint point time)‖ < family.collarRadius
    rw [coordinateDisk_coordinatePoint]
    exact lt_of_le_of_lt pointIn family.collarLarge
  have domainOpen : IsOpen
      (Set.Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
        (Set.Ioo family.parameterLower family.parameterUpper ×ˢ
          coordinateCollar family.collarRadius)) :=
    isOpen_Ioo.prod (isOpen_Ioo.prod
      (coordinateCollar_isOpen family.collarRadius))
  have sectionSmooth : ContDiff ℝ ∞ diskSection := by
    have timeSmooth : ContDiff ℝ ∞ (fun _ : Plane => time) := contDiff_const
    have pointSmooth : ContDiff ℝ ∞
        (fun argument : Plane => coordinatePoint argument time) := by
      simpa [Function.comp_def] using coordinatePoint_uncurried_contDiff.comp
        (contDiff_id.prodMk timeSmooth)
    exact contDiff_const.prodMk (contDiff_const.prodMk pointSmooth)
  have vDifferentiable : DifferentiableAt ℝ
      (fun argument : Plane => family.v epsilon parameter.val argument time)
      point := by
    have outer := family.vSmooth.contDiffAt (domainOpen.mem_nhds inputIn)
      |>.differentiableAt (by simp)
    have composed := outer.comp point
      ((sectionSmooth.differentiable (by simp)).differentiableAt)
    simpa [Function.comp_def, uncurriedCell, diskSection] using composed
  have remainderDifferentiable : DifferentiableAt ℝ
      (fun argument : Plane =>
        family.remainder epsilon parameter.val argument time) point := by
    have outer := family.remainderSmooth.contDiffAt
      (domainOpen.mem_nhds inputIn) |>.differentiableAt (by simp)
    have composed := outer.comp point
      ((sectionSmooth.differentiable (by simp)).differentiableAt)
    simpa [Function.comp_def, uncurriedCell, diskSection] using composed
  let axisMap := cellAxisCLM family.rho family.alpha family.delta parameter.val
    time (normalizedFactor (family.tilt epsilon parameter.val time))
      (family.tilt epsilon parameter.val time)
  have chartDifferentiable : DifferentiableAt ℝ
      (fun argument : Plane => axisMap argument +
        family.remainder epsilon parameter.val argument time) point :=
    axisMap.differentiableAt.add remainderDifferentiable
  have uniqueDiff : UniqueDiffWithinAt ℝ (Metric.closedBall (0 : Plane) 1)
      point := by
    apply uniqueDiffWithinAt_convex (convex_closedBall (0 : Plane) 1)
    · exact ⟨0, Metric.ball_subset_interior_closedBall (by simp)⟩
    · exact subset_closure (by
        simpa [Metric.mem_closedBall, dist_zero_right] using pointIn)
  have withinEquality := v_fderivWithin_closedDisk_eq_normalizedChart
    cellLength family epsilon epsilonIn parameter time point pointIn
  change fderivWithin ℝ
      (fun argument : Plane => family.v epsilon parameter.val argument time)
        (Metric.closedBall 0 1) point =
    fderivWithin ℝ
      (fun argument : Plane => axisMap argument +
        family.remainder epsilon parameter.val argument time)
        (Metric.closedBall 0 1) point at withinEquality
  rw [fderivWithin_eq_fderiv uniqueDiff vDifferentiable,
    fderivWithin_eq_fderiv uniqueDiff chartDifferentiable] at withinEquality
  rw [withinEquality]
  have sumDerivative := fderiv_add axisMap.differentiableAt
    remainderDifferentiable
  change fderiv ℝ (fun argument : Plane => axisMap argument +
      family.remainder epsilon parameter.val argument time) point =
    fderiv ℝ axisMap point +
      fderiv ℝ (fun argument : Plane =>
        family.remainder epsilon parameter.val argument time) point
      at sumDerivative
  rw [sumDerivative, axisMap.fderiv]

/-- On the target cylinder the relative derivative of the descended sampled
position is exactly the relative derivative of its literal real lift. -/
theorem periodicLift_position_fderivWithin_eq_sampled
    (cellLength : ℝ) (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Set.Icc family.lower family.upper)
    (point : Vec) (pointIn : point ∈ cylinder) :
    fderivWithin ℝ
        (periodicLift
          (sampledRepresentativeFamily cellLength family period epsilonIn
            potential parameter).position)
        cylinder point =
      fderivWithin ℝ
        (fun argument : Vec =>
          sampledPositionLift cellLength family period parameter.val
            (planarPart argument) (argument 2))
        cylinder point := by
  apply fderivWithin_congr'
  intro argument argumentIn
  exact periodicLift_sampledRepresentativeExtension_position cellLength family
    period epsilonIn potential parameter.val
      (parameter_mem_open cellLength family parameter) argument argumentIn
  exact pointIn

end Grad.PhysicalFamily.SampledPositionDerivative
