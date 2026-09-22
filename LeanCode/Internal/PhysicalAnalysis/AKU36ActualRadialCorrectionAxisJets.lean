import AKU35OriginalPolynomialCoordinateDecomposition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearRadial Grad.NonlinearDivision

/-- The actual radial integral preserves any vanishing axis derivative.
This uses its genuine smooth integral and the exact dilation chain rule. -/
theorem radialIntervalJet_axis_derivative_zero {dimension order : ℕ}
    (field : ClosedJet dimension) (word : CartesianWord order)
    (vanishes : closedDerivative field order word closedOrigin = 0) :
    closedDerivative (radialIntervalJet 0 1 field) order word closedOrigin = 0 := by
  rw [radialIntervalJet,globalClosedJet_derivative]
  unfold radialIntervalValue
  have smooth : ContDiff ℝ ∞ (fun argument : SpatialPlane × ℝ =>
      smoothClosedExtension field (argument.2 • argument.1)) :=
    (smoothClosedExtension_smooth field).comp (contDiff_snd.smul contDiff_fst)
  rw [cartesianDerivative_weightedIntegral order word smooth
    Real.negMulLog Real.continuous_negMulLog 0 1]
  apply integral_eq_zero_of_ae
  filter_upwards with scale
  rw [cartesianDerivative_dilation scale _ (smoothClosedExtension_smooth field)]
  change Real.negMulLog scale • (scale ^ order •
    cartesianDerivative order word (smoothClosedExtension field) (scale • (0 : SpatialPlane))) = 0
  rw [smul_zero]
  have derivative := smoothClosedExtension_derivative field word closedOrigin
  change cartesianDerivative order word (smoothClosedExtension field) 0 = _ at derivative
  rw [derivative,vanishes,smul_zero,smul_zero]

theorem radialIntervalJet_originPartial_zero {dimension : ℕ} (field : ClosedJet dimension)
    (direction : Fin 2) (vanishes : originPartial direction field = 0) :
    originPartial direction (radialIntervalJet 0 1 field) = 0 :=
  radialIntervalJet_axis_derivative_zero field (fun _ => direction) vanishes

/-- The full radial correction always has zero first axis derivative:
the angular projection, Laplacian, and actual radial integral are retained. -/
theorem radialQuotientPost_first_zero {parameters : PhaseParameters}
    (field : ACore parameters 1) (direction : Fin 2) :
    traceFirst direction (radialQuotientPost parameters field) = 0 := by
  apply Subtype.ext
  funext cell
  change originPartial direction (radialIntervalJet 0 1
    ((laplacianCore parameters (angularCore parameters 0 field)).val cell)) = 0
  apply radialIntervalJet_originPartial_zero
  change originPartial direction (laplacianJet (angularClosedJet 0 (field.val cell))) = 0
  rw [Grad.CircularHighRegularity.laplacianJet_angular]
  exact angularJet_zero_originPartial direction _

/-- If the actual quadratic input jet vanishes, its radial correction
also has zero value at the axis. No pointwise remainder estimate is assumed. -/
theorem radialQuotientPost_origin_zero {parameters : PhaseParameters}
    (field : ACore parameters 1)
    (vanishes : ∀ first second, secondAxisTrace first second field = 0) :
    traceZero (radialQuotientPost parameters field) = 0 := by
  apply Subtype.ext
  funext cell
  change ((radialCore parameters (laplacianCore parameters (angularCore parameters 0 field))).val cell).value closedOrigin = 0
  apply (radialCore_origin parameters (laplacianCore parameters (angularCore parameters 0 field)) cell).trans
  rw [laplacianCore_actual]
  change (1/4 : ℝ) • closedLaplacianValue (angularClosedJet 0 (field.val cell)) closedOrigin = 0
  have angular : closedLaplacianValue (angularClosedJet 0 (field.val cell)) closedOrigin =
      closedLaplacianValue (field.val cell) closedOrigin := angularClosedJet_laplacian_origin (field.val cell)
  rw [angular]
  have second (direction : Fin 2) :
      closedDerivative (field.val cell) 2 (fun _ => direction) closedOrigin = 0 := by
    have equality := congrArg (fun axis : Grad.AxisCore.AxisSmoothCore parameters 1 => axis.val cell)
      (vanishes direction direction)
    change (Grad.GaugeCoefficients.Physical.Compensated.partialJet direction
      (Grad.GaugeCoefficients.Physical.Compensated.partialJet direction (field.val cell))).value closedOrigin = 0 at equality
    rw [doublePartial_eq_closedDerivative] at equality
    have words : (![direction,direction] : CartesianWord 2) = fun _ => direction := by
      funext index
      fin_cases index <;> rfl
    rwa [words] at equality
  rw [closedLaplacianValue,second 0,second 1,add_zero,smul_zero]

end Grad.FinitePhysicalJetLift
