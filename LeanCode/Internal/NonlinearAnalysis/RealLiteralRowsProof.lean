import RealRowBridge

noncomputable section

open Set
open scoped ContDiff

namespace Grad.NonlinearQuotient

open Grad.MainTarget Grad.PhysicalFamily Grad.Constraints

theorem complexRawRows_complexify (cellLength epsilon : ℝ)
    {mapping : Plane → ℝ → Vec} {potential : Plane → ℝ → ℝ} {radius : ℝ}
    (mappingSmooth : ContDiffOn ℝ ∞ (Function.uncurry mapping) (Metric.ball 0 radius ×ˢ univ))
    (potentialSmooth : ContDiffOn ℝ ∞ (Function.uncurry potential) (Metric.ball 0 radius ×ˢ univ))
    (point : Plane) (pointIn : point ∈ Metric.ball (0 : Plane) radius) (time : ℝ) :
    complexRawRows cellLength epsilon (complexifyMapping mapping) (complexifyPotential potential) point time =
      fun row => (actualRealRawRows cellLength epsilon mapping potential point time row : ℂ) := by
  have mappingSpatial (argument : Plane) (argumentIn : argument ∈ Metric.ball (0 : Plane) radius) (cellTime : ℝ) :=
    ((cellSection_smooth mappingSmooth cellTime).contDiffAt
      (Metric.isOpen_ball.mem_nhds argumentIn)).differentiableAt (by simp)
  have potentialSpatial (argument : Plane) (argumentIn : argument ∈ Metric.ball (0 : Plane) radius) (cellTime : ℝ) :=
    ((cellSection_smooth potentialSmooth cellTime).contDiffAt
      (Metric.isOpen_ball.mem_nhds argumentIn)).differentiableAt (by simp)
  have mappingEuler argument argumentIn cellTime :=
    diskEuler_postcompose complexifyVecCLM mapping argument cellTime (mappingSpatial argument argumentIn cellTime)
  have mappingAngular argument argumentIn cellTime :=
    diskAngular_postcompose complexifyVecCLM mapping argument cellTime (mappingSpatial argument argumentIn cellTime)
  have potentialEuler argument argumentIn cellTime :=
    diskEuler_postcompose Complex.ofRealCLM potential argument cellTime (potentialSpatial argument argumentIn cellTime)
  have potentialAngular argument argumentIn cellTime :=
    diskAngular_postcompose Complex.ofRealCLM potential argument cellTime (potentialSpatial argument argumentIn cellTime)
  have mappingAffine argument argumentIn cellTime :=
    complexAffineStateDerivative_complexify cellLength epsilon mapping argument cellTime
      ((timeSection_smooth mappingSmooth argumentIn).contDiffAt.differentiableAt (by simp))
  have potentialTime argument argumentIn cellTime :=
    cellDerivative_postcompose Complex.ofRealCLM potential argument cellTime
      ((timeSection_smooth potentialSmooth argumentIn).contDiffAt.differentiableAt (by simp))
  funext row
  fin_cases row
  · change diskAngular (complexifyPotential potential) point time -
        complexDot (diskAngular (complexifyMapping mapping) point time)
          (diskAngular (complexifyMapping mapping) point time) + (‖point‖ ^ 2 : ℝ) =
      (firstCellRow mapping potential point time : ℂ)
    change diskAngular (fun p t => Complex.ofRealCLM (potential p t)) point time -
        complexDot (diskAngular (fun p t => complexifyVecCLM (mapping p t)) point time)
          (diskAngular (fun p t => complexifyVecCLM (mapping p t)) point time) + (‖point‖ ^ 2 : ℝ) = _
    rw [potentialAngular point pointIn time, mappingAngular point pointIn time]
    simp [complexDot_complexify, firstCellRow]
  · change complexRemoveAngularAverage (fun argument cellTime =>
        diskEuler (complexifyPotential potential) argument cellTime -
          complexDot (diskEuler (complexifyMapping mapping) argument cellTime)
            (diskAngular (complexifyMapping mapping) argument cellTime)) point time =
      (secondCellRow mapping potential point time : ℂ)
    apply complexRemoveAngularAverage_ofReal (radius := radius) _ point pointIn time
    intro argument argumentIn cellTime
    change diskEuler (fun p t => Complex.ofRealCLM (potential p t)) argument cellTime -
        complexDot (diskEuler (fun p t => complexifyVecCLM (mapping p t)) argument cellTime)
          (diskAngular (fun p t => complexifyVecCLM (mapping p t)) argument cellTime) = _
    rw [potentialEuler argument argumentIn cellTime, mappingEuler argument argumentIn cellTime,
      mappingAngular argument argumentIn cellTime]
    simp [complexDot_complexify]
  · change complexRemoveAngularAverage (fun argument cellTime =>
        complexDot (diskAngular (complexifyMapping mapping) argument cellTime)
          (complexAffineStateDerivative cellLength epsilon (complexifyMapping mapping) argument cellTime) -
        cellDerivative (complexifyPotential potential) argument cellTime) point time =
      (thirdCellRow cellLength epsilon mapping potential point time : ℂ)
    apply complexRemoveAngularAverage_ofReal (radius := radius) _ point pointIn time
    intro argument argumentIn cellTime
    rw [mappingAffine argument argumentIn cellTime]
    change complexDot (diskAngular (fun p t => complexifyVecCLM (mapping p t)) argument cellTime) _ -
        cellDerivative (fun p t => Complex.ofRealCLM (potential p t)) argument cellTime = _
    rw [mappingAngular argument argumentIn cellTime, potentialTime argument argumentIn cellTime]
    simp [complexDot_complexify]
  · change complexRemoveAngularAverage (fun argument cellTime =>
        complexDeterminant (diskEuler (complexifyMapping mapping) argument cellTime)
          (diskAngular (complexifyMapping mapping) argument cellTime)
          (complexAffineStateDerivative cellLength epsilon (complexifyMapping mapping) argument cellTime)) point time =
      (fourthCellRow cellLength epsilon mapping point time : ℂ)
    apply complexRemoveAngularAverage_ofReal (radius := radius) _ point pointIn time
    intro argument argumentIn cellTime
    rw [mappingAffine argument argumentIn cellTime]
    change complexDeterminant (diskEuler (fun p t => complexifyVecCLM (mapping p t)) argument cellTime)
        (diskAngular (fun p t => complexifyVecCLM (mapping p t)) argument cellTime) _ = _
    rw [mappingEuler argument argumentIn cellTime, mappingAngular argument argumentIn cellTime]
    exact complexDeterminant_complexify _ _ _

/-- Actual-project literal-row consumer for constructing a cell solution from
the constrained potential space. No angular gauge is inferred from a supplied
CellSolutionFamily, whose prior contract deliberately does not store that gauge. -/
theorem realLiteralRows : RealLiteralRowsGoal := by
  intro cellLength epsilon radius mapping potential radiusLarge mappingSmooth potentialSmooth meanZero point pointBound time
  have mappingComplexSmooth : ContDiffOn ℝ ∞ (Function.uncurry (complexifyMapping mapping))
      (Metric.ball 0 radius ×ˢ univ) :=
    complexifyVecCLM.contDiff.comp_contDiffOn mappingSmooth
  have potentialComplexSmooth : ContDiffOn ℝ ∞ (Function.uncurry (complexifyPotential potential))
      (Metric.ball 0 radius ×ˢ univ) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn potentialSmooth
  have meanComplexZero : ∀ argument ∈ Metric.ball (0 : Plane) radius, ∀ cellTime,
      complexAngularAverage (complexifyPotential potential) argument cellTime = 0 := by
    intro argument argumentIn cellTime
    rw [complexAngularAverage_ofReal, meanZero argument argumentIn cellTime, Complex.ofReal_zero]
  have pointIn : point ∈ Metric.ball (0 : Plane) radius := by
    simpa [Metric.mem_ball, dist_zero_right] using pointBound.trans_lt radiusLarge
  exact (literalRows cellLength epsilon radius (complexifyMapping mapping) (complexifyPotential potential)
    radiusLarge mappingComplexSmooth potentialComplexSmooth meanComplexZero point pointBound time).trans
      (complexRawRows_complexify cellLength epsilon mappingSmooth potentialSmooth point pointIn time)

end Grad.NonlinearQuotient
