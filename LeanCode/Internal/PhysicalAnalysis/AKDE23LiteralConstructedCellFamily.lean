import AKDE22ActualPhysicalC2Estimate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set
open scoped ContDiff
namespace Grad.OriginalCellFamily
open Grad.CartesianState Grad.ClosedJets Grad.Constraints Grad.PhysicalFamily Grad.MainTarget Grad.NonlinearQuotient
open Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}
    {inverse : OriginalNewtonInverse neighborhood cellLength loss}

namespace ConstructedParameterWindow
variable (scale : OriginalNewtonScale inverse) (window : ConstructedParameterWindow scale)

theorem halfRadius_mem {epsilon : ℝ} (member : epsilon ∈ Ioo (-window.radius/2) (window.radius/2)) :
    epsilon ∈ Ioo (-window.radius) window.radius :=
  ⟨by linarith [window.positive,member.1],by linarith [window.positive,member.2]⟩

/-- The literal CellSolutionFamily built from the SAME original Newton
limit. The zero-seed residual identity is consumed through the exact
zero-limit law; every field, equation and physical norm is constructed. -/
def cellFamily (leftLaw : inverse.LeftLaw)
    (zero : ∀ parameter ∈ Ioo window.parameterLower window.parameterUpper,
      scale.parameterLimit (cellFiniteParameter window.rho window.alpha window.delta 0 parameter)=0) : CellSolutionFamily cellLength where
  rho := window.rho
  alpha := window.alpha
  delta := window.delta
  lower := window.lower
  upper := window.upper
  parameterLower := window.parameterLower
  parameterUpper := window.parameterUpper
  epsilonZero := window.radius/2
  collarRadius := 4/3
  bound := (window.physicalC2_bound scale leftLaw zero).choose
  v := window.v scale
  w := window.w scale
  remainder := window.remainder scale
  tilt := window.tilt scale
  rhoPositive := window.rhoPositive
  rhoSmall := window.rhoSmall
  deltaNonzero := window.deltaNonzero
  alphaNonresonant := window.alphaNonresonant
  lowerPositive := window.lowerPositive
  intervalNontrivial := window.intervalNontrivial
  upperSmall := window.upperSmall
  parameterContains := window.parameterContains
  epsilonPositive := half_pos window.positive
  collarLarge := by norm_num
  boundAtLeastOne := (window.physicalC2_bound scale leftLaw zero).choose_spec.1
  vSmooth := (window.fields_smooth scale leftLaw).1.mono (fun _ member =>
    ⟨window.halfRadius_mem scale (by simpa only [neg_div] using member.1),member.2⟩)
  wSmooth := (window.fields_smooth scale leftLaw).2.1.mono (fun _ member =>
    ⟨window.halfRadius_mem scale (by simpa only [neg_div] using member.1),member.2⟩)
  remainderSmooth := (window.fields_smooth scale leftLaw).2.2.1.mono (fun _ member =>
    ⟨window.halfRadius_mem scale (by simpa only [neg_div] using member.1),member.2⟩)
  tiltSmooth := (window.fields_smooth scale leftLaw).2.2.2.mono (fun _ member =>
    ⟨window.halfRadius_mem scale (by simpa only [neg_div] using member.1),member.2⟩)
  vPeriodic := by
    intro epsilon _ parameter _ point _ time
    exact (constructedCellFields_periodic scale _ point time).1
  wPeriodic := by
    intro epsilon _ parameter _ point _ time
    exact (constructedCellFields_periodic scale _ point time).2.1
  remainderPeriodic := by
    intro epsilon _ parameter _ point _ time
    exact (constructedCellFields_periodic scale _ point time).2.2.2
  tiltPeriodic := by
    intro epsilon _ parameter _ time
    exact (constructedCellFields_periodic scale _ 0 time).2.2.1
  tiltBound := by
    intro epsilon epsilonIn parameter parameterIn time
    exact constructedTilt_bound scale _
      (window.included epsilon (window.halfRadius_mem scale (by simpa only [neg_div] using epsilonIn))
        parameter (window.parameter_mem scale parameterIn)) time
  normalizedChart := by
    intro epsilon _ parameter _ point _ time
    simpa [v,tilt,remainder,cellFiniteParameter] using constructedCell_normalized scale
      (cellFiniteParameter window.rho window.alpha window.delta epsilon parameter) point time
  remainderValueZero := by
    intro epsilon epsilonIn parameter parameterIn time
    exact constructedCellRemainder_zero_value scale _
      (window.included epsilon (window.halfRadius_mem scale (by simpa only [neg_div] using epsilonIn))
        parameter (window.parameter_mem scale parameterIn)) time
  remainderDerivativeZero := by
    intro epsilon epsilonIn parameter parameterIn time
    exact constructedCellRemainder_zero_derivative scale _
      (window.included epsilon (window.halfRadius_mem scale (by simpa only [neg_div] using epsilonIn))
        parameter (window.parameter_mem scale parameterIn)) time
  firstRowZero := by
    intro epsilon epsilonIn parameter parameterIn point pointIn time
    exact congrFun (constructedCellRows_zero scale _
      (window.included epsilon (window.halfRadius_mem scale (by simpa only [neg_div] using epsilonIn))
        parameter (window.parameter_mem scale parameterIn)) ⟨point,pointIn⟩ time) 0
  secondRowZero := by
    intro epsilon epsilonIn parameter parameterIn point pointIn time
    exact congrFun (constructedCellRows_zero scale _
      (window.included epsilon (window.halfRadius_mem scale (by simpa only [neg_div] using epsilonIn))
        parameter (window.parameter_mem scale parameterIn)) ⟨point,pointIn⟩ time) 1
  thirdRowZero := by
    intro epsilon epsilonIn parameter parameterIn point pointIn time
    exact congrFun (constructedCellRows_zero scale _
      (window.included epsilon (window.halfRadius_mem scale (by simpa only [neg_div] using epsilonIn))
        parameter (window.parameter_mem scale parameterIn)) ⟨point,pointIn⟩ time) 2
  fourthRowZero := by
    intro epsilon epsilonIn parameter parameterIn point pointIn time
    exact congrFun (constructedCellRows_zero scale _
      (window.included epsilon (window.halfRadius_mem scale (by simpa only [neg_div] using epsilonIn))
        parameter (window.parameter_mem scale parameterIn)) ⟨point,pointIn⟩ time) 3
  physicalC2Estimate := by
    intro epsilon epsilonIn parameter parameterIn
    exact (window.physicalC2_bound scale leftLaw zero).choose_spec.2 epsilon
      (abs_le.mpr ⟨by linarith [epsilonIn.1],epsilonIn.2.le⟩) parameter parameterIn

end ConstructedParameterWindow
end Grad.OriginalCellFamily
