import AKDE21OriginalParameterWindow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff
namespace Grad.OriginalCellFamily
open Grad.CartesianState Grad.Constraints Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}
    {inverse : OriginalNewtonInverse neighborhood cellLength loss}

/-- The fixed epsilon/lambda rectangle is constructed by openness around
one actual zero seed. The analytic width and physical collar stay fixed. -/
theorem exists_constructedParameterWindow (scale : OriginalNewtonScale inverse)
    (rho alpha delta parameter : ℝ) (rhoPositive : 0 < rho) (rhoSmall : rho < 1/4)
    (deltaNonzero : delta ≠ 0)
    (alphaNonresonant : ∀ multiple : ℤ, alpha ≠ (Real.pi/2)*(multiple:ℝ))
    (parameterPositive : 0 < parameter) (parameterSmall : parameter < 1/2)
    (member : cellFiniteParameter rho alpha delta 0 parameter ∈ scale.openParameterDomain) :
    Nonempty (ConstructedParameterWindow scale) := by
  let patch := (fun point : ℝ × ℝ => cellFiniteParameter rho alpha delta point.1 point.2) ⁻¹' scale.openParameterDomain
  have patchOpen : IsOpen patch := scale.openParameterDomain_isOpen.preimage (cellFiniteParameter_smooth rho alpha delta).continuous
  obtain ⟨radius,radiusPositive,ballIncluded⟩ := Metric.isOpen_iff.mp patchOpen (0,parameter) member
  let deltaRadius := min (radius/2) (min (parameter/2) ((1/2-parameter)/2))
  have deltaPositive : 0 < deltaRadius := lt_min (half_pos radiusPositive)
    (lt_min (half_pos parameterPositive) (by linarith))
  have deltaRadius_le : deltaRadius ≤ radius/2 := min_le_left _ _
  have deltaParameter_le : deltaRadius ≤ parameter/2 := (min_le_right _ _).trans (min_le_left _ _)
  have deltaUpper_le : deltaRadius ≤ (1/2-parameter)/2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨{
    rho := rho, alpha := alpha, delta := delta,
    lower := parameter-deltaRadius/2, upper := parameter+deltaRadius/2,
    parameterLower := parameter-deltaRadius, parameterUpper := parameter+deltaRadius,
    radius := radius/2, rhoPositive := rhoPositive, rhoSmall := rhoSmall,
    deltaNonzero := deltaNonzero, alphaNonresonant := alphaNonresonant,
    lowerPositive := by linarith,
    intervalNontrivial := by linarith,
    upperSmall := by linarith,
    parameterContains := ⟨by linarith,by linarith⟩,
    positive := half_pos radiusPositive,
    included := ?_ }⟩
  intro epsilon epsilonIn query queryIn
  change (epsilon,query) ∈ patch
  apply ballIncluded
  rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq,sub_zero]
  apply max_lt
  · have small : |epsilon| < radius/2 := abs_lt.mpr ⟨by linarith [epsilonIn.1],epsilonIn.2⟩
    exact small.trans (by linarith)
  · have small : |query-parameter| < deltaRadius := abs_lt.mpr ⟨by linarith [queryIn.1],by linarith [queryIn.2]⟩
    exact small.trans_le (deltaRadius_le.trans (by linarith))

end Grad.OriginalCellFamily
