import AKDN48LinearEulerEnergyAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.OriginalCartesianTameEstimate

section Signed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorEulerWithin_sub (domain : Set ℝ) (unique : UniqueDiffOn ℝ domain)
    (first second : ℝ → E) (rank : ℕ)
    (firstSmooth : ContDiffOn ℝ rank first domain) (secondSmooth : ContDiffOn ℝ rank second domain)
    (radius : ℝ) (inside : radius ∈ domain) :
    vectorEulerWithinIteratedDerivative domain rank (fun point => first point-second point) radius =
      vectorEulerWithinIteratedDerivative domain rank first radius-
        vectorEulerWithinIteratedDerivative domain rank second radius := by
  let difference := ContinuousLinearMap.fst ℝ E E-ContinuousLinearMap.snd ℝ E E
  have observed := vectorEulerWithin_observation domain unique (fun point => (first point,second point))
    difference rank (firstSmooth.prodMk secondSmooth) inside
  change vectorEulerWithinIteratedDerivative domain rank (fun point => first point-second point) radius = _ at observed
  dsimp only at observed
  rw [vectorEulerWithin_pair domain unique first second rank firstSmooth secondSmooth radius inside] at observed
  exact observed

theorem eulerCurve_squareEnergy_sub (lower : ℝ) (bounded : lower < 1) (first second : ℝ → E)
    (rank : ℕ) (firstSmooth : ContDiffOn ℝ rank first (Icc lower 1))
    (secondSmooth : ContDiffOn ℝ rank second (Icc lower 1)) (weight firstPayment secondPayment : ℝ)
    (first0 : 0 ≤ firstPayment) (second0 : 0 ≤ secondPayment)
    (firstEnergy : (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank first radius‖^2)) ≤ ENNReal.ofReal (firstPayment^2))
    (secondEnergy : (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank second radius‖^2)) ≤ ENNReal.ofReal (secondPayment^2)) :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank (fun point => first point-second point) radius‖^2)) ≤
      ENNReal.ofReal ((2*(firstPayment+secondPayment))^2) := by
  have actual := twoInput_squareEnergy (volume.restrict (Icc lower 1))
    (fun radius => weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank (fun point => first point-second point) radius)
    (fun radius => weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank first radius)
    (fun radius => weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank second radius)
    ((weightedEuler_continuous lower bounded first rank firstSmooth weight).aestronglyMeasurable measurableSet_Icc)
    ((weightedEuler_continuous lower bounded second rank secondSmooth weight).aestronglyMeasurable measurableSet_Icc)
    1 1 firstPayment secondPayment zero_le_one zero_le_one first0 second0 (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
      rw [vectorEulerWithin_sub (Icc lower 1) (uniqueDiffOn_Icc bounded) first second rank firstSmooth secondSmooth radius inside,
        smul_sub,one_mul,one_mul]
      exact norm_sub_le _ _) firstEnergy secondEnergy
  simpa only [one_mul,mul_one] using actual

end Signed
end Grad.OriginalCartesianTameEstimate
