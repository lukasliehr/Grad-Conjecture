import AKDN45ActualPhysicalPrimitiveEnergy
import AKDN47ActualRadiusSourceEnergy
import AKDN38ActualThirdSourceExpansion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.OriginalCartesianTameEstimate

section Assembly
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem weightedEuler_continuous (lower : ℝ) (bounded : lower < 1) (curve : ℝ → E)
    (rank : ℕ) (smooth : ContDiffOn ℝ rank curve (Icc lower 1)) (weight : ℝ) :
    ContinuousOn (fun radius => weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank curve radius) (Icc lower 1) :=
  ((vectorEulerWithin_smooth (Icc lower 1) (uniqueDiffOn_Icc bounded) curve rank 0
    (by simpa only [Nat.zero_add] using smooth)).continuousOn).const_smul weight

theorem eulerCurve_squareEnergy_congr (lower : ℝ) (first second : ℝ → E)
    (same : EqOn first second (Icc lower 1)) (rank : ℕ) (weight : ℝ) :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank first radius‖^2)) =
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank second radius‖^2)) := by
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
  rw [vectorEulerWithin_congr (Icc lower 1) rank first second same inside]

theorem eulerCurve_squareEnergy_add (lower : ℝ) (bounded : lower < 1) (first second : ℝ → E)
    (rank : ℕ) (firstSmooth : ContDiffOn ℝ rank first (Icc lower 1))
    (secondSmooth : ContDiffOn ℝ rank second (Icc lower 1)) (weight firstPayment secondPayment : ℝ)
    (first0 : 0 ≤ firstPayment) (second0 : 0 ≤ secondPayment)
    (firstEnergy : (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank first radius‖^2)) ≤ ENNReal.ofReal (firstPayment^2))
    (secondEnergy : (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank second radius‖^2)) ≤ ENNReal.ofReal (secondPayment^2)) :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank (fun point => first point+second point) radius‖^2)) ≤
      ENNReal.ofReal ((2*(firstPayment+secondPayment))^2) := by
  have actual := twoInput_squareEnergy (volume.restrict (Icc lower 1))
    (fun radius => weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank (fun point => first point+second point) radius)
    (fun radius => weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank first radius)
    (fun radius => weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank second radius)
    ((weightedEuler_continuous lower bounded first rank firstSmooth weight).aestronglyMeasurable measurableSet_Icc)
    ((weightedEuler_continuous lower bounded second rank secondSmooth weight).aestronglyMeasurable measurableSet_Icc)
    1 1 firstPayment secondPayment zero_le_one zero_le_one first0 second0 (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
      rw [vectorEulerWithin_add (Icc lower 1) (uniqueDiffOn_Icc bounded) first second rank firstSmooth secondSmooth radius inside,
        smul_add,one_mul,one_mul]
      exact norm_add_le _ _) firstEnergy secondEnergy
  simpa only [one_mul,mul_one] using actual

theorem eulerCurve_squareEnergy_observation (lower : ℝ) (bounded : lower < 1) (curve : ℝ → E)
    (rank : ℕ) (smooth : ContDiffOn ℝ rank curve (Icc lower 1))
    (mapping : E →L[ℝ] F) (weight payment : ℝ)
    (energy : (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank curve radius‖^2)) ≤ ENNReal.ofReal (payment^2)) :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank (fun point => mapping (curve point)) radius‖^2)) ≤
      ENNReal.ofReal ((‖mapping‖*payment)^2) := by
  have actual := dominated_squareEnergy (volume.restrict (Icc lower 1))
    (fun radius => weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank (fun point => mapping (curve point)) radius)
    (fun radius => ‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank curve radius‖)
    ‖mapping‖ payment (norm_nonneg _) (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
      rw [vectorEulerWithin_observation (Icc lower 1) (uniqueDiffOn_Icc bounded) curve mapping rank smooth inside,←map_smul]
      exact mapping.le_opNorm _) (by simpa only [norm_norm] using energy)
  exact actual

end Assembly
end Grad.OriginalCartesianTameEstimate
