import AKDZ1CanonicalRadialJetEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace Grad.OriginalCollarNorm
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift
open Grad.SourceCollarDivision Grad.SourceCollarRestriction Grad.SourceCollarCoefficients
open Grad.AnnularGeneralSourceRegularity Grad.OriginalRadialRecovery Grad.OriginalCartesianTameEstimate
open Grad.DiskExtension.Operator Grad.Constraints

/-- Full finite-cell polar tensor payment, fixed before the original core. -/
def canonicalPolarTensorConstant (lower : ℝ) (order : ℕ) : ℝ :=
  productWordCoefficientSum order * ∑ word : CartesianWord order,
    ‖productWordCoefficient word‖*((2*Real.pi)*(rawRadialEnergyConstant lower (polarWordCount word 0))^2)

theorem canonicalPolarTensorConstant_nonnegative (lower : ℝ) (order : ℕ) :
    0≤canonicalPolarTensorConstant lower order := by
  apply mul_nonneg (productWordCoefficientSum_nonnegative order)
  exact Finset.sum_nonneg (fun word _ => mul_nonneg (norm_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (sq_nonneg _)))

theorem polarTensorAngular_continuous {dimension : ℕ} (field : SpatialPlane→ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ field) (order : ℕ) :
    Continuous (fun radius : ℝ => ∫ angle in -Real.pi..Real.pi,
      ‖iteratedFDeriv ℝ order (field ∘ polarPlane) (radius,angle)‖^2) := by
  have continuousTensor := (smooth.comp polarPlane_smooth).continuous_iteratedFDeriv
    (by exact_mod_cast (le_top : (order : ℕ∞)≤⊤))
  exact timeIntegral_continuous
    (fun point : ℝ×ℝ => ‖iteratedFDeriv ℝ order (field ∘ polarPlane) (point.2,point.1)‖^2)
    ((continuousTensor.comp (continuous_snd.prodMk continuous_fst)).norm.pow 2)
    (-Real.pi) Real.pi (neg_le_self Real.pi_pos.le)

/-- Every finite axial support is summed before the full Fourier norm
energy is paid. The constant is independent of that finite support. -/
theorem canonicalPolarTensor_integral {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (order : ℕ)
    (core : ACore parameters dimension) (payment : ℝ) (paymentNonnegative : 0≤payment)
    (energy : ∀ power rank,power+rank≤order →
      (∫⁻ radius in Icc lower 1,ENNReal.ofReal
        (‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank
          (cartesianWeightedRadialCurve parameters lower positive bounded core power 0) radius‖^2))≤ENNReal.ofReal (payment^2))
    (cells : Finset ℤ) :
    (∑ cell∈cells,∫ radius in lower..1,∫ angle in -Real.pi..Real.pi,
      ‖iteratedFDeriv ℝ order (originalPolarValue (phaseWeightedJet parameters cell (core.val cell)))
        (radius,angle)‖^2)≤canonicalPolarTensorConstant lower order*payment^2 := by
  have firstContinuous (cell : ℤ) : Continuous (fun radius : ℝ => ∫ angle in -Real.pi..Real.pi,
      ‖iteratedFDeriv ℝ order (originalPolarValue (phaseWeightedJet parameters cell (core.val cell)))
        (radius,angle)‖^2) :=
    polarTensorAngular_continuous _ (smoothClosedExtension_smooth _) order
  have sumContinuous : Continuous (fun radius : ℝ => ∑ cell∈cells,∫ angle in -Real.pi..Real.pi,
      ‖iteratedFDeriv ℝ order (originalPolarValue (phaseWeightedJet parameters cell (core.val cell)))
        (radius,angle)‖^2) := continuous_finsetSum cells (fun cell _ => firstContinuous cell)
  have rawContinuous (word : CartesianWord order) : Continuous (fun radius : ℝ =>
      ‖cartesianWeightedRadialCurve parameters lower positive bounded core
        (polarWordCount word 1) (polarWordCount word 0) radius‖^2) :=
    (cartesianWeightedRadialCurve_continuous parameters lower positive bounded core _ _).norm.pow 2
  have secondContinuous : Continuous (fun radius : ℝ => productWordCoefficientSum order *
      ∑ word : CartesianWord order, ‖productWordCoefficient word‖*((2*Real.pi)*
        ‖cartesianWeightedRadialCurve parameters lower positive bounded core
          (polarWordCount word 1) (polarWordCount word 0) radius‖^2)) := by
    apply continuous_const.mul
    apply continuous_finsetSum
    intro word _
    exact continuous_const.mul (continuous_const.mul (rawContinuous word))
  have comparison := intervalIntegral.integral_mono_on (μ:=volume) bounded.le
    (sumContinuous.intervalIntegrable _ _) (secondContinuous.intervalIntegrable _ _)
    (fun radius inside => canonicalPolarTensor_energy parameters lower positive bounded core order radius inside cells)
  rw [intervalIntegral.integral_finsetSum (fun cell _ => (firstContinuous cell).intervalIntegrable lower 1),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum] at comparison
  swap
  · intro word _
    exact (continuous_const.mul (continuous_const.mul (rawContinuous word))).intervalIntegrable lower 1
  simp only [intervalIntegral.integral_const_mul] at comparison
  have paid := comparison.trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun word _ => mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (canonicalRadialJet_integral parameters lower positive bounded core (polarWordCount word 1) (polarWordCount word 0)
          payment paymentNonnegative (fun rank rankLe => energy _ rank (by have := polarWordCount_total word; omega)))
        (mul_nonneg (by norm_num) Real.pi_pos.le)) (norm_nonneg _)))
    (productWordCoefficientSum_nonnegative order))
  exact paid.trans_eq (by
    unfold canonicalPolarTensorConstant
    simp only [mul_pow,←mul_assoc,←Finset.sum_mul])

end Grad.OriginalCollarNorm
