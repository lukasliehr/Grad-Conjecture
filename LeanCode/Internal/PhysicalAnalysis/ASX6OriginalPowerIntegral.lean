import ASX5OriginalDilationDerivative

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotient Grad.NonlinearRadial
open Grad.RepresentedKernel.SpatialProduct Grad.ActualCenterVolterra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.AnalyticWeights.Calculus

def originalWeightedDilationJoint {dimension : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (field : ClosedJet dimension) (argument : SpatialPlane × ℝ) : ComplexEuclidean dimension :=
  physicalWeight sigma gamma ell cell argument.1 • smoothClosedExtension field (argument.2 • argument.1)

theorem originalWeightedDilationJoint_smooth {dimension : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (field : ClosedJet dimension) : ContDiff ℝ ∞ (originalWeightedDilationJoint sigma gamma ell cell field) :=
  (((smoothGoal sigma gamma ell cell).2.1).comp contDiff_fst).smul
    ((smoothClosedExtension_smooth field).comp (contDiff_snd.smul contDiff_fst))

theorem originalWeightedDilationJoint_restricts {dimension : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (field : ClosedJet dimension) (scale : ℝ) :
    globalClosedJet (fun point => originalWeightedDilationJoint sigma gamma ell cell field (point, scale))
      ((originalWeightedDilationJoint_smooth sigma gamma ell cell field).comp (contDiff_id.prodMk contDiff_const)) =
      apWeightedJet sigma gamma ell cell (dilationJet scale field) := by
  apply globalClosedJet_eq_of_restriction
  intro point
  rw [apWeightedJet_value]
  rfl

theorem originalWeightedDilationJoint_derivative {dimension rank : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (field : ClosedJet dimension) (scale : ℝ) (word : CartesianWord rank) (point : ClosedDisk) :
    cartesianDerivative rank word (fun source => originalWeightedDilationJoint sigma gamma ell cell field (source, scale)) point.val =
      closedDerivative (apWeightedJet sigma gamma ell cell (dilationJet scale field)) rank word point := by
  rw [← originalWeightedDilationJoint_restricts sigma gamma ell cell field scale, globalClosedJet_derivative]

theorem originalWeightedPower_restricts {dimension : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (power : ℕ) (field : ClosedJet dimension) :
    globalClosedJet
      (fun point => ∫ scale in Icc (0 : ℝ) 1,
        scale ^ power • originalWeightedDilationJoint sigma gamma ell cell field (point, scale))
      (weightedIntegral_contDiff (originalWeightedDilationJoint_smooth sigma gamma ell cell field)
        (fun scale : ℝ => scale ^ power) (continuous_id.pow power) 0 1) =
      apWeightedJet sigma gamma ell cell (powerDilationJet power field) := by
  apply globalClosedJet_eq_of_restriction
  intro point
  rw [apWeightedJet_value, powerDilationJet_value]
  change (∫ scale in Icc (0 : ℝ) 1, scale ^ power •
    (physicalWeight sigma gamma ell cell point.val • smoothClosedExtension field (scale • point.val))) =
      physicalWeight sigma gamma ell cell point.val • _
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with scale
  exact smul_comm _ _ _

theorem originalPower_weighted_derivative {dimension rank : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (power : ℕ) (field : ClosedJet dimension) (word : CartesianWord rank) (point : ClosedDisk) :
    closedDerivative (apWeightedJet sigma gamma ell cell (powerDilationJet power field)) rank word point =
      ∫ scale in Icc (0 : ℝ) 1, scale ^ power •
        closedDerivative (apWeightedJet sigma gamma ell cell (dilationJet scale field)) rank word point := by
  rw [← originalWeightedPower_restricts sigma gamma ell cell power field, globalClosedJet_derivative,
    cartesianDerivative_weightedIntegral rank word (originalWeightedDilationJoint_smooth sigma gamma ell cell field)
      (fun scale : ℝ => scale ^ power) (continuous_id.pow power) 0 1]
  apply integral_congr_ae
  filter_upwards with scale
  rw [originalWeightedDilationJoint_derivative]

def originalPowerDerivativeFamily {dimension rank : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (power : ℕ) (field : ClosedJet dimension) (word : CartesianWord rank) (scale : ℝ) :
    C(ClosedDisk, ComplexEuclidean dimension) :=
  scale ^ power • closedDerivative (apWeightedJet sigma gamma ell cell (dilationJet scale field)) rank word

theorem originalPowerDerivativeFamily_continuous {dimension rank : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (power : ℕ) (field : ClosedJet dimension) (word : CartesianWord rank) :
    Continuous (originalPowerDerivativeFamily sigma gamma ell cell power field word) := by
  have smooth := originalWeightedDilationJoint_smooth sigma gamma ell cell field
  have derivativeContinuous := (sliceListDerivative_smooth (List.ofFn word) smooth).continuous
  apply ContinuousMap.continuous_of_continuous_uncurry
  have equality : (fun argument : ℝ × ClosedDisk =>
      originalPowerDerivativeFamily sigma gamma ell cell power field word argument.1 argument.2) =
      fun argument => argument.1 ^ power • sliceListDerivative (List.ofFn word)
        (originalWeightedDilationJoint sigma gamma ell cell field) (argument.2.val, argument.1) := by
    funext argument
    change argument.1 ^ power •
      closedDerivative (apWeightedJet sigma gamma ell cell (dilationJet argument.1 field)) rank word argument.2 = _
    apply congrArg (fun value : ComplexEuclidean dimension => argument.1 ^ power • value)
    rw [← originalWeightedDilationJoint_derivative]
    have listEquality := congrFun (sliceListDerivative_eq (List.ofFn word) smooth argument.1) argument.2.val
    exact ((listDerivative_ofFn isOpen_univ rank word
      ((smooth.comp (contDiff_id.prodMk contDiff_const)).contDiffOn) (mem_univ _)).symm.trans listEquality.symm)
  change Continuous (fun argument : ℝ × ClosedDisk =>
    originalPowerDerivativeFamily sigma gamma ell cell power field word argument.1 argument.2)
  rw [equality]
  exact (continuous_fst.pow power).smul
    (derivativeContinuous.comp ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst))

theorem originalPower_weighted_derivative_map {dimension rank : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (power : ℕ) (field : ClosedJet dimension) (word : CartesianWord rank) :
    closedDerivative (apWeightedJet sigma gamma ell cell (powerDilationJet power field)) rank word =
      ∫ scale in Icc (0 : ℝ) 1, originalPowerDerivativeFamily sigma gamma ell cell power field word scale := by
  apply ContinuousMap.ext
  intro point
  rw [originalPower_weighted_derivative, ContinuousMap.integral_apply
    (originalPowerDerivativeFamily_continuous sigma gamma ell cell power field word).continuousOn.integrableOn_Icc]
  rfl

end Grad.ActualExceptionalInverse
