import RadialSmoothIntegral
import RadialWeightedDerivative
import ClosedJetIntegralL2

noncomputable section

open Set MeasureTheory
open scoped ContDiff Topology

namespace Grad.NonlinearRadial

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotient
open Grad.RepresentedKernel.SpatialProduct

def radialIntervalValue {dimension : ℕ} (lower upper : ℝ) (field : ClosedJet dimension)
    (point : SpatialPlane) : ComplexEuclidean dimension :=
  ∫ scale in Icc lower upper, Real.negMulLog scale • smoothClosedExtension field (scale • point)

theorem radialIntervalValue_smooth {dimension : ℕ} (lower upper : ℝ) (field : ClosedJet dimension) :
    ContDiff ℝ ∞ (radialIntervalValue lower upper field) := by
  exact weightedIntegral_contDiff
    (field := fun argument : SpatialPlane × ℝ => smoothClosedExtension field (argument.2 • argument.1))
    ((smoothClosedExtension_smooth field).comp (contDiff_snd.smul contDiff_fst))
    Real.negMulLog Real.continuous_negMulLog lower upper

def radialIntervalJet {dimension : ℕ} (lower upper : ℝ) (field : ClosedJet dimension) : ClosedJet dimension :=
  globalClosedJet (radialIntervalValue lower upper field) (radialIntervalValue_smooth lower upper field)

theorem radialIntervalJet_value {dimension : ℕ} (lower upper : ℝ) (field : ClosedJet dimension)
    (point : ClosedDisk) :
    (radialIntervalJet lower upper field).value point = radialIntervalValue lower upper field point.val := rfl

theorem radialIntervalJet_full_value {dimension : ℕ} (field : ClosedJet dimension) (point : ClosedDisk) :
    (radialIntervalJet 0 1 field).value point = integralCoefficient field point := by
  change (∫ scale in Icc (0 : ℝ) 1, Real.negMulLog scale • smoothClosedExtension field (scale • point.val)) = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  rfl

def weightedDilationJoint {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) (argument : SpatialPlane × ℝ) : ComplexEuclidean dimension :=
  cartesianWeight parameters cell argument.1 • smoothClosedExtension field (argument.2 • argument.1)

theorem weightedDilationJoint_smooth {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) : ContDiff ℝ ∞ (weightedDilationJoint parameters cell field) :=
  ((cartesianWeight_contDiff parameters cell).comp contDiff_fst).smul
    ((smoothClosedExtension_smooth field).comp (contDiff_snd.smul contDiff_fst))

theorem weightedDilationJoint_restricts {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) (scale : ℝ) :
    globalClosedJet (fun point => weightedDilationJoint parameters cell field (point, scale))
      ((weightedDilationJoint_smooth parameters cell field).comp (contDiff_id.prodMk contDiff_const)) =
      phaseWeightedJet parameters cell (dilationJet scale field) := by
  apply globalClosedJet_eq_of_restriction
  intro point
  rw [phaseWeightedJet_spec]
  rfl

theorem weightedDilationJoint_derivative {dimension rank : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) (scale : ℝ) (word : CartesianWord rank) (point : ClosedDisk) :
    cartesianDerivative rank word (fun source => weightedDilationJoint parameters cell field (source, scale)) point.val =
      closedDerivative (phaseWeightedJet parameters cell (dilationJet scale field)) rank word point := by
  rw [← weightedDilationJoint_restricts parameters cell field scale, globalClosedJet_derivative]

theorem weightedRadialInterval_restricts {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (lower upper : ℝ) (field : ClosedJet dimension) :
    globalClosedJet
      (fun point => ∫ scale in Icc lower upper,
        Real.negMulLog scale • weightedDilationJoint parameters cell field (point, scale))
      (weightedIntegral_contDiff (weightedDilationJoint_smooth parameters cell field)
        Real.negMulLog Real.continuous_negMulLog lower upper) =
      phaseWeightedJet parameters cell (radialIntervalJet lower upper field) := by
  apply globalClosedJet_eq_of_restriction
  intro point
  rw [phaseWeightedJet_spec]
  change (∫ scale in Icc lower upper, Real.negMulLog scale •
    (cartesianWeight parameters cell point.val • smoothClosedExtension field (scale • point.val))) =
      cartesianWeight parameters cell point.val • radialIntervalValue lower upper field point.val
  unfold radialIntervalValue
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with scale
  exact smul_comm _ _ _

theorem radialIntervalJet_weighted_derivative {dimension rank : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (lower upper : ℝ) (field : ClosedJet dimension) (word : CartesianWord rank) (point : ClosedDisk) :
    closedDerivative (phaseWeightedJet parameters cell (radialIntervalJet lower upper field)) rank word point =
      ∫ scale in Icc lower upper, Real.negMulLog scale •
        closedDerivative (phaseWeightedJet parameters cell (dilationJet scale field)) rank word point := by
  rw [← weightedRadialInterval_restricts parameters cell lower upper field, globalClosedJet_derivative,
    cartesianDerivative_weightedIntegral rank word (weightedDilationJoint_smooth parameters cell field)
      Real.negMulLog Real.continuous_negMulLog lower upper]
  apply integral_congr_ae
  filter_upwards with scale
  rw [weightedDilationJoint_derivative]

def weightedDilationDerivativeFamily {dimension rank : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) (word : CartesianWord rank) (scale : ℝ) :
    C(ClosedDisk, ComplexEuclidean dimension) :=
  Real.negMulLog scale • closedDerivative (phaseWeightedJet parameters cell (dilationJet scale field)) rank word

theorem weightedDilationDerivativeFamily_continuous {dimension rank : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) (word : CartesianWord rank) :
    Continuous (weightedDilationDerivativeFamily parameters cell field word) := by
  have smooth := weightedDilationJoint_smooth parameters cell field
  have derivativeContinuous := (sliceListDerivative_smooth (List.ofFn word) smooth).continuous
  apply ContinuousMap.continuous_of_continuous_uncurry
  have equality : (fun argument : ℝ × ClosedDisk =>
      weightedDilationDerivativeFamily parameters cell field word argument.1 argument.2) =
      fun argument => Real.negMulLog argument.1 • sliceListDerivative (List.ofFn word)
        (weightedDilationJoint parameters cell field) (argument.2.val, argument.1) := by
    funext argument
    change Real.negMulLog argument.1 •
      closedDerivative (phaseWeightedJet parameters cell (dilationJet argument.1 field)) rank word argument.2 = _
    apply congrArg (fun value : ComplexEuclidean dimension => Real.negMulLog argument.1 • value)
    rw [← weightedDilationJoint_derivative]
    have listEquality := congrFun (sliceListDerivative_eq (List.ofFn word) smooth argument.1) argument.2.val
    exact ((listDerivative_ofFn isOpen_univ rank word
      ((smooth.comp (contDiff_id.prodMk contDiff_const)).contDiffOn) (mem_univ _)).symm.trans listEquality.symm)
  change Continuous (fun argument : ℝ × ClosedDisk =>
    weightedDilationDerivativeFamily parameters cell field word argument.1 argument.2)
  rw [equality]
  exact (Real.continuous_negMulLog.comp continuous_fst).smul
    (derivativeContinuous.comp ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst))

theorem radialIntervalJet_weighted_derivative_map {dimension rank : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (lower upper : ℝ) (field : ClosedJet dimension) (word : CartesianWord rank) :
    closedDerivative (phaseWeightedJet parameters cell (radialIntervalJet lower upper field)) rank word =
      ∫ scale in Icc lower upper, weightedDilationDerivativeFamily parameters cell field word scale := by
  apply ContinuousMap.ext
  intro point
  rw [radialIntervalJet_weighted_derivative, ContinuousMap.integral_apply
    (weightedDilationDerivativeFamily_continuous parameters cell field word).continuousOn.integrableOn_Icc]
  rfl

end Grad.NonlinearRadial
