import ANF4OriginalBoundaryForcing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualScalarForcing
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Ledger
open Grad.CircularHighWeak
open Grad.ActualAngularInverse Grad.ActualNonexceptionalInverse Grad.RawCircularSectors Grad.ActualMeanInverse
variable {L sigma gamma ell : ℝ}

private theorem doubled {E : Type*} [AddCommGroup E] [Module ℂ E] (a b : E) :
    (a + b) + b = a + (2 : ℂ) • b := by module

theorem rotation_gradient_actual (theta : ClosedJet 1) :
    rotationJet (gradientJet theta) = gradientJet (rotationJet theta) + valueMapJet quarterValueMap (gradientJet theta) := by
  change rotationJet
    (valueMapJet (matrixUnit 0 0) (partialJet 0 theta) + valueMapJet (matrixUnit 1 0) (partialJet 1 theta)) = _
  rw [rotationJet_add]
  rw [rotationJet_valueMap, rotationJet_valueMap, rotation_partial_zero, rotation_partial_one]
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  simp only [closedJet_value_add, ContinuousMap.add_apply, valueMapJet_value,
    sub_eq_add_neg, closedJet_value_neg, ContinuousMap.neg_apply, gradientJet_value]
  fin_cases coordinate <;> simp [matrixUnit_apply, operatorBasis, quarterValueMap, quarterValueLinear]

theorem apRotation_gradient_actual (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) :
    apSmoothRotation admissible 2 (apSmoothGradient admissible theta) =
      apSmoothGradient admissible (apSmoothRotation admissible 1 theta) +
        apSmoothQuarter L sigma gamma ell (apSmoothGradient admissible theta) := by
  apply apSmoothJet_ext admissible
  intro cell
  let jet1 := apSmoothJet admissible 1 cell
  let jet2 := apSmoothJet admissible 2 cell
  have left := (apSmoothRotation_jet admissible (apSmoothGradient admissible theta) cell).trans
    (congrArg rotationJet (apSmoothGradient_jet admissible theta cell))
  have grad := (apSmoothGradient_jet admissible (apSmoothRotation admissible 1 theta) cell).trans
    (congrArg gradientJet (apSmoothRotation_jet admissible theta cell))
  have turned := (apSmoothValueMap_jet admissible quarterValueMap (apSmoothGradient admissible theta) cell).trans
    (congrArg (valueMapJet quarterValueMap) (apSmoothGradient_jet admissible theta cell))
  have right := (jet2.map_add (apSmoothGradient admissible (apSmoothRotation admissible 1 theta))
    (apSmoothQuarter L sigma gamma ell (apSmoothGradient admissible theta))).trans
      (congrArg₂ (fun a b : ClosedJet 2 => a + b) grad turned)
  exact left.trans ((rotation_gradient_actual (jet1 theta)).trans right.symm)

theorem excludedForce_nonresonant (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (excluded : AvoidsExceptionalSource source) :
    VectorNonresonant admissible source.1 := by
  constructor
  · apply rawExclusion_nonresonant admissible source.1 1 (Or.inl rfl)
    exact congrArg Prod.fst (excluded _ (by norm_num [IsExceptionalRaw]))
  · apply rawExclusion_nonresonant admissible source.1 (-1) (Or.inr rfl)
    exact congrArg Prod.fst (excluded _ (by norm_num [IsExceptionalRaw]))

theorem forceResponse_equation (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (excluded : AvoidsExceptionalSource source) :
    vectorRotation admissible (forceResponse admissible source.1) = -source.1 :=
  ((vectorRotation admissible).map_neg _).trans
    (congrArg Neg.neg (apVectorInverse_solves admissible source.1 (excludedForce_nonresonant admissible source excluded)))

def homogeneousVelocity (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell) : APSmooth L sigma gamma ell 2 :=
  apSmoothGradient admissible theta + reconstructedVector admissible theta source.1 - forceResponse admissible source.1

private theorem homogeneous_algebra {E : Type*} [AddCommGroup E] [Module ℂ E]
    (row : E →ₗ[ℂ] E) (gradient turned rotated stored response force : E)
    (gradientEquation : row gradient = rotated + (2 : ℂ) • turned)
    (storedEquation : row stored = -((2 : ℂ) • turned + force))
    (responseEquation : row response = -force) :
    row (gradient + stored - response) = rotated := by
  rw [map_sub, map_add, gradientEquation, storedEquation, responseEquation]
  module

theorem homogeneousVelocity_equation (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source) :
    vectorRotation admissible (homogeneousVelocity admissible theta source) =
      apSmoothGradient admissible (apSmoothRotation admissible 1 theta) := by
  let grad := apSmoothGradient admissible theta
  let turned := apSmoothQuarter L sigma gamma ell grad
  let rotated := apSmoothGradient admissible (apSmoothRotation admissible 1 theta)
  have gradientEquation : vectorRotation admissible grad = rotated + (2 : ℂ) • turned :=
    (congrArg (fun value : APSmooth L sigma gamma ell 2 => value + turned)
      (apRotation_gradient_actual admissible theta)).trans (doubled rotated turned)
  have storedEquation : vectorRotation admissible (reconstructedVector admissible theta source.1) =
      -((2 : ℂ) • turned + source.1) :=
    ((vectorRotation admissible).map_neg (apVectorInverse admissible (reconstructionLoad admissible theta source.1))).trans
      (congrArg Neg.neg (apVectorInverse_solves admissible (reconstructionLoad admissible theta source.1)
        (reconstructionLoad_nonresonant admissible theta source thetaExcluded sourceExcluded)))
  exact homogeneous_algebra (vectorRotation admissible) grad turned rotated
    (reconstructedVector admissible theta source.1) (forceResponse admissible source.1) source.1
    gradientEquation storedEquation (forceResponse_equation admissible source sourceExcluded)

end Grad.ActualScalarForcing
