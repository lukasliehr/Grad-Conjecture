import SM1Leibniz
import SM1Tuple

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets.SpatialMultiplier

theorem unweightedCoordinate_weak (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (upper : JetIndex order) (jet : WJet dimension order domain exponent) (cell : ℤ)
    (vector : PhysicalValue dimension) (test : TestFunction domain) :
    testPairing dimension domain cell vector test
        (unweightedCoordinate dimension order domain openDomain symbol exponent upper jet) =
      (-1 : ℂ) ^ degree upper * derivativeTestPairing dimension order domain upper cell vector test
        (fieldMultiplier dimension domain openDomain (derivativeScalar symbol (zeroIndex order))
          (base dimension order domain exponent jet)) := by
  classical
  let productTest (lower : JetIndex order) : TestFunction domain :=
    multiplyTest (scalarDerivative (difference upper lower).val symbol.toFun)
      (scalarDerivative_smooth _ symbol.toFun symbol.smooth) test
  have integrableTerm (lower : JetIndex order) :
      Integrable (fun point => ((-1 : ℝ) ^ degree lower * binomial upper lower) •
        (scalarDerivative lower.val (productTest lower).toFun point •
          inner ℂ vector (base dimension order domain exponent jet point cell))) (volume.restrict domain) := by
    exact ((Grad.WeakTesting.pairing_integrable dimension domain cell vector
      (scalarDerivative lower.val (productTest lower).toFun)
      (Grad.WeakTesting.orderedTestDerivative_memLp domain (degree lower) (derivativeWord lower)
        (productTest lower).toFun (productTest lower).smooth (productTest lower).compact)
      (base dimension order domain exponent jet)).smul
        ((-1 : ℝ) ^ degree lower * binomial upper lower)).congr
          (Filter.Eventually.of_forall (fun _ => rfl))
  calc
    _ = ∑ lower ∈ below upper, (binomial upper lower : ℂ) *
        ((-1 : ℂ) ^ degree lower *
          derivativeTestPairing dimension order domain lower cell vector (productTest lower)
            (base dimension order domain exponent jet)) := by
      rw [unweightedCoordinate_apply, map_sum]
      apply Finset.sum_congr rfl
      intro lower membership
      rw [map_smul, fieldMultiplier_pairing]
      change (binomial upper lower : ℂ) *
        testPairing dimension domain cell vector (productTest lower)
          (Realization.recoveredDerivative dimension order domain exponent lower jet) = _
      rw [Realization.recoveredDerivative_weak]
    _ = ∑ lower ∈ below upper, ∫ point in domain,
        ((-1 : ℝ) ^ degree lower * binomial upper lower) •
          (scalarDerivative lower.val (productTest lower).toFun point •
            inner ℂ vector (base dimension order domain exponent jet point cell)) := by
      apply Finset.sum_congr rfl
      intro lower membership
      rw [integral_smul, derivativeTestPairing_apply,
        scalarDerivative_eq lower (productTest lower).toFun]
      change (binomial upper lower : ℂ) * ((-1 : ℂ) ^ degree lower * _) =
        (((-1 : ℝ) ^ degree lower * (binomial upper lower : ℝ) : ℝ) : ℂ) * _
      push_cast
      ring
    _ = ∫ point in domain, ∑ lower ∈ below upper,
        ((-1 : ℝ) ^ degree lower * binomial upper lower) •
          (scalarDerivative lower.val (productTest lower).toFun point •
            inner ℂ vector (base dimension order domain exponent jet point cell)) :=
      (integral_finsetSum _ (fun lower _ => integrableTerm lower)).symm
    _ = ∫ point in domain, ((-1 : ℝ) ^ degree upper * symbol.toFun point *
        scalarDerivative upper.val test.toFun point) •
          inner ℂ vector (base dimension order domain exponent jet point cell) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun point => by
        simp only [smul_smul, ← Finset.sum_smul]
        change (∑ lower ∈ below upper, (-1 : ℝ) ^ degree lower * binomial upper lower *
          scalarDerivative lower.val
            (fun point => scalarDerivative (difference upper lower).val symbol.toFun point *
              test.toFun point) point) •
          inner ℂ vector (base dimension order domain exponent jet point cell) = _
        rw [scalar_adjoint order upper symbol.toFun test.toFun symbol.smooth test.smooth])
    _ = (-1 : ℂ) ^ degree upper * ∫ point in domain,
        (symbol.toFun point * scalarDerivative upper.val test.toFun point) •
          inner ℂ vector (base dimension order domain exponent jet point cell) := by
      change _ = (-1 : ℂ) ^ degree upper • ∫ point in domain,
        (symbol.toFun point * scalarDerivative upper.val test.toFun point) •
          inner ℂ vector (base dimension order domain exponent jet point cell)
      rw [← integral_smul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun point => by
        change (((-1 : ℝ) ^ degree upper * symbol.toFun point *
          scalarDerivative upper.val test.toFun point : ℝ) : ℂ) *
            inner ℂ vector (base dimension order domain exponent jet point cell) =
          (-1 : ℂ) ^ degree upper *
            (((symbol.toFun point * scalarDerivative upper.val test.toFun point : ℝ) : ℂ) *
              inner ℂ vector (base dimension order domain exponent jet point cell))
        push_cast
        ring)
    _ = _ := by
      rw [derivativeTestPairing_apply]
      congr 1
      apply integral_congr_ae
      filter_upwards [fieldMultiplier_ae dimension domain openDomain
        (derivativeScalar symbol (zeroIndex order)) (base dimension order domain exponent jet)]
        with point coordinates
      rw [coordinates cell, inner_smul_right]
      change ((symbol.toFun point * scalarDerivative upper.val test.toFun point : ℝ) : ℂ) *
        inner ℂ vector (base dimension order domain exponent jet point cell) =
        (scalarDerivative upper.val test.toFun point : ℂ) *
          ((symbol.toFun point : ℂ) * inner ℂ vector (base dimension order domain exponent jet point cell))
      push_cast
      ring

theorem unweightedCoordinate_integral (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (upper : JetIndex order) (jet : WJet dimension order domain exponent) (cell : ℤ)
    (vector : PhysicalValue dimension) (test : TestFunction domain) :
    (∫ point in domain, test.toFun point • inner ℂ vector
      (unweightedCoordinate dimension order domain openDomain symbol exponent upper jet point cell)) =
      (-1 : ℂ) ^ degree upper * ∫ point in domain,
        scalarDerivative upper.val test.toFun point • inner ℂ vector
          (fieldMultiplier dimension domain openDomain (derivativeScalar symbol (zeroIndex order))
            (base dimension order domain exponent jet) point cell) := by
  simpa only [testPairing_apply, derivativeTestPairing_apply, scalarDerivative_eq] using
    unweightedCoordinate_weak dimension order domain openDomain symbol exponent upper jet cell vector test

theorem unweightedCoordinate_hasWeak (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (upper : JetIndex order) (jet : WJet dimension order domain exponent) :
    Grad.WeakTesting.Commutation.HasWeakOrderedDerivative dimension domain (degree upper)
      (derivativeWord upper)
      (fieldMultiplier dimension domain openDomain (derivativeScalar symbol (zeroIndex order))
        (base dimension order domain exponent jet))
      (unweightedCoordinate dimension order domain openDomain symbol exponent upper jet) := by
  intro cell vector test smoothness compactSupport supported
  exact unweightedCoordinate_weak dimension order domain openDomain symbol exponent upper jet cell vector
    ⟨test, smoothness, compactSupport, supported⟩

theorem weak_consumer : WeakLeibnizGoal := by
  intro dimension order domain openDomain symbol exponent upper jet
  exact ⟨unweightedCoordinate_hasWeak dimension order domain openDomain symbol exponent upper jet,
    unweightedCoordinate_integral dimension order domain openDomain symbol exponent upper jet⟩

end Grad.WeightedJets.SpatialMultiplier
