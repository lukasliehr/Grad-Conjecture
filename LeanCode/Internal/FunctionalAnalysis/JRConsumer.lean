import JRProof

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets.Realization

theorem recovery_consumer : RecoveryGoal := by
  intro dimension order domain exponent index
  exact ⟨recoveredDerivative_opNorm_le dimension order domain exponent index,
    recoveredDerivative_apply dimension order domain exponent index,
    recoveredDerivative_norm_le dimension order domain exponent index,
    recoveredDerivative_coordinates dimension order domain exponent index⟩

theorem zero_consumer : ZeroGoal := recoveredDerivative_zero

theorem weak_consumer : WeakGoal := recoveredDerivative_weak

theorem integral_consumer : IntegralGoal := recoveredDerivative_integral

theorem multiplier_consumer : MultiplierGoal := by
  intro dimension order domain exponent index jet
  exact ⟨recoveredDerivative_fieldGraph dimension order domain exponent index jet,
    recoveredDerivative_operatorGraph dimension order domain exponent index jet,
    recoveredDerivative_mem_domain dimension order domain exponent index jet,
    recoveredDerivative_operator_apply dimension order domain exponent index jet,
    recoveredDerivative_positive_coordinates dimension order domain exponent index jet⟩

theorem coherence_consumer : CoherenceGoal := recoveredDerivative_inclusion

theorem block_consumer : BlockGoal :=
  ⟨recovery_consumer, zero_consumer, weak_consumer, integral_consumer, multiplier_consumer, coherence_consumer⟩

theorem literal_integral_consumer (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (index : JetIndex order)
    (jet : WJet dimension order domain exponent) (cell : ℤ) (vector : PhysicalValue dimension)
    (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (supported : tsupport test ⊆ domain) :
    (∫ point in domain, test point •
      inner ℂ vector (recoveredDerivative dimension order domain exponent index jet point cell)) =
      (-1 : ℂ) ^ degree index * ∫ point in domain,
        Grad.WeakTesting.orderedTestDerivative (degree index) (derivativeWord index) test point •
          inner ℂ vector (base dimension order domain exponent jet point cell) :=
  recoveredDerivative_integral dimension order domain exponent index jet cell vector
    ⟨test, smooth, compact, supported⟩

theorem positive_domain_consumer (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (index : JetIndex order)
    (jet : WJet dimension order domain exponent) :
    Grad.CellWeights.fieldOperator dimension domain (Grad.CellWeights.positiveFactor (exponent index))
      ⟨recoveredDerivative dimension order domain exponent index jet,
        recoveredDerivative_mem_domain dimension order domain exponent index jet⟩ = jet.val index :=
  recoveredDerivative_operator_apply dimension order domain exponent index jet _

end Grad.WeightedJets.Realization
