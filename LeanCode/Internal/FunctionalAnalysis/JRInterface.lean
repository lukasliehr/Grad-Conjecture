import JetInclusionsProof
import CellMultiplierGraphs

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets.Realization

def recoveredDerivative (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (index : JetIndex order) :
    WJet dimension order domain exponent →L[ℂ] FieldL2 dimension domain :=
  (Grad.CellWeights.inverseFieldCLM dimension domain (exponent index)).comp
    ((coordinate dimension order domain index).comp
      (jetGraph dimension order domain exponent).subtypeL)

def RecoveryGoal : Prop :=
  ∀ (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (index : JetIndex order),
    ‖recoveredDerivative dimension order domain exponent index‖ ≤ 1 ∧
    (∀ jet : WJet dimension order domain exponent,
      recoveredDerivative dimension order domain exponent index jet =
        Grad.CellWeights.inverseFieldCLM dimension domain (exponent index) (jet.val index)) ∧
    (∀ jet : WJet dimension order domain exponent,
      ‖recoveredDerivative dimension order domain exponent index jet‖ ≤ ‖jet‖) ∧
    (∀ jet : WJet dimension order domain exponent,
      ∀ᵐ point ∂volume.restrict domain, ∀ cell : ℤ,
        recoveredDerivative dimension order domain exponent index jet point cell =
          Grad.CellWeights.inverseFactor (exponent index) cell • jet.val index point cell)

def ZeroGoal : Prop :=
  ∀ (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ),
    recoveredDerivative dimension order domain exponent (zeroIndex order) =
      base dimension order domain exponent

def WeakGoal : Prop :=
  ∀ (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (index : JetIndex order) (jet : WJet dimension order domain exponent)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction domain),
    testPairing dimension domain cell vector test
        (recoveredDerivative dimension order domain exponent index jet) =
      (-1 : ℂ) ^ degree index * derivativeTestPairing dimension order domain index cell vector test
        (base dimension order domain exponent jet)

def IntegralGoal : Prop :=
  ∀ (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (index : JetIndex order) (jet : WJet dimension order domain exponent)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction domain),
    (∫ point in domain, test.toFun point •
      inner ℂ vector (recoveredDerivative dimension order domain exponent index jet point cell)) =
      (-1 : ℂ) ^ degree index * ∫ point in domain,
        Grad.WeakTesting.orderedTestDerivative (degree index) (derivativeWord index) test.toFun point •
          inner ℂ vector (base dimension order domain exponent jet point cell)

def MultiplierGoal : Prop :=
  ∀ (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (index : JetIndex order) (jet : WJet dimension order domain exponent),
    (recoveredDerivative dimension order domain exponent index jet, jet.val index) ∈
      Grad.CellWeights.fieldGraph dimension domain (Grad.CellWeights.positiveFactor (exponent index)) ∧
    (recoveredDerivative dimension order domain exponent index jet, jet.val index) ∈
      (Grad.CellWeights.fieldOperator dimension domain
        (Grad.CellWeights.positiveFactor (exponent index))).graph ∧
    recoveredDerivative dimension order domain exponent index jet ∈
      (Grad.CellWeights.fieldOperator dimension domain
        (Grad.CellWeights.positiveFactor (exponent index))).domain ∧
    (∀ membership : recoveredDerivative dimension order domain exponent index jet ∈
      (Grad.CellWeights.fieldOperator dimension domain
        (Grad.CellWeights.positiveFactor (exponent index))).domain,
      Grad.CellWeights.fieldOperator dimension domain (Grad.CellWeights.positiveFactor (exponent index))
        ⟨recoveredDerivative dimension order domain exponent index jet, membership⟩ = jet.val index) ∧
    (∀ᵐ point ∂volume.restrict domain, ∀ cell : ℤ,
      jet.val index point cell = Grad.CellWeights.positiveFactor (exponent index) cell •
        recoveredDerivative dimension order domain exponent index jet point cell)

def CoherenceGoal : Prop :=
  ∀ (dimension lower higher : ℕ) (domain : Set Spatial) (gap : ℕ) (bound : lower ≤ higher)
    (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ)
    (compatible : Inclusions.Compatible bound gap source target) (index : JetIndex lower),
    (recoveredDerivative dimension lower domain target index).comp
        (Inclusions.inclusion dimension lower higher domain gap bound source target compatible) =
      recoveredDerivative dimension higher domain source (Inclusions.indexInclusion bound index)

def BlockGoal : Prop :=
  RecoveryGoal ∧ ZeroGoal ∧ WeakGoal ∧ IntegralGoal ∧ MultiplierGoal ∧ CoherenceGoal

end Grad.WeightedJets.Realization
