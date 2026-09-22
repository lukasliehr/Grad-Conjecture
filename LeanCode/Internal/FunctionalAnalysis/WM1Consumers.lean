import WM1Proof

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open scoped Topology ContDiff BigOperators

namespace Grad.Mollifier.WeakJets.Consumer

theorem fullBlock : BlockGoal := blockGoal

theorem dependentBlock : DependentGoal := dependentGoal

def weightedRegularizer (dimension order : ℕ) (exponent : JetIndex order → ℕ) (epsilon : ℝ) :
    WJet dimension order Set.univ exponent →L[ℂ] WJet dimension order Set.univ exponent :=
  jetRegularizer dimension order exponent epsilon

theorem weightedCoordinate (dimension order : ℕ) (exponent : JetIndex order → ℕ)
    (epsilon : ℝ) (positive : 0 < epsilon) (jet : WJet dimension order Set.univ exponent)
    (index : JetIndex order) :
    (weightedRegularizer dimension order exponent epsilon jet).val index =
      Grad.SpatialTranslation.average (CellValues dimension) (Pointwise.scaledEta epsilon) (jet.val index) :=
  congrArg (fun tuple : JetTuple dimension order Set.univ => tuple index)
    ((jetRegularizer_specification dimension order exponent epsilon positive).1.1 jet)

theorem weightedBase (dimension order : ℕ) (exponent : JetIndex order → ℕ)
    (epsilon : ℝ) (positive : 0 < epsilon) (jet : WJet dimension order Set.univ exponent) :
    base dimension order Set.univ exponent (weightedRegularizer dimension order exponent epsilon jet) =
      Grad.SpatialTranslation.average (CellValues dimension) (Pointwise.scaledEta epsilon)
        (base dimension order Set.univ exponent jet) :=
  (jetRegularizer_specification dimension order exponent epsilon positive).1.2 jet

theorem weightedNormSquare (dimension order : ℕ) (exponent : JetIndex order → ℕ)
    (epsilon : ℝ) (positive : 0 < epsilon) (jet : WJet dimension order Set.univ exponent) :
    ‖weightedRegularizer dimension order exponent epsilon jet‖ ^ 2 =
      ∑ index, ‖Grad.SpatialTranslation.average (CellValues dimension) (Pointwise.scaledEta epsilon)
        (jet.val index)‖ ^ 2 := by
  rw [jet_norm_sq]
  apply Finset.sum_congr rfl
  intro index _
  rw [weightedCoordinate dimension order exponent epsilon positive jet index]

theorem weightedContraction (dimension order : ℕ) (exponent : JetIndex order → ℕ)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ‖weightedRegularizer dimension order exponent epsilon‖ ≤ 1 :=
  (jetRegularizer_specification dimension order exponent epsilon positive).2

theorem weightedStrongApproximation (dimension order : ℕ) (exponent : JetIndex order → ℕ)
    (jet : WJet dimension order Set.univ exponent) :
    Filter.Tendsto (fun epsilon => weightedRegularizer dimension order exponent epsilon jet)
      (𝓝[>] 0) (𝓝 jet) := jetRegularizer_tendsto dimension order exponent jet

theorem smoothAllCells (dimension order : ℕ) (exponent : JetIndex order → ℕ)
    (epsilon : ℝ) (positive : 0 < epsilon) (jet : WJet dimension order Set.univ exponent)
    (index : JetIndex order) (point : Spatial) (cell : ℤ) :
    Pointwise.smoothRepresentative (CellValues dimension) (Pointwise.scaledEta epsilon)
        (jet.val index) point cell =
      Grad.CellWeights.positiveFactor (exponent index) cell •
        Pointwise.orderedDerivative (degree index) (derivativeWord index)
          (Pointwise.smoothRepresentative (CellValues dimension) (Pointwise.scaledEta epsilon)
            (base dimension order Set.univ exponent jet)) point cell :=
  weighted_kernel_identity dimension order exponent _ (Pointwise.scaledEta_contDiff epsilon)
    (Pointwise.scaledEta_compactSupport epsilon positive) jet index point cell

theorem smoothActualRepresentatives : SmoothGoal := smoothGoal

theorem rawWeightedIntegral : IntegralGoal := integralGoal

theorem averagedExistingWeakDerivative : AveragedWeakGoal := averagedWeakGoal

theorem finiteZeroCases : ZeroGoal := zeroGoal

end Grad.Mollifier.WeakJets.Consumer
