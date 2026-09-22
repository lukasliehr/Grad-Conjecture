import AKCX2LowerOrderedFirstGraph
import CB1Jets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets Grad.WeightedJets.Ordered
open Grad.CellWeights Grad.CellBinomial

/-- The strict lower spatial derivative keeps the original cell reserve in
its actual first graph. The stored weighted coordinate supplies the lambda
jet; no higher regularity of this derivative is assumed. -/
theorem startupOrderedDerivative_firstWeighted {dimension order rank weight : ℕ}
    (field : GraphGrade dimension order weight openUnitDisk) (bound : rank+1 ≤ order)
    (word : Fin rank → Fin 2) :
    ∃ graph : GraphGrade dimension 1 weight openUnitDisk,
      base dimension 1 openUnitDisk (fun _ => weight) graph =
        orderedDerivative dimension order rank openUnitDisk (fun _ => weight) (by omega) field word := by
  let lambda := lambdaJetOfGrade dimension order weight openUnitDisk field
  obtain ⟨first,firstSame⟩ := startupOrderedDerivative_first lambda.jet bound word
  have stored : orderedDerivative dimension order rank openUnitDisk (fun _ => 0) (by omega) lambda.jet word =
      field.val (wordIndex (show rank ≤ order from by omega) word) := by
    rw [orderedDerivative_apply,Realization.recoveredDerivative_apply,inverseFieldCLM_zero,
      ContinuousLinearMap.id_apply]
    exact congrFun (congrArg (fun value => fun index => value index)
      (lambdaJetOfGrade_tuple dimension order weight openUnitDisk field)) _
  have actualGraph :
      (orderedDerivative dimension order rank openUnitDisk (fun _ => weight) (by omega) field word,
        base dimension 1 openUnitDisk (fun _ => 0) first) ∈
          fieldGraph dimension openUnitDisk (positiveFactor weight) := by
    rw [firstSame,stored,orderedDerivative_apply]
    exact Realization.recoveredDerivative_fieldGraph dimension order openUnitDisk (fun _ => weight) _ field
  let firstLambda := operatorJetOfGraph dimension 1 openUnitDisk (positiveFactor weight)
    (orderedDerivative dimension order rank openUnitDisk (fun _ => weight) (by omega) field word) first actualGraph
  exact ⟨weightedJetOfLambda dimension 1 weight openUnitDisk _ firstLambda,
    weightedJetOfLambda_base dimension 1 weight openUnitDisk _ firstLambda⟩

end Grad.CartesianStartup
