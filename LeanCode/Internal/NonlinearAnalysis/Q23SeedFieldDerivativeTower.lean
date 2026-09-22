import Q23SeedTransferReassemblyTower
import Q23SeedScalarFamilies

noncomputable section

set_option maxRecDepth 5000
set_option maxHeartbeats 3200000

open Set
open scoped BigOperators ContDiff

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers Grad.Constraints.Gauges Grad.Constraints.Seed

/-- Core representative of every seed derivative of the planar seed field. -/
def q23SeedPlanarFieldCoreDerivative (phase : PhaseParameters) (order : ℕ)
    (parameter : Seed.Parameters) (directions : Fin order → Seed.Parameters) :
    ACore phase 2 :=
  q23SeedMatrixCoreDerivative phase order parameter directions
    (tamePlanarCoordinateField phase)

/-- Core representative of every seed derivative of the included seed field. -/
def q23SeedFieldCoreDerivative (phase : PhaseParameters) (order : ℕ)
    (parameter : Seed.Parameters) (directions : Fin order → Seed.Parameters) :
    ACore phase 3 :=
  Grad.Constraints.valueMapCore tamePlanarInclusion phase
    (q23SeedPlanarFieldCoreDerivative phase order parameter directions)

theorem completedTameSeedPlanarFieldFamily_all_orders_core
    (phase : PhaseParameters) (grade order : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    iteratedFDeriv ℝ order (completedTameSeedPlanarFieldFamily phase grade)
        parameter directions =
      q23ACoreEta phase 2 grade
        (q23SeedPlanarFieldCoreDerivative phase order parameter directions) := by
  let fixed : AGrade phase 2 grade :=
    q23ACoreEta phase 2 grade (tamePlanarCoordinateField phase)
  have matrixSmooth :=
    (completedSeedMatrixFamily_contDiffOn phase grade).contDiffAt
      (Seed.parameterDomain_isOpen.mem_nhds inside)
  let evaluationMap :
      (AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade) →L[ℝ]
        AGrade phase 2 grade :=
    (ContinuousLinearMap.apply ℝ (AGrade phase 2 grade) fixed).comp
      (q23RestrictScalarsCLM (E := AGrade phase 2 grade)
        (F := AGrade phase 2 grade))
  have evaluation := q23IteratedFDeriv_linearFunction_comp
    (fun operator : AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade =>
      evaluationMap operator)
    evaluationMap.map_add evaluationMap.map_smul evaluationMap.continuous
    (completedSeedMatrixFamily phase grade) parameter matrixSmooth order directions
  change iteratedFDeriv ℝ order
      (fun point => completedSeedMatrixFamily phase grade point
        (q23ACoreEta phase 2 grade (tamePlanarCoordinateField phase)))
      parameter directions = _
  change iteratedFDeriv ℝ order
      (fun point => completedSeedMatrixFamily phase grade point fixed)
      parameter directions =
    iteratedFDeriv ℝ order (completedSeedMatrixFamily phase grade)
      parameter directions fixed at evaluation
  rw [evaluation]
  exact completedSeedMatrixFamily_all_orders_core phase grade order parameter inside
    directions (tamePlanarCoordinateField phase)

theorem completedTameSeedFieldFamily_all_orders_core
    (phase : PhaseParameters) (grade order : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    iteratedFDeriv ℝ order (completedTameSeedFieldFamily phase grade)
        parameter directions =
      q23ACoreEta phase 3 grade
        (q23SeedFieldCoreDerivative phase order parameter directions) := by
  have planarSmooth :=
    (completedTameSeedPlanarFieldFamily_contDiffOn phase grade).contDiffAt
      (Seed.parameterDomain_isOpen.mem_nhds inside)
  let inclusion := q23ValueMapCompleted (grade := grade) phase tamePlanarInclusion
  have mapped := q23IteratedFDeriv_linearFunction_comp
    (fun field : AGrade phase 2 grade => inclusion field)
    (fun x y => by simp)
    (fun r x => by simp)
    inclusion.continuous
    (completedTameSeedPlanarFieldFamily phase grade) parameter planarSmooth order directions
  change iteratedFDeriv ℝ order
      (fun point => inclusion (completedTameSeedPlanarFieldFamily phase grade point))
      parameter directions = _
  rw [mapped,
    completedTameSeedPlanarFieldFamily_all_orders_core phase grade order parameter inside]
  change q23ValueMapCompleted (grade := grade) phase tamePlanarInclusion
      (q23ACoreEta phase 2 grade
        (q23SeedPlanarFieldCoreDerivative phase order parameter directions)) = _
  rw [q23ACoreEta_apply, q23ValueMapCompleted_core]
  rfl

end Grad.NonlinearQuotientBounds
