import Q23SeedDirectionalGenuine

noncomputable section

set_option maxRecDepth 5000
set_option maxHeartbeats 3200000

open Set Filter
open scoped Topology

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Seed
open Grad.NonlinearProduct

/-- The actual seed-field core tower is a genuine newest-first derivative
tower in every original grade. -/
theorem q23SeedFieldCoreDerivative_genuine
    (phase : PhaseParameters) (order grade : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (oldDirections : Fin order → Seed.Parameters) (newDirection : Seed.Parameters) :
    Tendsto (fun t : ℝ => originalGradeNorm grade
      ((((t : ℂ))⁻¹ •
          (q23SeedFieldCoreDerivative phase order
              (parameter + t • newDirection) oldDirections -
            q23SeedFieldCoreDerivative phase order parameter oldDirections)) -
        q23SeedFieldCoreDerivative phase (order + 1) parameter
          (Fin.cons newDirection oldDirections)))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  exact q23CoreTower_genuine_of_actual
    (P := Seed.Parameters) (E := AGrade phase 3 grade)
    (Core := ACore phase 3)
    (mapping := completedTameSeedFieldFamily phase grade)
    (domain := Seed.parameterDomain) Seed.parameterDomain_isOpen
    (completedTameSeedFieldFamily_contDiffOn phase grade)
    (q23ACoreEta phase 3 grade)
    (fun value : ACore phase 3 => originalGradeNorm grade value)
    (fun value : ACore phase 3 =>
      aGradeEta_norm phase (GradeCore.ofCoreLinear value))
    (q23SeedFieldCoreDerivative phase)
    (fun derivativeOrder point pointInside
        (derivativeDirections : Fin derivativeOrder → Seed.Parameters) =>
      completedTameSeedFieldFamily_all_orders_core phase grade derivativeOrder
        point pointInside derivativeDirections)
    order parameter inside oldDirections newDirection

/-- The actual seed-scalar core tower is a genuine newest-first derivative
tower in every original grade. -/
theorem q23SeedScalarCoreDerivative_genuine
    (phase : PhaseParameters) (order grade : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (oldDirections : Fin order → Seed.Parameters) (newDirection : Seed.Parameters) :
    Tendsto (fun t : ℝ => originalGradeNorm grade
      ((((t : ℂ))⁻¹ •
          (q23SeedScalarCoreDerivative phase order
              (parameter + t • newDirection) oldDirections -
            q23SeedScalarCoreDerivative phase order parameter oldDirections)) -
        q23SeedScalarCoreDerivative phase (order + 1) parameter
          (Fin.cons newDirection oldDirections)))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  exact q23CoreTower_genuine_of_actual
    (P := Seed.Parameters) (E := AGrade phase 1 grade)
    (Core := ACore phase 1)
    (mapping := completedTameSeedScalarFamily phase grade)
    (domain := Seed.parameterDomain) Seed.parameterDomain_isOpen
    (completedTameSeedScalarFamily_contDiffOn phase grade)
    (q23FieldEmbed phase 1 grade)
    (fun value : ACore phase 1 => originalGradeNorm grade value)
    (q23FieldEmbed_norm phase 1 grade)
    (q23SeedScalarCoreDerivative phase)
    (fun derivativeOrder point pointInside
        (derivativeDirections : Fin derivativeOrder → Seed.Parameters) =>
      completedTameSeedScalarFamily_all_orders_core phase grade derivativeOrder
        point pointInside derivativeDirections)
    order parameter inside oldDirections newDirection

end Grad.NonlinearQuotientBounds
