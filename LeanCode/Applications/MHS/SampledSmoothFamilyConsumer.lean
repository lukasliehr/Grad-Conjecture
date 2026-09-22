import SampledSmoothFamily

noncomputable section

open Set

namespace Grad.PhysicalFamily.SampledSmoothFamily.Consumer

open Grad.MainTarget
open Grad.PhysicalFamily
open Grad.PhysicalFamily.IntegerSampling
open Grad.PhysicalFamily.SampledSmoothFamily

/-- Immediate target consumer: one sampled family uses the literal G05
position, magnetic and pressure formulas and satisfies the exact
`SmoothRepresentatives` predicate on the construction interval. -/
theorem exactSampledSmoothFamily (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) :
    SmoothRepresentatives (Set.Icc family.lower family.upper)
        (sampledRepresentativeFamily cellLength family period epsilonIn
          potential) ∧
      (∀ (parameter : Set.Icc family.lower family.upper)
          (point : ClosedDisk) (time : ℝ),
        let representative := sampledRepresentativeFamily cellLength family
          period epsilonIn potential parameter
        representative.position (point, (time : CellCircle)) =
            sampledPositionLift cellLength family period parameter.val
              point.val time ∧
          representative.magnetic (point, (time : CellCircle)) =
            sampledMagneticLift cellLength family period parameter.val
              point.val time ∧
          representative.pressure (point, (time : CellCircle)) =
            sampledPressureLift potential point.val time) := by
  refine ⟨sampled_smoothRepresentatives cellLength family period epsilonIn
    potential, ?_⟩
  intro parameter point time
  have parameterIn :=
    closedInterval_subset_parameterNeighborhood cellLength family
      parameter.property
  simp [sampledRepresentativeFamily, sampledRepresentativeExtension,
    parameterIn]

end Grad.PhysicalFamily.SampledSmoothFamily.Consumer
