import GaugeMultiplierPhysical

noncomputable section

open scoped BigOperators

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Frame

/-- Literal seed factors at the physical cell coordinate. -/
def seedPhysicalFactor (kind : Fin 3) (parameter : Seed.Parameters) (angle : ℝ) :
    ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2 :=
  if kind = 0 then
    harmonicSeedOperator (parameter 0) (parameter 1) (parameter 2) (parameter 3) angle -
      ContinuousLinearMap.id ℂ (ComplexEuclidean 2)
  else if kind = 1 then Seed.actualInverseOperator parameter angle -
      ContinuousLinearMap.id ℂ (ComplexEuclidean 2)
  else deriv (harmonicSeedOperator (parameter 0) (parameter 1) (parameter 2) (parameter 3)) angle

theorem seedPhysicalFactor_fourier (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (kind : Fin 3) (angle : ℝ) :
    (∑' cell : ℤ, cellExponential cell angle • Seed.actualCells kind parameter cell) =
      seedPhysicalFactor kind parameter angle := by
  have identities := Seed.actual_seed_fourier phase parameter inside angle
  fin_cases kind
  · exact identities.1
  · exact identities.2.1
  · exact identities.2.2

/-- The smooth-core operations are actual physical multiplication, not only
weighted-row operators. This is the input needed for the written N12 gauges. -/
theorem seedDeviationCore_physical (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (kind : Fin 3)
    (field : ACore phase 2) (point : ClosedDisk) (angle : ℝ) :
    originalPhysicalEvaluationLift phase
      (GradeCore.ofCoreLinear (grade := 0) (seedDeviationCore phase parameter inside kind field)) point angle =
      seedPhysicalFactor kind parameter angle
        (originalPhysicalEvaluationLift phase (GradeCore.ofCoreLinear (grade := 0) field) point angle) := by
  have actual := smoothMultiplier_physical phase (Seed.actualCells kind parameter)
    (seedCells_all_summable phase parameter inside kind) field point angle
  rw [seedPhysicalFactor_fourier phase parameter inside kind angle] at actual
  exact actual

end Grad.Constraints.Gauges
