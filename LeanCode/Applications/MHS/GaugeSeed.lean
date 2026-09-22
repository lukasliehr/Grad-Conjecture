import GaugeMultiplierEvaluation

noncomputable section

open scoped BigOperators

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints.Multipliers

theorem seedCells_all_summable (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (kind : Fin 3) (grade : ℕ) :
    Summable (envelopeTerm phase grade (Seed.actualCells kind parameter)) := by
  let radius := ∑ index : Fin 3, |parameter index.succ|
  have radiusNonnegative : 0 ≤ radius := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have radiusBound (index : Fin 3) : |parameter index.succ| ≤ radius :=
    Finset.single_le_sum (s := Finset.univ) (f := fun index : Fin 3 => |parameter index.succ|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ index)
  obtain ⟨_, _, bounded⟩ := Seed.actualSeedQuantitative phase grade |parameter 0| radius
    (abs_nonneg _) inside radiusNonnegative
  exact (bounded parameter le_rfl radiusBound).1 kind

/-- Actual smooth original-core multiplication by each literal seed deviation,
inverse deviation, and angular derivative, sharing every completed grade. -/
def seedDeviationCore (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (kind : Fin 3) :
    ACore phase 2 →ₗ[ℂ] ACore phase 2 :=
  smoothMultiplier phase (Seed.actualCells kind parameter)
    (seedCells_all_summable phase parameter inside kind)

def seedMatrixCore (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) : ACore phase 2 →ₗ[ℂ] ACore phase 2 :=
  LinearMap.id + seedDeviationCore phase parameter inside 0

def seedInverseCore (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) : ACore phase 2 →ₗ[ℂ] ACore phase 2 :=
  LinearMap.id + seedDeviationCore phase parameter inside 1

def seedDerivativeCore (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) : ACore phase 2 →ₗ[ℂ] ACore phase 2 :=
  seedDeviationCore phase parameter inside 2

theorem seedDeviationCore_bound (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (kind : Fin 3)
    (field : ACore phase 2) (grade : ℕ) :
    ‖GradeCore.ofCoreLinear (grade := grade) (seedDeviationCore phase parameter inside kind field)‖ ≤
      multiplierConstant grade phase.gamma * envelope phase grade (Seed.actualCells kind parameter) *
        ‖GradeCore.ofCoreLinear (grade := grade) field‖ :=
  smoothMultiplier_bound phase _ (seedCells_all_summable phase parameter inside kind) field grade

theorem seedDeviationCore_zero_jets (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (kind : Fin 3)
    (field : ACore phase 2) (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.1 cell)) :
    ∀ cell, ZeroCartesianFirstJets ((seedDeviationCore phase parameter inside kind field).1 cell) :=
  smoothMultiplier_preserves_zero_first_jets phase _
    (seedCells_all_summable phase parameter inside kind) field zeroJets

theorem seedDeviationCore_literal_derivatives (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (kind : Fin 3)
    (field : ACore phase 2) (cell : ℤ) (order : ℕ)
    (word : CartesianWord order) (point : ClosedDisk) :
    HasSum (fun shift : ℤ => Seed.actualCells kind parameter shift
      (closedDerivative (field.1 (cell - shift)) order word point))
      (closedDerivative ((seedDeviationCore phase parameter inside kind field).1 cell) order word point) :=
  smoothMultiplier_derivative_hasSum phase _
    (seedCells_all_summable phase parameter inside kind) field cell order word point

end Grad.Constraints.Gauges
