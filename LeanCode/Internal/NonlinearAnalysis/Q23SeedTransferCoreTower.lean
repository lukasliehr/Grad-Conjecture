import Q23CoreOperatorCalculus

noncomputable section

set_option maxRecDepth 5000
set_option maxHeartbeats 3200000

open Set
open scoped BigOperators ContDiff

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers Grad.Constraints.Gauges Grad.Constraints.Seed

/-- The accepted smooth core embedded in one completed original grade. -/
def q23ACoreEta (phase : PhaseParameters) (dimension grade : ℕ) :
    ACore phase dimension →ₗ[ℂ] AGrade phase dimension grade :=
  (aGradeEta phase).toLinearMap.comp GradeCore.ofCoreLinear

@[simp]
theorem q23ACoreEta_apply (phase : PhaseParameters) (dimension grade : ℕ)
    (field : ACore phase dimension) :
    q23ACoreEta phase dimension grade field =
      aGradeEta phase (GradeCore.ofCoreLinear field) := rfl

/-- Total core representative of every derivative of one seed multiplier. -/
def q23SeedDeviationCoreDerivative (phase : PhaseParameters) (kind : Fin 3)
    (order : ℕ) (parameter : Seed.Parameters)
    (directions : Fin order → Seed.Parameters) :
    ACore phase 2 →ₗ[ℂ] ACore phase 2 := by
  classical
  exact if inside : parameter ∈ Seed.parameterDomain then
      seedParameterMultiplier phase order kind parameter inside directions
    else 0

theorem q23SeedDeviationCoreDerivative_of_inside (phase : PhaseParameters)
    (kind : Fin 3) (order : ℕ) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    q23SeedDeviationCoreDerivative phase kind order parameter directions =
      seedParameterMultiplier phase order kind parameter inside directions := by
  classical
  simp only [q23SeedDeviationCoreDerivative, dif_pos inside]

theorem completedSeedDeviationFamily_all_orders_core (phase : PhaseParameters)
    (grade : ℕ) (kind : Fin 3) (order : ℕ) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 2) :
    iteratedFDeriv ℝ order (completedSeedDeviationFamily phase grade kind)
        parameter directions (q23ACoreEta phase 2 grade field) =
      q23ACoreEta phase 2 grade
        (q23SeedDeviationCoreDerivative phase kind order parameter directions field) := by
  rw [iteratedFDeriv_completedSeedDeviationFamily phase grade order kind parameter inside
      directions,
    q23SeedDeviationCoreDerivative_of_inside phase kind order parameter inside directions]
  change completedSeedParameterDerivative phase grade order kind parameter directions
      (aGradeEta phase (GradeCore.ofCoreLinear field)) =
    aGradeEta phase (GradeCore.ofCoreLinear
      (seedParameterMultiplier phase order kind parameter inside directions field))
  exact completedSeedParameterDerivative_core phase grade order kind parameter inside
    directions field

/-- Total core representative of every derivative of a transposed seed
multiplier. -/
def q23SeedTransposeCoreDerivative (phase : PhaseParameters) (kind : Fin 3)
    (order : ℕ) (parameter : Seed.Parameters)
    (directions : Fin order → Seed.Parameters) :
    ACore phase 2 →ₗ[ℂ] ACore phase 2 := by
  classical
  exact if inside : parameter ∈ Seed.parameterDomain then
      seedTransposeParameterMultiplier phase order kind parameter inside directions
    else 0

theorem q23SeedTransposeCoreDerivative_of_inside (phase : PhaseParameters)
    (kind : Fin 3) (order : ℕ) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    q23SeedTransposeCoreDerivative phase kind order parameter directions =
      seedTransposeParameterMultiplier phase order kind parameter inside directions := by
  classical
  simp only [q23SeedTransposeCoreDerivative, dif_pos inside]

theorem iteratedFDeriv_completedSeedTransposeDeviationFamily
    (phase : PhaseParameters) (grade order : ℕ) (kind : Fin 3)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    iteratedFDeriv ℝ order (completedSeedTransposeDeviationFamily phase grade kind)
        parameter directions =
      completedSeedTransposeParameterDerivative phase grade order kind parameter directions := by
  have weightedSmooth :=
    (Seed.weightedSeedFamilies_contDiffOn phase grade kind).contDiffAt
      (Seed.parameterDomain_isOpen.mem_nhds inside)
  exact q23IteratedFDeriv_linearFunction_comp
    (fun sequence => weightedCompletedTransposeMap phase grade sequence)
    (fun x y => (weightedCompletedTransposeMap phase grade).map_add x y)
    (fun r x => by
      apply ContinuousLinearMap.ext
      intro field
      exact congrArg
        (fun operator : AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade => operator field)
        (((weightedCompletedTransposeMap phase grade).restrictScalars ℝ).map_smul r x))
    (weightedCompletedTransposeMap phase grade).continuous
    (Seed.weightedSeedFamilies phase grade kind) parameter weightedSmooth order directions

theorem completedSeedTransposeDeviationFamily_all_orders_core
    (phase : PhaseParameters) (grade : ℕ) (kind : Fin 3) (order : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 2) :
    iteratedFDeriv ℝ order (completedSeedTransposeDeviationFamily phase grade kind)
        parameter directions (q23ACoreEta phase 2 grade field) =
      q23ACoreEta phase 2 grade
        (q23SeedTransposeCoreDerivative phase kind order parameter directions field) := by
  rw [iteratedFDeriv_completedSeedTransposeDeviationFamily phase grade order kind parameter
      inside directions,
    q23SeedTransposeCoreDerivative_of_inside phase kind order parameter inside directions]
  change completedSeedTransposeParameterDerivative phase grade order kind parameter directions
      (aGradeEta phase (GradeCore.ofCoreLinear field)) =
    aGradeEta phase (GradeCore.ofCoreLinear
      (seedTransposeParameterMultiplier phase order kind parameter inside directions field))
  exact completedSeedTransposeParameterDerivative_core phase grade order kind parameter inside
    directions field

/-- Core tower for the actual completed matrix `M_p`. -/
def q23SeedMatrixCoreDerivative (phase : PhaseParameters) :
    (order : ℕ) → Seed.Parameters →
      (Fin order → Seed.Parameters) → ACore phase 2 →ₗ[ℂ] ACore phase 2 :=
  q23CoreOperatorAddDerivative
    (q23CoreConstantOperatorDerivative (LinearMap.id : ACore phase 2 →ₗ[ℂ] ACore phase 2))
    (q23SeedDeviationCoreDerivative phase 0)

theorem completedSeedMatrixFamily_all_orders_core (phase : PhaseParameters)
    (grade order : ℕ) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 2) :
    iteratedFDeriv ℝ order (completedSeedMatrixFamily phase grade)
        parameter directions (q23ACoreEta phase 2 grade field) =
      q23ACoreEta phase 2 grade
        (q23SeedMatrixCoreDerivative phase order parameter directions field) := by
  unfold completedSeedMatrixFamily q23SeedMatrixCoreDerivative
  exact iteratedFDeriv_operator_add_core
    (q23ACoreEta phase 2 grade) (q23ACoreEta phase 2 grade)
    (fun _ : Seed.Parameters => ContinuousLinearMap.id ℂ (AGrade phase 2 grade))
    (completedSeedDeviationFamily phase grade 0)
    (q23CoreConstantOperatorDerivative
      (LinearMap.id : ACore phase 2 →ₗ[ℂ] ACore phase 2))
    (q23SeedDeviationCoreDerivative phase 0)
    contDiffOn_const (completedSeedDeviationFamily_contDiffOn phase grade 0)
    (fun j p _ dp f => iteratedFDeriv_const_operator_core
      (q23ACoreEta phase 2 grade) (q23ACoreEta phase 2 grade)
      (ContinuousLinearMap.id ℂ (AGrade phase 2 grade)) LinearMap.id
      (fun value => rfl) j p dp f)
    (fun j p hp dp f => completedSeedDeviationFamily_all_orders_core
      phase grade 0 j p hp dp f)
    order parameter inside directions field

/-- Core tower for the actual completed transpose `M_pᵀ`. -/
def q23SeedTransposeMatrixCoreDerivative (phase : PhaseParameters) :
    (order : ℕ) → Seed.Parameters →
      (Fin order → Seed.Parameters) → ACore phase 2 →ₗ[ℂ] ACore phase 2 :=
  q23CoreOperatorAddDerivative
    (q23CoreConstantOperatorDerivative (LinearMap.id : ACore phase 2 →ₗ[ℂ] ACore phase 2))
    (q23SeedTransposeCoreDerivative phase 0)

theorem completedSeedTransposeFamily_all_orders_core (phase : PhaseParameters)
    (grade order : ℕ) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 2) :
    iteratedFDeriv ℝ order (completedSeedTransposeFamily phase grade)
        parameter directions (q23ACoreEta phase 2 grade field) =
      q23ACoreEta phase 2 grade
        (q23SeedTransposeMatrixCoreDerivative phase order parameter directions field) := by
  unfold completedSeedTransposeFamily q23SeedTransposeMatrixCoreDerivative
  exact iteratedFDeriv_operator_add_core
    (q23ACoreEta phase 2 grade) (q23ACoreEta phase 2 grade)
    (fun _ : Seed.Parameters => ContinuousLinearMap.id ℂ (AGrade phase 2 grade))
    (completedSeedTransposeDeviationFamily phase grade 0)
    (q23CoreConstantOperatorDerivative
      (LinearMap.id : ACore phase 2 →ₗ[ℂ] ACore phase 2))
    (q23SeedTransposeCoreDerivative phase 0)
    contDiffOn_const (completedSeedTransposeDeviationFamily_contDiffOn phase grade 0)
    (fun j p _ dp f => iteratedFDeriv_const_operator_core
      (q23ACoreEta phase 2 grade) (q23ACoreEta phase 2 grade)
      (ContinuousLinearMap.id ℂ (AGrade phase 2 grade)) LinearMap.id
      (fun value => rfl) j p dp f)
    (fun j p hp dp f => completedSeedTransposeDeviationFamily_all_orders_core
      phase grade 0 j p hp dp f)
    order parameter inside directions field

end Grad.NonlinearQuotientBounds
