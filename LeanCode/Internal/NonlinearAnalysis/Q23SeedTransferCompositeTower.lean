import Q23SeedTransferCoreTower

noncomputable section

set_option maxRecDepth 6000
set_option maxHeartbeats 4000000

open Set
open scoped BigOperators ContDiff

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers Grad.Constraints.Gauges Grad.Constraints.Seed

/-- Total core representative of every seed derivative of the `M'ᵀ` dot
operator. -/
def q23DerivativeDotCoreDerivative (phase : PhaseParameters) (order : ℕ)
    (parameter : Seed.Parameters) (directions : Fin order → Seed.Parameters) :
    ACore phase 2 →ₗ[ℂ] ACore phase 1 := by
  classical
  exact if inside : parameter ∈ Seed.parameterDomain then
      seedDerivativeDotParameterDerivative phase order parameter inside directions
    else 0

theorem q23DerivativeDotCoreDerivative_of_inside (phase : PhaseParameters)
    (order : ℕ) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    q23DerivativeDotCoreDerivative phase order parameter directions =
      seedDerivativeDotParameterDerivative phase order parameter inside directions := by
  classical
  simp only [q23DerivativeDotCoreDerivative, dif_pos inside]

theorem iteratedFDeriv_completedSeedDerivativeDotFamily
    (phase : PhaseParameters) (grade order : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    iteratedFDeriv ℝ order (completedSeedDerivativeDotFamily phase grade)
        parameter directions =
      completedDerivativeDotParameterDerivative phase grade order parameter directions := by
  have weightedSmooth :=
    (Seed.weightedSeedFamilies_contDiffOn phase grade 2).contDiffAt
      (Seed.parameterDomain_isOpen.mem_nhds inside)
  exact q23IteratedFDeriv_linearFunction_comp
    (fun sequence => ((derivativeDotLift phase grade).comp
      (weightedCompletedTransposeMap phase grade)) sequence)
    (fun x y => ((derivativeDotLift phase grade).comp
      (weightedCompletedTransposeMap phase grade)).map_add x y)
    (fun r x => by
      apply ContinuousLinearMap.ext
      intro field
      exact congrArg
        (fun operator : AGrade phase 2 grade →L[ℂ] AGrade phase 1 grade => operator field)
        ((((derivativeDotLift phase grade).comp
          (weightedCompletedTransposeMap phase grade)).restrictScalars ℝ).map_smul r x))
    ((derivativeDotLift phase grade).comp
      (weightedCompletedTransposeMap phase grade)).continuous
    (Seed.weightedSeedFamilies phase grade 2) parameter weightedSmooth order directions

theorem completedSeedDerivativeDotFamily_all_orders_core
    (phase : PhaseParameters) (grade order : ℕ) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 2) :
    iteratedFDeriv ℝ order (completedSeedDerivativeDotFamily phase grade)
        parameter directions (q23ACoreEta phase 2 grade field) =
      q23ACoreEta phase 1 grade
        (q23DerivativeDotCoreDerivative phase order parameter directions field) := by
  rw [iteratedFDeriv_completedSeedDerivativeDotFamily phase grade order parameter inside
      directions,
    q23DerivativeDotCoreDerivative_of_inside phase order parameter inside directions]
  change completedDerivativeDotParameterDerivative phase grade order parameter directions
      (aGradeEta phase (GradeCore.ofCoreLinear field)) =
    aGradeEta phase (GradeCore.ofCoreLinear
      (seedDerivativeDotParameterDerivative phase order parameter inside directions field))
  exact completedDerivativeDotParameterDerivative_core phase grade order parameter inside
    directions field

/-- Derivative tower for `M_pᵀ ∘ M_p`. -/
def q23TransposeMatrixCoreDerivative (phase : PhaseParameters) :
    (order : ℕ) → Seed.Parameters →
      (Fin order → Seed.Parameters) → ACore phase 2 →ₗ[ℂ] ACore phase 2 :=
  q23CoreOperatorCompositionDerivative
    (q23SeedTransposeMatrixCoreDerivative phase)
    (q23SeedMatrixCoreDerivative phase)

theorem completedTransposeMatrixFamily_all_orders_core
    (phase : PhaseParameters) (grade order : ℕ) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 2) :
    iteratedFDeriv ℝ order
        (fun point => (completedSeedTransposeFamily phase grade point).comp
          (completedSeedMatrixFamily phase grade point))
        parameter directions (q23ACoreEta phase 2 grade field) =
      q23ACoreEta phase 2 grade
        (q23TransposeMatrixCoreDerivative phase order parameter directions field) := by
  exact iteratedFDeriv_operator_comp_core
    (q23ACoreEta phase 2 grade) (q23ACoreEta phase 2 grade)
    (q23ACoreEta phase 2 grade)
    (completedSeedTransposeFamily phase grade) (completedSeedMatrixFamily phase grade)
    (q23SeedTransposeMatrixCoreDerivative phase) (q23SeedMatrixCoreDerivative phase)
    (completedSeedTransposeFamily_contDiffOn phase grade)
    (completedSeedMatrixFamily_contDiffOn phase grade)
    (fun j p hp dp f => completedSeedTransposeFamily_all_orders_core
      phase grade j p hp dp f)
    (fun j p hp dp f => completedSeedMatrixFamily_all_orders_core
      phase grade j p hp dp f)
    order parameter inside directions field

/-- Derivative tower for the tangential correction
`tangential ∘ M_pᵀ ∘ M_p`. -/
def q23TangentialCorrectionCoreDerivative (phase : PhaseParameters) :
    (order : ℕ) → Seed.Parameters →
      (Fin order → Seed.Parameters) → ACore phase 2 →ₗ[ℂ] ACore phase 2 :=
  q23CoreOperatorCompositionDerivative
    (q23CoreConstantOperatorDerivative (tangentialCore phase))
    (q23TransposeMatrixCoreDerivative phase)

theorem completedTangentialCorrectionFamily_all_orders_core
    (phase : PhaseParameters) (grade order : ℕ) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 2) :
    iteratedFDeriv ℝ order
        (fun point => (tangentialCompleted phase).comp
          ((completedSeedTransposeFamily phase grade point).comp
            (completedSeedMatrixFamily phase grade point)))
        parameter directions (q23ACoreEta phase 2 grade field) =
      q23ACoreEta phase 2 grade
        (q23TangentialCorrectionCoreDerivative phase order parameter directions field) := by
  exact iteratedFDeriv_operator_comp_core
    (q23ACoreEta phase 2 grade) (q23ACoreEta phase 2 grade)
    (q23ACoreEta phase 2 grade)
    (fun _ : Seed.Parameters => tangentialCompleted (grade := grade) phase)
    (fun point => (completedSeedTransposeFamily phase grade point).comp
      (completedSeedMatrixFamily phase grade point))
    (q23CoreConstantOperatorDerivative (tangentialCore phase))
    (q23TransposeMatrixCoreDerivative phase)
    contDiffOn_const
    (q23ContDiffOn_complexCLM_comp
      (completedSeedTransposeFamily_contDiffOn phase grade)
      (completedSeedMatrixFamily_contDiffOn phase grade))
    (fun j p _ dp f => iteratedFDeriv_const_operator_core
      (q23ACoreEta phase 2 grade) (q23ACoreEta phase 2 grade)
      (tangentialCompleted (grade := grade) phase) (tangentialCore phase)
      (fun value => tangentialCompleted_eta phase (GradeCore.ofCoreLinear value))
      j p dp f)
    (fun j p hp dp f => completedTransposeMatrixFamily_all_orders_core
      phase grade j p hp dp f)
    order parameter inside directions field

/-- Derivative tower of the literal slice projection. -/
def q23SeedSliceCoreDerivative (phase : PhaseParameters) :
    (order : ℕ) → Seed.Parameters →
      (Fin order → Seed.Parameters) → ACore phase 2 →ₗ[ℂ] ACore phase 2 :=
  q23CoreOperatorSubDerivative
    (q23CoreConstantOperatorDerivative (LinearMap.id : ACore phase 2 →ₗ[ℂ] ACore phase 2))
    (q23TangentialCorrectionCoreDerivative phase)

theorem completedSeedSliceFamily_all_orders_core
    (phase : PhaseParameters) (grade order : ℕ) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 2) :
    iteratedFDeriv ℝ order (completedSeedSliceFamily phase grade)
        parameter directions (q23ACoreEta phase 2 grade field) =
      q23ACoreEta phase 2 grade
        (q23SeedSliceCoreDerivative phase order parameter directions field) := by
  unfold completedSeedSliceFamily q23SeedSliceCoreDerivative
  exact iteratedFDeriv_operator_sub_core
    (q23ACoreEta phase 2 grade) (q23ACoreEta phase 2 grade)
    (fun _ : Seed.Parameters => ContinuousLinearMap.id ℂ (AGrade phase 2 grade))
    (fun point => (tangentialCompleted phase).comp
      ((completedSeedTransposeFamily phase grade point).comp
        (completedSeedMatrixFamily phase grade point)))
    (q23CoreConstantOperatorDerivative
      (LinearMap.id : ACore phase 2 →ₗ[ℂ] ACore phase 2))
    (q23TangentialCorrectionCoreDerivative phase)
    contDiffOn_const
    (q23ContDiffOn_complexCLM_comp
      (contDiffOn_const : ContDiffOn ℝ ∞
        (fun _ : Seed.Parameters => tangentialCompleted (grade := grade) phase)
          Seed.parameterDomain)
      (q23ContDiffOn_complexCLM_comp
        (completedSeedTransposeFamily_contDiffOn phase grade)
        (completedSeedMatrixFamily_contDiffOn phase grade)))
    (fun j p _ dp f => iteratedFDeriv_const_operator_core
      (q23ACoreEta phase 2 grade) (q23ACoreEta phase 2 grade)
      (ContinuousLinearMap.id ℂ (AGrade phase 2 grade)) LinearMap.id
      (fun value => rfl) j p dp f)
    (fun j p hp dp f => completedTangentialCorrectionFamily_all_orders_core
      phase grade j p hp dp f)
    order parameter inside directions field

end Grad.NonlinearQuotientBounds
