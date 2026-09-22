import Q23SeedTransferCompositeTower

noncomputable section

set_option maxRecDepth 7000
set_option maxHeartbeats 4800000

open Set
open scoped BigOperators ContDiff

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers Grad.Constraints.Gauges Grad.Constraints.Seed

/-- The fixed inverse at the reference seed, viewed as a constant core
parameter-derivative tower. -/
def q23SeedInverseFixedCoreDerivative (phase : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) :
    (order : ℕ) → Seed.Parameters →
      (Fin order → Seed.Parameters) → ACore phase 2 →ₗ[ℂ] ACore phase 2 :=
  q23CoreConstantOperatorDerivative (seedInverseCore phase reference insideR)

theorem completedSeedInverseFixed_all_orders_core
    (phase : PhaseParameters) (grade : ℕ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (order : ℕ)
    (parameter : Seed.Parameters) (directions : Fin order → Seed.Parameters)
    (field : ACore phase 2) :
    iteratedFDeriv ℝ order
        (fun _ : Seed.Parameters => completedSeedInverseFixed phase grade reference)
        parameter directions (q23ACoreEta phase 2 grade field) =
      q23ACoreEta phase 2 grade
        (q23SeedInverseFixedCoreDerivative phase reference insideR
          order parameter directions field) := by
  exact iteratedFDeriv_const_operator_core
    (q23ACoreEta phase 2 grade) (q23ACoreEta phase 2 grade)
    (completedSeedInverseFixed phase grade reference)
    (seedInverseCore phase reference insideR)
    (fun value => completedSeedInverseFixed_core phase grade reference insideR value)
    order parameter directions field

/-- Derivative tower for `slice_p ∘ M_ref⁻¹`. -/
def q23SliceInverseCoreDerivative (phase : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) :
    (order : ℕ) → Seed.Parameters →
      (Fin order → Seed.Parameters) → ACore phase 2 →ₗ[ℂ] ACore phase 2 :=
  q23CoreOperatorCompositionDerivative
    (q23SeedSliceCoreDerivative phase)
    (q23SeedInverseFixedCoreDerivative phase reference insideR)

theorem completedSliceInverseFamily_all_orders_core
    (phase : PhaseParameters) (grade : ℕ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (order : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 2) :
    iteratedFDeriv ℝ order
        (fun point => (completedSeedSliceFamily phase grade point).comp
          (completedSeedInverseFixed phase grade reference))
        parameter directions (q23ACoreEta phase 2 grade field) =
      q23ACoreEta phase 2 grade
        (q23SliceInverseCoreDerivative phase reference insideR
          order parameter directions field) := by
  exact iteratedFDeriv_operator_comp_core
    (q23ACoreEta phase 2 grade) (q23ACoreEta phase 2 grade)
    (q23ACoreEta phase 2 grade)
    (completedSeedSliceFamily phase grade)
    (fun _ : Seed.Parameters => completedSeedInverseFixed phase grade reference)
    (q23SeedSliceCoreDerivative phase)
    (q23SeedInverseFixedCoreDerivative phase reference insideR)
    (completedSeedSliceFamily_contDiffOn phase grade) contDiffOn_const
    (fun j p hp dp f => completedSeedSliceFamily_all_orders_core phase grade j p hp dp f)
    (fun j p _ dp f => completedSeedInverseFixed_all_orders_core
      phase grade reference insideR j p dp f)
    order parameter inside directions field

/-- All seed derivatives of the completed planar transfer. -/
def q23PlanarTransferCoreDerivative (phase : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) :
    (order : ℕ) → Seed.Parameters →
      (Fin order → Seed.Parameters) → ACore phase 2 →ₗ[ℂ] ACore phase 2 :=
  q23CoreOperatorCompositionDerivative
    (q23SeedMatrixCoreDerivative phase)
    (q23SliceInverseCoreDerivative phase reference insideR)

theorem completedPlanarTransferFamily_all_orders_core
    (phase : PhaseParameters) (grade : ℕ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (order : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 2) :
    iteratedFDeriv ℝ order (completedPlanarTransferFamily phase grade reference)
        parameter directions (q23ACoreEta phase 2 grade field) =
      q23ACoreEta phase 2 grade
        (q23PlanarTransferCoreDerivative phase reference insideR
          order parameter directions field) := by
  unfold completedPlanarTransferFamily
  exact iteratedFDeriv_operator_comp_core
    (q23ACoreEta phase 2 grade) (q23ACoreEta phase 2 grade)
    (q23ACoreEta phase 2 grade)
    (completedSeedMatrixFamily phase grade)
    (fun point => (completedSeedSliceFamily phase grade point).comp
      (completedSeedInverseFixed phase grade reference))
    (q23SeedMatrixCoreDerivative phase)
    (q23SliceInverseCoreDerivative phase reference insideR)
    (completedSeedMatrixFamily_contDiffOn phase grade)
    (q23ContDiffOn_complexCLM_comp (completedSeedSliceFamily_contDiffOn phase grade)
      (contDiffOn_const : ContDiffOn ℝ ∞
        (fun _ : Seed.Parameters => completedSeedInverseFixed phase grade reference)
          Seed.parameterDomain))
    (fun j p hp dp f => completedSeedMatrixFamily_all_orders_core phase grade j p hp dp f)
    (fun j p hp dp f => completedSliceInverseFamily_all_orders_core
      phase grade reference insideR j p hp dp f)
    order parameter inside directions field

/-- Constant derivative tower of a fixed value map. -/
def q23ValueMapCoreDerivative (phase : PhaseParameters) {source target : ℕ}
    (mapping : ComplexEuclidean source →L[ℂ] ComplexEuclidean target) :
    (order : ℕ) → Seed.Parameters → (Fin order → Seed.Parameters) →
      ACore phase source →ₗ[ℂ] ACore phase target :=
  q23CoreConstantOperatorDerivative
    (Grad.Constraints.valueMapCore mapping phase)

theorem q23ValueMapCompleted_all_orders_core
    (phase : PhaseParameters) {source target grade : ℕ}
    (mapping : ComplexEuclidean source →L[ℂ] ComplexEuclidean target)
    (order : ℕ) (parameter : Seed.Parameters)
    (directions : Fin order → Seed.Parameters) (field : ACore phase source) :
    iteratedFDeriv ℝ order
        (fun _ : Seed.Parameters => q23ValueMapCompleted (grade := grade) phase mapping)
        parameter directions (q23ACoreEta phase source grade field) =
      q23ACoreEta phase target grade
        (q23ValueMapCoreDerivative phase mapping order parameter directions field) := by
  exact iteratedFDeriv_const_operator_core
    (q23ACoreEta phase source grade) (q23ACoreEta phase target grade)
    (q23ValueMapCompleted (grade := grade) phase mapping)
    (Grad.Constraints.valueMapCore mapping phase)
    (fun value => q23ValueMapCompleted_core phase mapping value)
    order parameter directions field

/-- Derivatives of the planar-transfer term after its fixed input projection. -/
def q23PlanarInputCoreDerivative (phase : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) :
    (order : ℕ) → Seed.Parameters →
      (Fin order → Seed.Parameters) → ACore phase 3 →ₗ[ℂ] ACore phase 2 :=
  q23CoreOperatorCompositionDerivative
    (q23PlanarTransferCoreDerivative phase reference insideR)
    (q23ValueMapCoreDerivative phase planarPartMap)

theorem completedPlanarInputFamily_all_orders_core
    (phase : PhaseParameters) (grade : ℕ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (order : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 3) :
    iteratedFDeriv ℝ order
        (fun point => (completedPlanarTransferFamily phase grade reference point).comp
          (q23ValueMapCompleted (grade := grade) phase planarPartMap))
        parameter directions (q23ACoreEta phase 3 grade field) =
      q23ACoreEta phase 2 grade
        (q23PlanarInputCoreDerivative phase reference insideR
          order parameter directions field) := by
  exact iteratedFDeriv_operator_comp_core
    (q23ACoreEta phase 3 grade) (q23ACoreEta phase 2 grade)
    (q23ACoreEta phase 2 grade)
    (completedPlanarTransferFamily phase grade reference)
    (fun _ : Seed.Parameters => q23ValueMapCompleted (grade := grade) phase planarPartMap)
    (q23PlanarTransferCoreDerivative phase reference insideR)
    (q23ValueMapCoreDerivative phase planarPartMap)
    (completedPlanarTransferFamily_contDiffOn phase grade reference) contDiffOn_const
    (fun j p hp dp f => completedPlanarTransferFamily_all_orders_core
      phase grade reference insideR j p hp dp f)
    (fun j p _ dp f => q23ValueMapCompleted_all_orders_core
      phase planarPartMap j p dp f)
    order parameter inside directions field

end Grad.NonlinearQuotientBounds
