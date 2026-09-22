import Q23SeedTransferFullTower

noncomputable section

set_option maxRecDepth 7000
set_option maxHeartbeats 4800000

open Set
open scoped BigOperators ContDiff

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers Grad.Constraints.Gauges Grad.Constraints.Seed

def q23PlanarOutputFamily (phase : PhaseParameters) (grade : ℕ)
    (reference parameter : Seed.Parameters) :
    AGrade phase 3 grade →L[ℂ] AGrade phase 3 grade :=
  (q23ValueMapCompleted (grade := grade) phase planarInclusionMap).comp
    ((completedPlanarTransferFamily phase grade reference parameter).comp
      (q23ValueMapCompleted (grade := grade) phase planarPartMap))

def q23PlanarOutputCoreDerivative (phase : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) :
    (order : ℕ) → Seed.Parameters → (Fin order → Seed.Parameters) →
      ACore phase 3 →ₗ[ℂ] ACore phase 3 :=
  q23CoreOperatorCompositionDerivative
    (q23ValueMapCoreDerivative phase planarInclusionMap)
    (q23PlanarInputCoreDerivative phase reference insideR)

theorem q23PlanarOutputFamily_all_orders_core
    (phase : PhaseParameters) (grade : ℕ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (order : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 3) :
    iteratedFDeriv ℝ order (q23PlanarOutputFamily phase grade reference)
        parameter directions (q23ACoreEta phase 3 grade field) =
      q23ACoreEta phase 3 grade
        (q23PlanarOutputCoreDerivative phase reference insideR
          order parameter directions field) := by
  exact iteratedFDeriv_operator_comp_core
    (q23ACoreEta phase 3 grade) (q23ACoreEta phase 2 grade)
    (q23ACoreEta phase 3 grade)
    (fun _ : Seed.Parameters =>
      q23ValueMapCompleted (grade := grade) phase planarInclusionMap)
    (fun point => (completedPlanarTransferFamily phase grade reference point).comp
      (q23ValueMapCompleted (grade := grade) phase planarPartMap))
    (q23ValueMapCoreDerivative phase planarInclusionMap)
    (q23PlanarInputCoreDerivative phase reference insideR)
    contDiffOn_const
    (q23ContDiffOn_complexCLM_comp
      (completedPlanarTransferFamily_contDiffOn phase grade reference) contDiffOn_const)
    (fun j p _ dp f => q23ValueMapCompleted_all_orders_core
      phase planarInclusionMap j p dp f)
    (fun j p hp dp f => completedPlanarInputFamily_all_orders_core
      phase grade reference insideR j p hp dp f)
    order parameter inside directions field

def q23DotPlanarFamily (phase : PhaseParameters) (grade : ℕ)
    (reference parameter : Seed.Parameters) :
    AGrade phase 3 grade →L[ℂ] AGrade phase 1 grade :=
  (completedSeedDerivativeDotFamily phase grade parameter).comp
    ((completedPlanarTransferFamily phase grade reference parameter).comp
      (q23ValueMapCompleted (grade := grade) phase planarPartMap))

def q23DotPlanarCoreDerivative (phase : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) :
    (order : ℕ) → Seed.Parameters → (Fin order → Seed.Parameters) →
      ACore phase 3 →ₗ[ℂ] ACore phase 1 :=
  q23CoreOperatorCompositionDerivative
    (q23DerivativeDotCoreDerivative phase)
    (q23PlanarInputCoreDerivative phase reference insideR)

theorem q23DotPlanarFamily_all_orders_core
    (phase : PhaseParameters) (grade : ℕ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (order : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 3) :
    iteratedFDeriv ℝ order (q23DotPlanarFamily phase grade reference)
        parameter directions (q23ACoreEta phase 3 grade field) =
      q23ACoreEta phase 1 grade
        (q23DotPlanarCoreDerivative phase reference insideR
          order parameter directions field) := by
  exact iteratedFDeriv_operator_comp_core
    (q23ACoreEta phase 3 grade) (q23ACoreEta phase 2 grade)
    (q23ACoreEta phase 1 grade)
    (completedSeedDerivativeDotFamily phase grade)
    (fun point => (completedPlanarTransferFamily phase grade reference point).comp
      (q23ValueMapCompleted (grade := grade) phase planarPartMap))
    (q23DerivativeDotCoreDerivative phase)
    (q23PlanarInputCoreDerivative phase reference insideR)
    (completedSeedDerivativeDotFamily_contDiffOn phase grade)
    (q23ContDiffOn_complexCLM_comp
      (completedPlanarTransferFamily_contDiffOn phase grade reference) contDiffOn_const)
    (fun j p hp dp f => completedSeedDerivativeDotFamily_all_orders_core
      phase grade j p hp dp f)
    (fun j p hp dp f => completedPlanarInputFamily_all_orders_core
      phase grade reference insideR j p hp dp f)
    order parameter inside directions field

def q23ScaledAngularCompleted (phase : PhaseParameters) (grade : ℕ) :
    AGrade phase 1 grade →L[ℂ] AGrade phase 1 grade :=
  (phase.length⁻¹ : ℂ) • angularCompleted (dimension := 1) (grade := grade) phase 0

def q23ScaledAngularCore (phase : PhaseParameters) :
    ACore phase 1 →ₗ[ℂ] ACore phase 1 :=
  (phase.length⁻¹ : ℂ) • angularCore phase 0

theorem q23ScaledAngularCompleted_core (phase : PhaseParameters) (grade : ℕ)
    (field : ACore phase 1) :
    q23ScaledAngularCompleted phase grade (q23ACoreEta phase 1 grade field) =
      q23ACoreEta phase 1 grade (q23ScaledAngularCore phase field) := by
  simp only [q23ScaledAngularCompleted, q23ScaledAngularCore, smul_apply,
    LinearMap.smul_apply, map_smul]
  change (phase.length⁻¹ : ℂ) •
      angularCompleted (dimension := 1) (grade := grade) phase 0
        (aGradeEta phase (GradeCore.ofCoreLinear field)) =
    (phase.length⁻¹ : ℂ) •
      aGradeEta phase (GradeCore.ofCoreLinear (angularCore phase 0 field))
  rw [angularCompleted_eta]
  rfl

def q23MeanDotCoreDerivative (phase : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) :
    (order : ℕ) → Seed.Parameters → (Fin order → Seed.Parameters) →
      ACore phase 3 →ₗ[ℂ] ACore phase 1 :=
  q23CoreOperatorCompositionDerivative
    (q23CoreConstantOperatorDerivative (q23ScaledAngularCore phase))
    (q23DotPlanarCoreDerivative phase reference insideR)

theorem q23MeanDotFamily_all_orders_core
    (phase : PhaseParameters) (grade : ℕ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (order : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 3) :
    iteratedFDeriv ℝ order
        (fun point => (q23ScaledAngularCompleted phase grade).comp
          (q23DotPlanarFamily phase grade reference point))
        parameter directions (q23ACoreEta phase 3 grade field) =
      q23ACoreEta phase 1 grade
        (q23MeanDotCoreDerivative phase reference insideR
          order parameter directions field) := by
  exact iteratedFDeriv_operator_comp_core
    (q23ACoreEta phase 3 grade) (q23ACoreEta phase 1 grade)
    (q23ACoreEta phase 1 grade)
    (fun _ : Seed.Parameters => q23ScaledAngularCompleted phase grade)
    (q23DotPlanarFamily phase grade reference)
    (q23CoreConstantOperatorDerivative (q23ScaledAngularCore phase))
    (q23DotPlanarCoreDerivative phase reference insideR)
    contDiffOn_const
    (q23ContDiffOn_complexCLM_comp
      (completedSeedDerivativeDotFamily_contDiffOn phase grade)
      (q23ContDiffOn_complexCLM_comp
        (completedPlanarTransferFamily_contDiffOn phase grade reference) contDiffOn_const))
    (fun j p _ dp f => iteratedFDeriv_const_operator_core
      (q23ACoreEta phase 1 grade) (q23ACoreEta phase 1 grade)
      (q23ScaledAngularCompleted phase grade) (q23ScaledAngularCore phase)
      (q23ScaledAngularCompleted_core phase grade) j p dp f)
    (fun j p hp dp f => q23DotPlanarFamily_all_orders_core
      phase grade reference insideR j p hp dp f)
    order parameter inside directions field

def q23ToroidalFixedCompleted (phase : PhaseParameters) (grade : ℕ) :
    AGrade phase 3 grade →L[ℂ] AGrade phase 1 grade :=
  let toroidalPart := q23ValueMapCompleted (grade := grade) phase toroidalPartMap
  toroidalPart -
    (angularCompleted (dimension := 1) (grade := grade) phase 0).comp toroidalPart

def q23ToroidalFixedCore (phase : PhaseParameters) :
    ACore phase 3 →ₗ[ℂ] ACore phase 1 :=
  let toroidalPart := Grad.Constraints.valueMapCore toroidalPartMap phase
  toroidalPart - (angularCore phase 0).comp toroidalPart

theorem q23ToroidalFixedCompleted_core (phase : PhaseParameters) (grade : ℕ)
    (field : ACore phase 3) :
    q23ToroidalFixedCompleted phase grade (q23ACoreEta phase 3 grade field) =
      q23ACoreEta phase 1 grade (q23ToroidalFixedCore phase field) := by
  simp only [q23ToroidalFixedCompleted, q23ToroidalFixedCore, sub_apply,
    LinearMap.sub_apply, ContinuousLinearMap.comp_apply, LinearMap.comp_apply]
  change q23ValueMapCompleted (grade := grade) phase toroidalPartMap
        (aGradeEta phase (GradeCore.ofCoreLinear field)) -
      angularCompleted (dimension := 1) (grade := grade) phase 0
        (q23ValueMapCompleted (grade := grade) phase toroidalPartMap
          (aGradeEta phase (GradeCore.ofCoreLinear field))) =
    aGradeEta phase (GradeCore.ofCoreLinear
      (Grad.Constraints.valueMapCore toroidalPartMap phase field -
        angularCore phase 0
          (Grad.Constraints.valueMapCore toroidalPartMap phase field)))
  rw [q23ValueMapCompleted_core, angularCompleted_eta, ← map_sub]
  congr 1

def q23ToroidalInnerCoreDerivative (phase : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) :
    (order : ℕ) → Seed.Parameters → (Fin order → Seed.Parameters) →
      ACore phase 3 →ₗ[ℂ] ACore phase 1 :=
  q23CoreOperatorSubDerivative
    (q23CoreConstantOperatorDerivative (q23ToroidalFixedCore phase))
    (q23MeanDotCoreDerivative phase reference insideR)

theorem q23ToroidalInnerFamily_all_orders_core
    (phase : PhaseParameters) (grade : ℕ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (order : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 3) :
    iteratedFDeriv ℝ order
        (fun point => q23ToroidalFixedCompleted phase grade -
          (q23ScaledAngularCompleted phase grade).comp
            (q23DotPlanarFamily phase grade reference point))
        parameter directions (q23ACoreEta phase 3 grade field) =
      q23ACoreEta phase 1 grade
        (q23ToroidalInnerCoreDerivative phase reference insideR
          order parameter directions field) := by
  exact iteratedFDeriv_operator_sub_core
    (q23ACoreEta phase 3 grade) (q23ACoreEta phase 1 grade)
    (fun _ : Seed.Parameters => q23ToroidalFixedCompleted phase grade)
    (fun point => (q23ScaledAngularCompleted phase grade).comp
      (q23DotPlanarFamily phase grade reference point))
    (q23CoreConstantOperatorDerivative (q23ToroidalFixedCore phase))
    (q23MeanDotCoreDerivative phase reference insideR)
    contDiffOn_const
    (q23ContDiffOn_complexCLM_comp contDiffOn_const
      (q23ContDiffOn_complexCLM_comp
        (completedSeedDerivativeDotFamily_contDiffOn phase grade)
        (q23ContDiffOn_complexCLM_comp
          (completedPlanarTransferFamily_contDiffOn phase grade reference) contDiffOn_const)))
    (fun j p _ dp f => iteratedFDeriv_const_operator_core
      (q23ACoreEta phase 3 grade) (q23ACoreEta phase 1 grade)
      (q23ToroidalFixedCompleted phase grade) (q23ToroidalFixedCore phase)
      (q23ToroidalFixedCompleted_core phase grade) j p dp f)
    (fun j p hp dp f => q23MeanDotFamily_all_orders_core
      phase grade reference insideR j p hp dp f)
    order parameter inside directions field

def q23ToroidalOutputCoreDerivative (phase : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) :
    (order : ℕ) → Seed.Parameters → (Fin order → Seed.Parameters) →
      ACore phase 3 →ₗ[ℂ] ACore phase 3 :=
  q23CoreOperatorCompositionDerivative
    (q23ValueMapCoreDerivative phase toroidalInclusionMap)
    (q23ToroidalInnerCoreDerivative phase reference insideR)

theorem q23ToroidalOutputFamily_all_orders_core
    (phase : PhaseParameters) (grade : ℕ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (order : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 3) :
    iteratedFDeriv ℝ order
        (fun point =>
          (q23ValueMapCompleted (grade := grade) phase toroidalInclusionMap).comp
            (q23ToroidalFixedCompleted phase grade -
              (q23ScaledAngularCompleted phase grade).comp
                (q23DotPlanarFamily phase grade reference point)))
        parameter directions (q23ACoreEta phase 3 grade field) =
      q23ACoreEta phase 3 grade
        (q23ToroidalOutputCoreDerivative phase reference insideR
          order parameter directions field) := by
  exact iteratedFDeriv_operator_comp_core
    (q23ACoreEta phase 3 grade) (q23ACoreEta phase 1 grade)
    (q23ACoreEta phase 3 grade)
    (fun _ : Seed.Parameters =>
      q23ValueMapCompleted (grade := grade) phase toroidalInclusionMap)
    (fun point => q23ToroidalFixedCompleted phase grade -
      (q23ScaledAngularCompleted phase grade).comp
        (q23DotPlanarFamily phase grade reference point))
    (q23ValueMapCoreDerivative phase toroidalInclusionMap)
    (q23ToroidalInnerCoreDerivative phase reference insideR)
    contDiffOn_const
    (contDiffOn_const.sub
      (q23ContDiffOn_complexCLM_comp contDiffOn_const
        (q23ContDiffOn_complexCLM_comp
          (completedSeedDerivativeDotFamily_contDiffOn phase grade)
          (q23ContDiffOn_complexCLM_comp
            (completedPlanarTransferFamily_contDiffOn phase grade reference)
            contDiffOn_const))))
    (fun j p _ dp f => q23ValueMapCompleted_all_orders_core
      phase toroidalInclusionMap j p dp f)
    (fun j p hp dp f => q23ToroidalInnerFamily_all_orders_core
      phase grade reference insideR j p hp dp f)
    order parameter inside directions field

def q23ReassembledSeedTransferFamily (phase : PhaseParameters) (grade : ℕ)
    (reference parameter : Seed.Parameters) :
    AGrade phase 3 grade →L[ℂ] AGrade phase 3 grade :=
  q23PlanarOutputFamily phase grade reference parameter +
    (q23ValueMapCompleted (grade := grade) phase toroidalInclusionMap).comp
      (q23ToroidalFixedCompleted phase grade -
        (q23ScaledAngularCompleted phase grade).comp
          (q23DotPlanarFamily phase grade reference parameter))

def q23SeedTransferCoreDerivative (phase : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) :
    (order : ℕ) → Seed.Parameters → (Fin order → Seed.Parameters) →
      ACore phase 3 →ₗ[ℂ] ACore phase 3 :=
  q23CoreOperatorAddDerivative
    (q23PlanarOutputCoreDerivative phase reference insideR)
    (q23ToroidalOutputCoreDerivative phase reference insideR)

theorem q23ReassembledSeedTransferFamily_eq
    (phase : PhaseParameters) (grade : ℕ) (reference parameter : Seed.Parameters) :
    q23ReassembledSeedTransferFamily phase grade reference parameter =
      completedSeedTransferFamily phase grade reference parameter := by
  rfl

/-- Every literal Fréchet derivative of the completed N18 seed-transfer family
preserves the accepted all-grade core, with the explicit allocation tower. -/
theorem completedSeedTransferFamily_all_orders_core
    (phase : PhaseParameters) (grade : ℕ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (order : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 3) :
    completedSeedTransferParameterDerivative phase grade order reference parameter directions
        (q23ACoreEta phase 3 grade field) =
      q23ACoreEta phase 3 grade
        (q23SeedTransferCoreDerivative phase reference insideR
          order parameter directions field) := by
  unfold completedSeedTransferParameterDerivative
  have families : completedSeedTransferFamily phase grade reference =
      q23ReassembledSeedTransferFamily phase grade reference := by
    funext point
    exact (q23ReassembledSeedTransferFamily_eq phase grade reference point).symm
  rw [families]
  change iteratedFDeriv ℝ order
      (fun point => q23PlanarOutputFamily phase grade reference point +
        (q23ValueMapCompleted (grade := grade) phase toroidalInclusionMap).comp
          (q23ToroidalFixedCompleted phase grade -
            (q23ScaledAngularCompleted phase grade).comp
              (q23DotPlanarFamily phase grade reference point)))
      parameter directions (q23ACoreEta phase 3 grade field) = _
  exact iteratedFDeriv_operator_add_core
    (q23ACoreEta phase 3 grade) (q23ACoreEta phase 3 grade)
    (q23PlanarOutputFamily phase grade reference)
    (fun point =>
      (q23ValueMapCompleted (grade := grade) phase toroidalInclusionMap).comp
        (q23ToroidalFixedCompleted phase grade -
          (q23ScaledAngularCompleted phase grade).comp
            (q23DotPlanarFamily phase grade reference point)))
    (q23PlanarOutputCoreDerivative phase reference insideR)
    (q23ToroidalOutputCoreDerivative phase reference insideR)
    (q23ContDiffOn_complexCLM_comp contDiffOn_const
      (q23ContDiffOn_complexCLM_comp
        (completedPlanarTransferFamily_contDiffOn phase grade reference) contDiffOn_const))
    (q23ContDiffOn_complexCLM_comp contDiffOn_const
      (contDiffOn_const.sub
        (q23ContDiffOn_complexCLM_comp contDiffOn_const
          (q23ContDiffOn_complexCLM_comp
            (completedSeedDerivativeDotFamily_contDiffOn phase grade)
            (q23ContDiffOn_complexCLM_comp
              (completedPlanarTransferFamily_contDiffOn phase grade reference)
              contDiffOn_const)))))
    (fun j p hp dp f => q23PlanarOutputFamily_all_orders_core
      phase grade reference insideR j p hp dp f)
    (fun j p hp dp f => q23ToroidalOutputFamily_all_orders_core
      phase grade reference insideR j p hp dp f)
    order parameter inside directions field

end Grad.NonlinearQuotientBounds
