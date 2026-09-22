import Q23Leibniz

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 2400000

open Set
open scoped BigOperators ContDiff

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Seed

/-- Composition of complex operators, bundled as a bounded real-bilinear map
on their operator spaces. -/
def q23ComplexCLMCompBilinear
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
    [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F] [IsScalarTower ℝ ℂ G] :
    (F →L[ℂ] G) →L[ℝ] (E →L[ℂ] F) →L[ℝ] (E →L[ℂ] G) :=
  (q23RestrictScalarsCLM (E := E →L[ℂ] F) (F := E →L[ℂ] G)).comp
    ((ContinuousLinearMap.compL ℂ E F G).restrictScalars ℝ)

@[simp]
theorem q23ComplexCLMCompBilinear_apply
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
    [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F] [IsScalarTower ℝ ℂ G]
    (outer : F →L[ℂ] G) (inner : E →L[ℂ] F) :
    q23ComplexCLMCompBilinear outer inner = outer.comp inner := rfl

/-- The core-side allocation formula for a composition of two
parameter-dependent operators. -/
def q23CoreOperatorCompositionDerivative
    {CoreE CoreF CoreG : Type*}
    [AddCommMonoid CoreE] [Module ℂ CoreE]
    [AddCommMonoid CoreF] [Module ℂ CoreF]
    [AddCommMonoid CoreG] [Module ℂ CoreG]
    (outerCore : (order : ℕ) → Seed.Parameters →
      (Fin order → Seed.Parameters) → CoreF →ₗ[ℂ] CoreG)
    (innerCore : (order : ℕ) → Seed.Parameters →
      (Fin order → Seed.Parameters) → CoreE →ₗ[ℂ] CoreF)
    (order : ℕ) (parameter : Seed.Parameters)
    (directions : Fin order → Seed.Parameters) : CoreE →ₗ[ℂ] CoreG :=
  ∑ assignment : Fin order → Fin 2,
    (outerCore (assignmentFiber assignment 0).card parameter
        (q23FiberTuple assignment 0 directions)).comp
      (innerCore (assignmentFiber assignment 1).card parameter
        (q23FiberTuple assignment 1 directions))

/-- Exact core preservation is stable under all parameter derivatives of
operator composition. -/
theorem iteratedFDeriv_operator_comp_core
    {CoreE CoreF CoreG E F G : Type*}
    [AddCommMonoid CoreE] [Module ℂ CoreE]
    [AddCommMonoid CoreF] [Module ℂ CoreF]
    [AddCommMonoid CoreG] [Module ℂ CoreG]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
    [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F] [IsScalarTower ℝ ℂ G]
    (etaE : CoreE →ₗ[ℂ] E) (etaF : CoreF →ₗ[ℂ] F) (etaG : CoreG →ₗ[ℂ] G)
    (outer : Seed.Parameters → F →L[ℂ] G)
    (inner : Seed.Parameters → E →L[ℂ] F)
    (outerCore : (order : ℕ) → Seed.Parameters →
      (Fin order → Seed.Parameters) → CoreF →ₗ[ℂ] CoreG)
    (innerCore : (order : ℕ) → Seed.Parameters →
      (Fin order → Seed.Parameters) → CoreE →ₗ[ℂ] CoreF)
    (outerSmooth : ContDiffOn ℝ ∞ outer Seed.parameterDomain)
    (innerSmooth : ContDiffOn ℝ ∞ inner Seed.parameterDomain)
    (outerAgrees : ∀ (order : ℕ) (parameter : Seed.Parameters),
      parameter ∈ Seed.parameterDomain →
      ∀ (directions : Fin order → Seed.Parameters) (field : CoreF),
        iteratedFDeriv ℝ order outer parameter directions (etaF field) =
          etaG (outerCore order parameter directions field))
    (innerAgrees : ∀ (order : ℕ) (parameter : Seed.Parameters),
      parameter ∈ Seed.parameterDomain →
      ∀ (directions : Fin order → Seed.Parameters) (field : CoreE),
        iteratedFDeriv ℝ order inner parameter directions (etaE field) =
          etaF (innerCore order parameter directions field))
    (order : ℕ) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : CoreE) :
    iteratedFDeriv ℝ order (fun point => (outer point).comp (inner point))
        parameter directions (etaE field) =
      etaG (q23CoreOperatorCompositionDerivative outerCore innerCore
        order parameter directions field) := by
  have allocation := iteratedFDeriv_bilinear_allocation_all_orders
    (q23ComplexCLMCompBilinear (E := E) (F := F) (G := G))
    outer inner Seed.parameterDomain Seed.parameterDomain_isOpen
    outerSmooth innerSmooth order parameter inside directions
  have evaluated := congrArg (fun mapping : E →L[ℂ] G => mapping (etaE field)) allocation
  rw [q23CoreOperatorCompositionDerivative]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  rw [map_sum]
  simpa only [q23ComplexCLMCompBilinear_apply, ContinuousLinearMap.comp_apply,
    sum_apply, LinearMap.sum_apply, LinearMap.comp_apply, outerAgrees _ parameter inside,
    innerAgrees _ parameter inside] using evaluated

/-- Core derivative tower of a constant complex operator family. -/
def q23CoreConstantOperatorDerivative
    {CoreE CoreF : Type*} [AddCommMonoid CoreE] [Module ℂ CoreE]
    [AddCommMonoid CoreF] [Module ℂ CoreF]
    (mapping : CoreE →ₗ[ℂ] CoreF) (order : ℕ)
    (_parameter : Seed.Parameters) (_directions : Fin order → Seed.Parameters) :
    CoreE →ₗ[ℂ] CoreF :=
  if order = 0 then mapping else 0

theorem iteratedFDeriv_const_operator_core
    {CoreE CoreF E F : Type*}
    [AddCommMonoid CoreE] [Module ℂ CoreE]
    [AddCommMonoid CoreF] [Module ℂ CoreF]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F]
    (etaE : CoreE →ₗ[ℂ] E) (etaF : CoreF →ₗ[ℂ] F)
    (mapping : E →L[ℂ] F) (coreMapping : CoreE →ₗ[ℂ] CoreF)
    (agrees : ∀ field, mapping (etaE field) = etaF (coreMapping field))
    (order : ℕ) (parameter : Seed.Parameters)
    (directions : Fin order → Seed.Parameters) (field : CoreE) :
    iteratedFDeriv ℝ order (fun _ : Seed.Parameters => mapping)
        parameter directions (etaE field) =
      etaF (q23CoreConstantOperatorDerivative coreMapping order parameter directions field) := by
  cases order with
  | zero =>
      simpa [q23CoreConstantOperatorDerivative] using agrees field
  | succ order =>
      rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero order) mapping]
      simp [q23CoreConstantOperatorDerivative]

/-- Pointwise sum of two core operator derivative towers. -/
def q23CoreOperatorAddDerivative
    {CoreE CoreF : Type*} [AddCommMonoid CoreE] [Module ℂ CoreE]
    [AddCommMonoid CoreF] [Module ℂ CoreF]
    (first second : (order : ℕ) → Seed.Parameters →
      (Fin order → Seed.Parameters) → CoreE →ₗ[ℂ] CoreF)
    (order : ℕ) (parameter : Seed.Parameters)
    (directions : Fin order → Seed.Parameters) : CoreE →ₗ[ℂ] CoreF :=
  first order parameter directions + second order parameter directions

theorem iteratedFDeriv_operator_add_core
    {CoreE CoreF E F : Type*}
    [AddCommMonoid CoreE] [Module ℂ CoreE]
    [AddCommMonoid CoreF] [Module ℂ CoreF]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F]
    (etaE : CoreE →ₗ[ℂ] E) (etaF : CoreF →ₗ[ℂ] F)
    (first second : Seed.Parameters → E →L[ℂ] F)
    (firstCore secondCore : (order : ℕ) → Seed.Parameters →
      (Fin order → Seed.Parameters) → CoreE →ₗ[ℂ] CoreF)
    (firstSmooth : ContDiffOn ℝ ∞ first Seed.parameterDomain)
    (secondSmooth : ContDiffOn ℝ ∞ second Seed.parameterDomain)
    (firstAgrees : ∀ (order : ℕ) (parameter : Seed.Parameters),
      parameter ∈ Seed.parameterDomain →
      ∀ (directions : Fin order → Seed.Parameters) (field : CoreE),
        iteratedFDeriv ℝ order first parameter directions (etaE field) =
          etaF (firstCore order parameter directions field))
    (secondAgrees : ∀ (order : ℕ) (parameter : Seed.Parameters),
      parameter ∈ Seed.parameterDomain →
      ∀ (directions : Fin order → Seed.Parameters) (field : CoreE),
        iteratedFDeriv ℝ order second parameter directions (etaE field) =
          etaF (secondCore order parameter directions field))
    (order : ℕ) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : CoreE) :
    iteratedFDeriv ℝ order (fun point => first point + second point)
        parameter directions (etaE field) =
      etaF (q23CoreOperatorAddDerivative firstCore secondCore
        order parameter directions field) := by
  change iteratedFDeriv ℝ order (first + second) parameter directions (etaE field) = _
  rw [iteratedFDeriv_add_apply
    ((firstSmooth.contDiffAt (Seed.parameterDomain_isOpen.mem_nhds inside)).of_le
      (show (order : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
    ((secondSmooth.contDiffAt (Seed.parameterDomain_isOpen.mem_nhds inside)).of_le
      (show (order : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))]
  simp only [add_apply, q23CoreOperatorAddDerivative, LinearMap.add_apply]
  rw [firstAgrees order parameter inside directions field,
    secondAgrees order parameter inside directions field, map_add]

/-- Pointwise difference of two core operator derivative towers. -/
def q23CoreOperatorSubDerivative
    {CoreE CoreF : Type*} [AddCommGroup CoreE] [Module ℂ CoreE]
    [AddCommGroup CoreF] [Module ℂ CoreF]
    (first second : (order : ℕ) → Seed.Parameters →
      (Fin order → Seed.Parameters) → CoreE →ₗ[ℂ] CoreF)
    (order : ℕ) (parameter : Seed.Parameters)
    (directions : Fin order → Seed.Parameters) : CoreE →ₗ[ℂ] CoreF :=
  first order parameter directions - second order parameter directions

theorem iteratedFDeriv_operator_sub_core
    {CoreE CoreF E F : Type*}
    [AddCommGroup CoreE] [Module ℂ CoreE]
    [AddCommGroup CoreF] [Module ℂ CoreF]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F]
    (etaE : CoreE →ₗ[ℂ] E) (etaF : CoreF →ₗ[ℂ] F)
    (first second : Seed.Parameters → E →L[ℂ] F)
    (firstCore secondCore : (order : ℕ) → Seed.Parameters →
      (Fin order → Seed.Parameters) → CoreE →ₗ[ℂ] CoreF)
    (firstSmooth : ContDiffOn ℝ ∞ first Seed.parameterDomain)
    (secondSmooth : ContDiffOn ℝ ∞ second Seed.parameterDomain)
    (firstAgrees : ∀ (order : ℕ) (parameter : Seed.Parameters),
      parameter ∈ Seed.parameterDomain →
      ∀ (directions : Fin order → Seed.Parameters) (field : CoreE),
        iteratedFDeriv ℝ order first parameter directions (etaE field) =
          etaF (firstCore order parameter directions field))
    (secondAgrees : ∀ (order : ℕ) (parameter : Seed.Parameters),
      parameter ∈ Seed.parameterDomain →
      ∀ (directions : Fin order → Seed.Parameters) (field : CoreE),
        iteratedFDeriv ℝ order second parameter directions (etaE field) =
          etaF (secondCore order parameter directions field))
    (order : ℕ) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : CoreE) :
    iteratedFDeriv ℝ order (fun point => first point - second point)
        parameter directions (etaE field) =
      etaF (q23CoreOperatorSubDerivative firstCore secondCore
        order parameter directions field) := by
  change iteratedFDeriv ℝ order (first - second) parameter directions (etaE field) = _
  rw [iteratedFDeriv_sub_apply
    ((firstSmooth.contDiffAt (Seed.parameterDomain_isOpen.mem_nhds inside)).of_le
      (show (order : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
    ((secondSmooth.contDiffAt (Seed.parameterDomain_isOpen.mem_nhds inside)).of_le
      (show (order : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))]
  simp only [sub_apply, q23CoreOperatorSubDerivative, LinearMap.sub_apply]
  rw [firstAgrees order parameter inside directions field,
    secondAgrees order parameter inside directions field, map_sub]

end Grad.NonlinearQuotientBounds
