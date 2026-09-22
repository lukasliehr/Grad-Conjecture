import Q23SeedTransferActual
import TameSeedField
import QuotientProductLinearity
import BanachAdapterSlot

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 2400000

open Set
open scoped ContDiff Topology

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers Grad.Constraints.Gauges Grad.Constraints.Seed
open Grad.NonlinearProduct

section Completion

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def q23ScalarSourceLinear : E →ₗ[ℝ] ((⊤ : Submodule ℝ ℝ) →ₗ[ℝ] E) where
  toFun value := (⊤ : Submodule ℝ ℝ).subtype.smulRight value
  map_add' first second := by ext scalar; exact smul_add _ _ _
  map_smul' scalar value := by ext source; exact smul_comm _ _ _

/-- The accepted slot-completion theorem specialized from an operator-valued
extension to an ordinary real multilinear map. -/
theorem q23MultilinearCompletion_exists (core : Submodule ℝ X)
    (dense : Dense (core : Set X)) (arity : ℕ)
    (mapping : MultilinearMap ℝ (fun _ : Fin arity => core) E)
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ arguments,
      ‖mapping arguments‖ ≤ constant * ∏ position, ‖arguments position‖) :
    ∃ completed : ContinuousMultilinearMap ℝ (fun _ : Fin arity => X) E,
      ∀ arguments : Fin arity → core,
        completed (fun position => (arguments position : X)) = mapping arguments := by
  let withSource : MultilinearMap ℝ (fun _ : Fin arity => core)
      ((⊤ : Submodule ℝ ℝ) →ₗ[ℝ] E) :=
    q23ScalarSourceLinear.compMultilinearMap mapping
  have sourceDense : Dense ((⊤ : Submodule ℝ ℝ) : Set ℝ) := dense_univ
  obtain ⟨completed, agrees⟩ := Grad.FiniteBanachCalculus.slotCompletion_exists
    dense sourceDense arity withSource constant nonnegative (by
      intro arguments source
      change ‖(source : ℝ) • mapping arguments‖ ≤ _
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left (bounded arguments)
        (norm_nonneg (source : ℝ))).trans_eq (by
          change ‖(source : ℝ)‖ * (constant * ∏ position, ‖arguments position‖) =
            constant * (∏ position, ‖arguments position‖) * ‖(source : ℝ)‖
          ring))
  refine ⟨(ContinuousLinearMap.apply ℝ E (1 : ℝ)).compContinuousMultilinearMap
    completed, ?_⟩
  intro arguments
  change completed (fun position => (arguments position : X)) (1 : ℝ) = _
  have equality := agrees arguments
    (⟨1, Submodule.mem_top⟩ : (⊤ : Submodule ℝ ℝ))
  change completed (fun position => (arguments position : X)) (1 : ℝ) =
    (1 : ℝ) • mapping arguments at equality
  simpa only [one_smul] using equality

end Completion

/-- The all-grade smooth core embedded into one completed original grade. -/
def q23FieldEmbed (phase : PhaseParameters) (dimension grade : ℕ) :
    ACore phase dimension →ₗ[ℂ] AGrade phase dimension grade :=
  (aGradeEta phase).toLinearMap.comp GradeCore.ofCoreLinear

theorem q23FieldEmbed_norm (phase : PhaseParameters) (dimension grade : ℕ)
    (field : ACore phase dimension) :
    ‖q23FieldEmbed phase dimension grade field‖ = originalGradeNorm grade field :=
  aGradeEta_norm phase (GradeCore.ofCoreLinear field)

theorem q23FieldEmbed_injective (phase : PhaseParameters) (dimension grade : ℕ) :
    Function.Injective (q23FieldEmbed phase dimension grade) := by
  intro first second equality
  exact congrArg GradeCore.toCore (aGradeEta_injective phase equality)

theorem q23FieldEmbed_denseRange (phase : PhaseParameters) (dimension grade : ℕ) :
    DenseRange (q23FieldEmbed phase dimension grade) := by
  apply (aGradeEta_denseRange phase).mono
  rintro _ ⟨field, rfl⟩
  exact ⟨field.toCore, by simp only [q23FieldEmbed, LinearMap.comp_apply,
    GradeCore.ofCore_toCore, LinearIsometry.coe_toLinearMap]⟩

abbrev Q23FieldCore (phase : PhaseParameters) (dimension grade : ℕ) :
    Submodule ℝ (AGrade phase dimension grade) :=
  ((q23FieldEmbed phase dimension grade).restrictScalars ℝ).range

def q23FieldCoreEquiv (phase : PhaseParameters) (dimension grade : ℕ) :
    ACore phase dimension ≃ₗ[ℝ] Q23FieldCore phase dimension grade :=
  LinearEquiv.ofInjective
    ((q23FieldEmbed phase dimension grade).restrictScalars ℝ)
    (q23FieldEmbed_injective phase dimension grade)

theorem q23FieldCore_dense (phase : PhaseParameters) (dimension grade : ℕ) :
    Dense (Q23FieldCore phase dimension grade : Set (AGrade phase dimension grade)) :=
  q23FieldEmbed_denseRange phase dimension grade

theorem q23FieldCoreEquiv_symm_norm (phase : PhaseParameters) (dimension grade : ℕ)
    (field : Q23FieldCore phase dimension grade) :
    originalGradeNorm grade ((q23FieldCoreEquiv phase dimension grade).symm field) =
      ‖field‖ := by
  rw [← q23FieldEmbed_norm]
  change ‖q23FieldCoreEquiv phase dimension grade
    ((q23FieldCoreEquiv phase dimension grade).symm field)‖ = ‖field‖
  rw [LinearEquiv.apply_symm_apply]

/-- The literal complex-bilinear field `(v₁,v₂) ↦ Rv₁ · Rv₂`. -/
def seedEnergyBilinearCore (phase : PhaseParameters) :
    MultilinearMap ℂ (fun _ : Fin 2 => ACore phase 3) (ACore phase 1) where
  toFun fields := pairProductLinear phase physicalDotProduct
    (rotationCore phase (fields 0)) (rotationCore phase (fields 1))
  map_update_add' := by
    intro _ fields slot first second
    fin_cases slot <;> simp only [Function.update_apply] <;>
      simp [map_add, LinearMap.add_apply]
  map_update_smul' := by
    intro _ fields slot scalar field
    fin_cases slot <;> simp only [Function.update_apply] <;>
      simp [map_smul, LinearMap.smul_apply]

@[simp] theorem seedEnergyBilinearCore_apply (phase : PhaseParameters)
    (fields : Fin 2 → ACore phase 3) :
    seedEnergyBilinearCore phase fields =
      actualMultilinearProduct phase physicalDotProduct
        ![rotationCore phase (fields 0), rotationCore phase (fields 1)] := rfl

/-- The quadratic energy map on the dense subspace of the high completed
field grade, before slot completion. -/
def seedEnergyCoreMap (phase : PhaseParameters) (grade : ℕ) :
    MultilinearMap ℝ
      (fun _ : Fin 2 => Q23FieldCore phase 3 (grade + 5))
      (AGrade phase 1 (grade + 1)) :=
  ((q23FieldEmbed phase 1 (grade + 1)).restrictScalars ℝ).compMultilinearMap
    (((seedEnergyBilinearCore phase).restrictScalars ℝ).compLinearMap
      (fun _ => (q23FieldCoreEquiv phase 3 (grade + 5)).symm.toLinearMap))

@[simp] theorem seedEnergyCoreMap_apply (phase : PhaseParameters) (grade : ℕ)
    (fields : Fin 2 → Q23FieldCore phase 3 (grade + 5)) :
    seedEnergyCoreMap phase grade fields =
      q23FieldEmbed phase 1 (grade + 1)
        (seedEnergyBilinearCore phase
          (fun position => (q23FieldCoreEquiv phase 3 (grade + 5)).symm
            (fields position))) := rfl

def seedEnergyCompletionConstant (grade : ℕ) : ℝ :=
  2 * productGradeConstant 1 (grade + 1) * ‖physicalDotProduct‖ *
    vectorDerivativeGradeConstant (grade + 4) * vectorDerivativeGradeConstant 3

theorem seedEnergyCompletionConstant_nonnegative (grade : ℕ) :
    0 ≤ seedEnergyCompletionConstant grade := by
  unfold seedEnergyCompletionConstant
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (productGradeConstant_nonnegative 1 (grade + 1)))
        (norm_nonneg physicalDotProduct))
      (vectorDerivativeGradeConstant_nonnegative (grade + 4)))
    (vectorDerivativeGradeConstant_nonnegative 3)

theorem seedEnergyCoreMap_bound (phase : PhaseParameters) (grade : ℕ)
    (fields : Fin 2 → Q23FieldCore phase 3 (grade + 5)) :
    ‖seedEnergyCoreMap phase grade fields‖ ≤
      seedEnergyCompletionConstant grade * ∏ position, ‖fields position‖ := by
  let coreFields : Fin 2 → ACore phase 3 := fun position =>
    (q23FieldCoreEquiv phase 3 (grade + 5)).symm (fields position)
  have highZero := rotationCore_bound phase (coreFields 0) (grade + 4)
  have highOne := rotationCore_bound phase (coreFields 1) (grade + 4)
  have lowZero : originalGradeNorm 3 (rotationCore phase (coreFields 0)) ≤
      vectorDerivativeGradeConstant 3 * originalGradeNorm (grade + 5) (coreFields 0) :=
    (rotationCore_bound phase (coreFields 0) 3).trans
      (mul_le_mul_of_nonneg_left
        (originalGradeNorm_mono (by omega) (coreFields 0))
        (vectorDerivativeGradeConstant_nonnegative 3))
  have lowOne : originalGradeNorm 3 (rotationCore phase (coreFields 1)) ≤
      vectorDerivativeGradeConstant 3 * originalGradeNorm (grade + 5) (coreFields 1) :=
    (rotationCore_bound phase (coreFields 1) 3).trans
      (mul_le_mul_of_nonneg_left
        (originalGradeNorm_mono (by omega) (coreFields 1))
        (vectorDerivativeGradeConstant_nonnegative 3))
  have firstTerm := mul_le_mul highZero lowOne
    (originalGradeNorm_nonnegative 3 (rotationCore phase (coreFields 1)))
    (mul_nonneg (vectorDerivativeGradeConstant_nonnegative (grade + 4))
      (originalGradeNorm_nonnegative (grade + 5) (coreFields 0)))
  have secondTerm := mul_le_mul highOne lowZero
    (originalGradeNorm_nonnegative 3 (rotationCore phase (coreFields 0)))
    (mul_nonneg (vectorDerivativeGradeConstant_nonnegative (grade + 4))
      (originalGradeNorm_nonnegative (grade + 5) (coreFields 1)))
  have oneHighBound : oneHighExpression (grade + 1)
      ![rotationCore phase (coreFields 0), rotationCore phase (coreFields 1)] ≤
      2 * vectorDerivativeGradeConstant (grade + 4) *
        vectorDerivativeGradeConstant 3 *
        (originalGradeNorm (grade + 5) (coreFields 0) *
          originalGradeNorm (grade + 5) (coreFields 1)) := by
    rw [oneHighExpression_pair]
    exact (add_le_add firstTerm secondTerm).trans_eq (by ring)
  have productBound := actualMultilinearProduct_bound phase physicalDotProduct
    ![rotationCore phase (coreFields 0), rotationCore phase (coreFields 1)] (grade + 1)
  rw [seedEnergyCoreMap_apply, q23FieldEmbed_norm,
    seedEnergyBilinearCore_apply]
  apply productBound.trans
  apply (mul_le_mul_of_nonneg_left oneHighBound
    (mul_nonneg (productGradeConstant_nonnegative 1 (grade + 1))
      (norm_nonneg physicalDotProduct))).trans_eq
  rw [Fin.prod_univ_two, ← q23FieldCoreEquiv_symm_norm phase 3 (grade + 5) (fields 0),
    ← q23FieldCoreEquiv_symm_norm phase 3 (grade + 5) (fields 1)]
  unfold seedEnergyCompletionConstant coreFields
  ring

/-- Evaluation of a smoothly parameterized complex operator on a smoothly
parameterized vector, with real parameters. -/
theorem q23ContDiffOn_complexCLM_apply
    {X E F : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F]
    {operators : X → E →L[ℂ] F} {values : X → E} {domain : Set X}
    (operatorsSmooth : ContDiffOn ℝ ∞ operators domain)
    (valuesSmooth : ContDiffOn ℝ ∞ values domain) :
    ContDiffOn ℝ ∞ (fun point => operators point (values point)) domain := by
  have realOperators : ContDiffOn ℝ ∞
      (fun point => q23RestrictScalarsCLM (operators point)) domain :=
    (q23RestrictScalarsCLM (E := E) (F := F)).contDiff.comp_contDiffOn operatorsSmooth
  exact realOperators.clm_apply valuesSmooth

/-- The completed planar seed field `M_p y`, at one original grade. -/
def completedTameSeedPlanarFieldFamily (phase : PhaseParameters) (grade : ℕ)
    (parameter : Seed.Parameters) : AGrade phase 2 grade :=
  completedSeedMatrixFamily phase grade parameter
    (aGradeEta phase (GradeCore.ofCoreLinear (tamePlanarCoordinateField phase)))

/-- The completed literal seed field `ι M_p y`, as a function of the finite
seed parameter. -/
def completedTameSeedFieldFamily (phase : PhaseParameters) (grade : ℕ)
    (parameter : Seed.Parameters) : AGrade phase 3 grade :=
  q23ValueMapCompleted (grade := grade) phase tamePlanarInclusion
    (completedTameSeedPlanarFieldFamily phase grade parameter)

theorem completedTameSeedPlanarFieldFamily_contDiffOn
    (phase : PhaseParameters) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedTameSeedPlanarFieldFamily phase grade)
      Seed.parameterDomain := by
  exact q23ContDiffOn_complexCLM_apply
    (completedSeedMatrixFamily_contDiffOn phase grade) contDiffOn_const

theorem completedTameSeedFieldFamily_contDiffOn
    (phase : PhaseParameters) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedTameSeedFieldFamily phase grade)
      Seed.parameterDomain := by
  exact ((q23ValueMapCompleted (grade := grade) phase
    tamePlanarInclusion).restrictScalars ℝ).contDiff.comp_contDiffOn
      (completedTameSeedPlanarFieldFamily_contDiffOn phase grade)

theorem completedTameSeedPlanarFieldFamily_core (phase : PhaseParameters) (grade : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain) :
    completedTameSeedPlanarFieldFamily phase grade parameter =
      aGradeEta phase (GradeCore.ofCoreLinear
        (tameSeedPlanarField phase parameter inside)) := by
  exact completedSeedMatrixFamily_core phase grade parameter inside
    (tamePlanarCoordinateField phase)

theorem completedTameSeedFieldFamily_core (phase : PhaseParameters) (grade : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain) :
    completedTameSeedFieldFamily phase grade parameter =
      aGradeEta phase (GradeCore.ofCoreLinear
        (tameSeedField phase parameter inside)) := by
  unfold completedTameSeedFieldFamily
  rw [completedTameSeedPlanarFieldFamily_core phase grade parameter inside,
    q23ValueMapCompleted_core]
  rfl

end Grad.NonlinearQuotientBounds
