import Q23SeedChartFamilies
import QuotientDerivativeCompletion

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 2400000

open Set
open scoped BigOperators ContDiff Topology

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Gauges Grad.Constraints.Seed Grad.NonlinearProduct

theorem seedEnergyCompletion_exists (phase : PhaseParameters) (grade : ℕ) :
    ∃ completed : ContinuousMultilinearMap ℝ
        (fun _ : Fin 2 => AGrade phase 3 (grade + 5))
        (AGrade phase 1 (grade + 1)),
      ∀ fields : Fin 2 → ACore phase 3,
        completed (fun position =>
          q23FieldEmbed phase 3 (grade + 5) (fields position)) =
        q23FieldEmbed phase 1 (grade + 1) (seedEnergyBilinearCore phase fields) := by
  obtain ⟨completed, agreement⟩ := q23MultilinearCompletion_exists
    (Q23FieldCore phase 3 (grade + 5))
    (q23FieldCore_dense phase 3 (grade + 5)) 2
    (seedEnergyCoreMap phase grade) (seedEnergyCompletionConstant grade)
    (seedEnergyCompletionConstant_nonnegative grade)
    (seedEnergyCoreMap_bound phase grade)
  refine ⟨completed, fun fields => ?_⟩
  let arguments : Fin 2 → Q23FieldCore phase 3 (grade + 5) := fun position =>
    q23FieldCoreEquiv phase 3 (grade + 5) (fields position)
  have equality := agreement arguments
  have argumentEquality : (fun position =>
      (arguments position : AGrade phase 3 (grade + 5))) =
      fun position => q23FieldEmbed phase 3 (grade + 5) (fields position) := by
    funext position
    rfl
  rw [argumentEquality] at equality
  simpa only [arguments, seedEnergyCoreMap_apply, LinearEquiv.symm_apply_apply] using equality

/-- Completed literal bilinear energy term, with five source grades retained
until the final one-grade rotation. -/
def completedSeedEnergyBilinear (phase : PhaseParameters) (grade : ℕ) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin 2 => AGrade phase 3 (grade + 5))
      (AGrade phase 1 (grade + 1)) :=
  Classical.choose (seedEnergyCompletion_exists phase grade)

theorem completedSeedEnergyBilinear_core (phase : PhaseParameters) (grade : ℕ)
    (fields : Fin 2 → ACore phase 3) :
    completedSeedEnergyBilinear phase grade (fun position =>
        q23FieldEmbed phase 3 (grade + 5) (fields position)) =
      q23FieldEmbed phase 1 (grade + 1) (seedEnergyBilinearCore phase fields) :=
  Classical.choose_spec (seedEnergyCompletion_exists phase grade) fields

/-- The literal planar rotation extended from grade `q+1` to grade `q`. -/
def q23RotationCompletedLossOne (phase : PhaseParameters) (grade : ℕ) :
    AGrade phase 1 (grade + 1) →L[ℂ] AGrade phase 1 grade :=
  (coordinateCompleted phase grade 0).comp (partialCompleted phase 1) -
    (coordinateCompleted phase grade 1).comp (partialCompleted phase 0)

theorem q23RotationCompletedLossOne_core (phase : PhaseParameters)
    (grade : ℕ) (field : ACore phase 1) :
    q23RotationCompletedLossOne phase grade
        (q23FieldEmbed phase 1 (grade + 1) field) =
      q23FieldEmbed phase 1 grade (rotationCore phase field) := by
  unfold q23RotationCompletedLossOne q23FieldEmbed
  change coordinateCompleted phase grade 0
      (partialCompleted phase 1 (aGradeEta phase (GradeCore.ofCoreLinear field))) -
    coordinateCompleted phase grade 1
      (partialCompleted phase 0 (aGradeEta phase (GradeCore.ofCoreLinear field))) = _
  rw [partialCompleted_eta, coordinateCompleted_core,
    partialCompleted_eta, coordinateCompleted_core, ← map_sub]
  rfl

/-- The completed energy `|R(ιM_p y)|²-r²`, in the grade needed before the
final rotation in the literal Q17 scalar. -/
def completedTameSeedEnergyFamily (phase : PhaseParameters) (grade : ℕ)
    (parameter : Seed.Parameters) : AGrade phase 1 (grade + 1) :=
  completedSeedEnergyBilinear phase grade
      (fun _ => completedTameSeedFieldFamily phase (grade + 5) parameter) -
    q23FieldEmbed phase 1 (grade + 1) (tameRadiusSquareField phase)

theorem completedTameSeedEnergyFamily_contDiffOn
    (phase : PhaseParameters) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedTameSeedEnergyFamily phase grade)
      Seed.parameterDomain := by
  have diagonal : ContDiffOn ℝ ∞
      (fun parameter : Seed.Parameters => fun _ : Fin 2 =>
        completedTameSeedFieldFamily phase (grade + 5) parameter)
      Seed.parameterDomain :=
    contDiffOn_pi.2 (fun _ => completedTameSeedFieldFamily_contDiffOn phase (grade + 5))
  exact ((completedSeedEnergyBilinear phase grade).contDiff.comp_contDiffOn diagonal).sub
    contDiffOn_const

theorem completedTameSeedEnergyFamily_core (phase : PhaseParameters) (grade : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain) :
    completedTameSeedEnergyFamily phase grade parameter =
      q23FieldEmbed phase 1 (grade + 1) (tameSeedEnergy phase parameter inside) := by
  unfold completedTameSeedEnergyFamily tameSeedEnergy
  rw [completedTameSeedFieldFamily_core phase (grade + 5) parameter inside]
  change completedSeedEnergyBilinear phase grade
      (fun _ => q23FieldEmbed phase 3 (grade + 5)
        (tameSeedField phase parameter inside)) -
      q23FieldEmbed phase 1 (grade + 1) (tameRadiusSquareField phase) = _
  rw [completedSeedEnergyBilinear_core, ← map_sub]
  rfl

def q23ComplexScalarCLM {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (scalar : ℂ) : E →L[ℝ] E :=
  (scalar • ContinuousLinearMap.id ℂ E).restrictScalars ℝ

/-- The completed literal Q17 scalar `-(1/4) R(|R(ιM_p y)|²-r²)`. -/
def completedTameSeedScalarFamily (phase : PhaseParameters) (grade : ℕ)
    (parameter : Seed.Parameters) : AGrade phase 1 grade :=
  q23ComplexScalarCLM (-(4 : ℂ)⁻¹)
    (q23RotationCompletedLossOne phase grade
      (completedTameSeedEnergyFamily phase grade parameter))

theorem completedTameSeedScalarFamily_contDiffOn
    (phase : PhaseParameters) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedTameSeedScalarFamily phase grade)
      Seed.parameterDomain := by
  exact (q23ComplexScalarCLM (E := AGrade phase 1 grade) (-(4 : ℂ)⁻¹)).contDiff.comp_contDiffOn
    (((q23RotationCompletedLossOne phase grade).restrictScalars ℝ).contDiff.comp_contDiffOn
      (completedTameSeedEnergyFamily_contDiffOn phase grade))

theorem completedTameSeedScalarFamily_core (phase : PhaseParameters) (grade : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain) :
    completedTameSeedScalarFamily phase grade parameter =
      q23FieldEmbed phase 1 grade (tameSeedScalar phase parameter inside) := by
  unfold completedTameSeedScalarFamily tameSeedScalar
  rw [completedTameSeedEnergyFamily_core phase grade parameter inside,
    q23RotationCompletedLossOne_core]
  change (-(4 : ℂ)⁻¹) • q23FieldEmbed phase 1 grade
      (rotationCore phase (tameSeedEnergy phase parameter inside)) = _
  rw [map_smul]

end Grad.NonlinearQuotientBounds
