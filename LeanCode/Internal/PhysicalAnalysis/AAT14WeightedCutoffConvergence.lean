import AAT13CompleteGradeModels

noncomputable section
set_option maxHeartbeats 1000000

open Set Filter
open scoped Topology

namespace Grad.AnnularGrades

open Grad.AnnularVariational Grad.ActualBandCompletion

section Cutoff
variable (lower length : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ)

theorem annularEnergyDecode_cut (keep : Set HighAnnularMode) (field : annularEnergySpace lower length positive) :
    annularEnergyDecode lower length positive angular cell inserted (annularEnergyCut lower length positive keep field) =
      annularEnergyCut lower length positive keep (annularEnergyDecode lower length positive angular cell inserted field) := by
  classical
  apply Subtype.ext
  apply lp.ext
  funext mode
  rw [annularEnergyDecode_apply, annularEnergyCut_val, lpCut_apply,
    annularEnergyCut_val, lpCut_apply, annularEnergyDecode_apply]
  split_ifs <;> simp

theorem annularEnergyCut_hasGrade (keep : Set HighAnnularMode) (field : annularEnergySpace lower length positive)
    (grade : HasAnnularEnergyGrade lower length positive angular cell inserted field) :
    HasAnnularEnergyGrade lower length positive angular cell inserted (annularEnergyCut lower length positive keep field) := by
  have identity := (annularEnergyDecode_cut lower length positive angular cell inserted keep
    (annularWeightedEnergy lower length positive angular cell inserted field grade)).trans
      (congrArg (annularEnergyCut lower length positive keep)
        (annularEnergyDecode_weighted lower length positive angular cell inserted field grade))
  exact (congrArg (HasAnnularEnergyGrade lower length positive angular cell inserted) identity).mp
    (annularEnergyDecode_hasGrade lower length positive angular cell inserted _)

theorem annularWeightedEnergy_cut (keep : Set HighAnnularMode) (field : annularEnergySpace lower length positive)
    (grade : HasAnnularEnergyGrade lower length positive angular cell inserted field)
    (cutGrade : HasAnnularEnergyGrade lower length positive angular cell inserted (annularEnergyCut lower length positive keep field)) :
    annularWeightedEnergy lower length positive angular cell inserted (annularEnergyCut lower length positive keep field) cutGrade =
      annularEnergyCut lower length positive keep (annularWeightedEnergy lower length positive angular cell inserted field grade) := by
  apply annularEnergyDecode_injective lower length positive angular cell inserted
  exact (annularEnergyDecode_weighted lower length positive angular cell inserted _ cutGrade).trans
    ((annularEnergyDecode_cut lower length positive angular cell inserted keep _).trans
      (congrArg (annularEnergyCut lower length positive keep)
        (annularEnergyDecode_weighted lower length positive angular cell inserted field grade))).symm

/-- Finite Fourier cuts converge in the exact weighted energy norm. -/
theorem annularWeightedEnergy_cut_tendsto (field : annularEnergySpace lower length positive)
    (grade : HasAnnularEnergyGrade lower length positive angular cell inserted field) :
    Tendsto (fun support : Finset HighAnnularMode =>
      annularWeightedEnergy lower length positive angular cell inserted
        (annularEnergyCut lower length positive (support : Set HighAnnularMode) field)
        (annularEnergyCut_hasGrade lower length positive angular cell inserted (support : Set HighAnnularMode) field grade))
      atTop (𝓝 (annularWeightedEnergy lower length positive angular cell inserted field grade)) := by
  have equality (support : Finset HighAnnularMode) :=
    annularWeightedEnergy_cut lower length positive angular cell inserted (support : Set HighAnnularMode) field grade
      (annularEnergyCut_hasGrade lower length positive angular cell inserted (support : Set HighAnnularMode) field grade)
  exact (annularEnergyCut_tendsto lower length positive
    (annularWeightedEnergy lower length positive angular cell inserted field grade)).congr'
      (Filter.Eventually.of_forall (fun support => (equality support).symm))

end Cutoff

section Trace
variable (lower length : ℝ) (positive : 0 < lower) (collar : lower < 1) (lengthPositive : 0 < length)
    (angular cell inserted : ℕ) (endpoint : Fin 2)

theorem annularEnergyTrace_weighted_decode (field : annularEnergySpace lower length positive)
    (grade : HasAnnularEnergyGrade lower length positive angular cell inserted field) :
    annularLpDecode angular cell inserted
      (annularEnergyTrace lower length positive collar lengthPositive endpoint
        (annularWeightedEnergy lower length positive angular cell inserted field grade)) =
      annularEnergyTrace lower length positive collar lengthPositive endpoint field :=
  (annularEnergyTrace_diagonal lower length positive collar lengthPositive
    (fun mode => (annularGradeWeight angular cell inserted mode)⁻¹) 1 (by norm_num)
    (annularGradeWeight_inv_bound angular cell inserted) endpoint _).symm.trans
      (congrArg (annularEnergyTrace lower length positive collar lengthPositive endpoint)
        (annularEnergyDecode_weighted lower length positive angular cell inserted field grade))

theorem annularEnergyTrace_weighted_norm_sq (field : annularEnergySpace lower length positive)
    (grade : HasAnnularEnergyGrade lower length positive angular cell inserted field) :
    ‖annularEnergyTrace lower length positive collar lengthPositive endpoint
      (annularWeightedEnergy lower length positive angular cell inserted field grade)‖ ^ 2 =
      ∑' mode : HighAnnularMode, annularGradeWeight angular cell inserted mode ^ 2 *
        ‖annularEnergyTrace lower length positive collar lengthPositive endpoint field mode‖ ^ 2 := by
  rw [annularLpDecode_norm_sq angular cell inserted, annularEnergyTrace_weighted_decode]

/-- Both sharp trace norms converge at every inserted/split grade. -/
theorem annularWeightedTrace_cut_tendsto (field : annularEnergySpace lower length positive)
    (grade : HasAnnularEnergyGrade lower length positive angular cell inserted field) :
    Tendsto (fun support : Finset HighAnnularMode =>
      annularEnergyTrace lower length positive collar lengthPositive endpoint
        (annularWeightedEnergy lower length positive angular cell inserted
          (annularEnergyCut lower length positive (support : Set HighAnnularMode) field)
          (annularEnergyCut_hasGrade lower length positive angular cell inserted (support : Set HighAnnularMode) field grade)))
      atTop (𝓝 (annularEnergyTrace lower length positive collar lengthPositive endpoint
        (annularWeightedEnergy lower length positive angular cell inserted field grade))) :=
  (annularEnergyTrace lower length positive collar lengthPositive endpoint).continuous.tendsto _ |>.comp
    (annularWeightedEnergy_cut_tendsto lower length positive angular cell inserted field grade)

end Trace

end Grad.AnnularGrades
