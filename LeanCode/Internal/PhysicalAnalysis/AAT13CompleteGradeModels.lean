import AAT12CompatibleGradeInclusions

noncomputable section
set_option maxHeartbeats 1000000

open MeasureTheory
open scoped Topology Interval

namespace Grad.AnnularGrades

open Grad.AnnularVariational Grad.ClosedJets

/-- Complete normalized model of the literal weighted energy carrier.
Its physical inclusion and exact range are AAT9; its norm is the literal
weighted square sum by AAT10. -/
abbrev AnnularEnergyGrade (lower length : ℝ) (positive : 0 < lower) (_angular _cell _inserted : ℕ) :=
  annularEnergySpace lower length positive

abbrev AnnularDataGrade (lower : ℝ) (_angular _cell _inserted : ℕ) :=
  AnnularForcing lower × AnnularBoundary

theorem annularEnergyGrade_complete (lower length : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ) :
    CompleteSpace (AnnularEnergyGrade lower length positive angular cell inserted) := inferInstance

theorem annularDataGrade_complete (lower : ℝ) (angular cell inserted : ℕ) :
    CompleteSpace (AnnularDataGrade lower angular cell inserted) := inferInstance

/-- Exactly the finite smooth core normalized by the prescribed weight. -/
def annularGradedEnergyCore (lower length : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ) :
    (HighAnnularMode →₀ complexSmoothRadialCore 1) →ₗ[ℂ]
      AnnularEnergyGrade lower length positive angular cell inserted :=
  (annularEnergyCoreInto lower length positive).comp (finiteRealDiagonal (annularGradeWeight angular cell inserted))

theorem annularGradedEnergyCore_decode (lower length : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    annularEnergyDecode lower length positive angular cell inserted
      (annularGradedEnergyCore lower length positive angular cell inserted core) =
        annularEnergyCoreInto lower length positive core := by
  change annularEnergyDiagonal lower length positive (fun mode => (annularGradeWeight angular cell inserted mode)⁻¹)
    1 (by norm_num) (annularGradeWeight_inv_bound angular cell inserted)
    (annularEnergyCoreInto lower length positive (finiteRealDiagonal (annularGradeWeight angular cell inserted) core)) = _
  rw [annularEnergyDiagonal_core]
  congr 1
  apply Finsupp.ext
  intro mode
  rw [finiteRealDiagonal_apply, finiteRealDiagonal_apply, smul_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (annularGradeWeight_pos angular cell inserted mode).ne', Complex.ofReal_one, one_smul]

theorem annularGradedEnergyCore_denseRange (lower length : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ) :
    DenseRange (annularGradedEnergyCore lower length positive angular cell inserted) := by
  apply (annularEnergyCoreInto_denseRange lower length positive).mono
  rintro _ ⟨core, rfl⟩
  refine ⟨finiteRealDiagonal (fun mode => (annularGradeWeight angular cell inserted mode)⁻¹) core, ?_⟩
  unfold annularGradedEnergyCore
  rw [LinearMap.comp_apply]
  congr 1
  apply Finsupp.ext
  intro mode
  rw [finiteRealDiagonal_apply, finiteRealDiagonal_apply, smul_smul, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (annularGradeWeight_pos angular cell inserted mode).ne', Complex.ofReal_one, one_smul]

/-- Literal weighted r dr energy of the dense finite smooth physical core. -/
theorem annularGradedEnergyCore_norm_sq (lower length : ℝ) (positive : 0 < lower) (collar : lower ≤ 1)
    (angular cell inserted : ℕ) (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    ‖annularGradedEnergyCore lower length positive angular cell inserted core‖ ^ 2 =
      ∑' mode : HighAnnularMode, annularGradeWeight angular cell inserted mode ^ 2 *
        ((∫ radius in lower..1, radius * (‖(core mode).val.2 radius‖ ^ 2 +
          annularPotential length radius mode.val.1 mode.val.2 * ‖(core mode).val.1 radius‖ ^ 2)) +
          2 * ‖(core mode).val.1 1‖ ^ 2) := by
  rw [annularEnergyDecode_norm_sq lower length positive angular cell inserted,
    annularGradedEnergyCore_decode]
  apply tsum_congr
  intro mode
  change annularGradeWeight angular cell inserted mode ^ 2 * ‖finiteAnnularEnergyCore lower length positive core mode‖ ^ 2 = _
  rw [finiteAnnularEnergyCore_apply, annularModeEnergyCore_norm_sq lower length positive collar]

end Grad.AnnularGrades
