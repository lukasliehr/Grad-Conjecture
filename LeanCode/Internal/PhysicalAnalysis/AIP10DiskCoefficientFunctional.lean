import AIP9PeriodizationCutoff

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace Grad.InteriorPeriodization
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.DiskExtension.Operator Grad.FourierGrade Grad.COR12Extension
open Grad.InteriorLocalization

def diskCharacterTest (firstMode secondMode : ℤ) : C(ClosedDisk, ComplexEuclidean 1) :=
  ⟨fun point => starRingEnd ℂ (negativeDiskCharacter firstMode secondMode point.val) •
    EuclideanSpace.single 0 1,
    (Complex.continuous_conj.comp ((negativeDiskCharacter_continuous firstMode secondMode).comp
      continuous_subtype_val)).smul continuous_const⟩

/-- The actual ordinary-disk Fourier coefficient, including the normalization
of the period-four probability torus. -/
def actualDiskCoefficient (firstMode secondMode : ℤ) : DiskL2 1 →L[ℂ] ℂ :=
  (1 / 16 : ℂ) • innerSL ℂ (closedContinuousToDiskL2 (diskCharacterTest firstMode secondMode))

theorem actualDiskCoefficient_integral (firstMode secondMode : ℤ) (field : DiskL2 1) :
    actualDiskCoefficient firstMode secondMode field =
      (1 / 16 : ℂ) * ∫ point in openUnitDisk,
        negativeDiskCharacter firstMode secondMode point * field point 0 := by
  change (1 / 16 : ℂ) * inner ℂ
    (closedContinuousToDiskL2 (diskCharacterTest firstMode secondMode)) field = _
  rw [L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [closedContinuousToDiskL2_ae (diskCharacterTest firstMode secondMode),
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point literal inside
  rw [literal, closedDiskLift, dif_pos (openDiskMembershipClosed point inside)]
  change inner ℂ (starRingEnd ℂ (negativeDiskCharacter firstMode secondMode point) •
    EuclideanSpace.single 0 1) (field point) = _
  rw [inner_smul_left]
  simp only [starRingEnd_apply, star_star, EuclideanSpace.inner_single_left, map_one, one_mul]

theorem actualDiskCoefficient_core (firstMode secondMode : ℤ) (field : ClosedJet 1) :
    actualDiskCoefficient firstMode secondMode (closedL2Core field) =
      (1 / 16 : ℂ) * ∫ point in openUnitDisk,
        negativeDiskCharacter firstMode secondMode point * (closedDiskLift field.value point) 0 := by
  rw [actualDiskCoefficient_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards [closedContinuousToDiskL2_ae field.value] with point literal
  change _ * closedContinuousToDiskL2 field.value point 0 = _
  rw [literal]

theorem spatialCoreCoefficient_coordinate (field : ClosedJet 1)
    (supported : ∀ point : ClosedDisk, (3 / 4 : ℝ) < ‖point.val‖ → field.value point = 0)
    (firstMode secondMode : ℤ) :
    (spatialCoreCoefficient field firstMode secondMode) 0 =
      actualDiskCoefficient firstMode secondMode (closedL2Core field) := by
  let integrand := fun point => negativeDiskCharacter firstMode secondMode point • smoothClosedExtension field point
  have continuousIntegrand : Continuous integrand :=
    (negativeDiskCharacter_continuous firstMode secondMode).smul (smoothClosedExtension_smooth field).continuous
  have integrable : IntegrableOn integrand openUnitDisk :=
    (continuousIntegrand.continuousOn.integrableOn_compact diskCompact).mono_set
      (fun _ member => openDiskMembershipClosed _ member)
  have mapped := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).integral_comp_comm integrable
  rw [spatialCoreCoefficient_disk field supported, actualDiskCoefficient_core]
  have literal (point : SpatialPlane) : integrand point =
      negativeDiskCharacter firstMode secondMode point • closedDiskLift field.value point := by
    change _ • smoothClosedExtension field point = _
    rw [compact_smoothClosedExtension_literal field supported]
  simp_rw [literal] at mapped
  change ((1 / 16 : ℝ) • (∫ point in openUnitDisk,
      negativeDiskCharacter firstMode secondMode point • closedDiskLift field.value point)) 0 = _
  rw [PiLp.smul_apply]
  change (1 / 16 : ℝ) • ((∫ point in openUnitDisk,
      negativeDiskCharacter firstMode secondMode point • closedDiskLift field.value point) 0) = _
  simp only [PiLp.proj_apply, PiLp.smul_apply, smul_eq_mul] at mapped
  rw [← mapped]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  norm_num

end Grad.InteriorPeriodization
