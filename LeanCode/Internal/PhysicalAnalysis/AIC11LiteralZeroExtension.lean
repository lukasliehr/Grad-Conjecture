import AIC10DiskCutoffLaplacian

noncomputable section
open MeasureTheory Classical
open scoped ContDiff

namespace Grad.InteriorLocalization
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.CircularHighWeak
open Grad.WeightedJets Grad.WeightedJets.ZeroExtension

/-- Literal zero extension of the original disk field in auxiliary cell zero. -/
def diskZeroExtension : DiskL2 1 →L[ℂ] FieldL2 1 Set.univ :=
  (fieldExtension (CellValues 1) openUnitDisk openUnitDisk_isOpen.measurableSet).toContinuousLinearMap.comp
    (apDiskInjection 1)

theorem diskZeroExtension_bound (field : DiskL2 1) :
    ‖diskZeroExtension field‖ ≤ ‖apDiskInjection 1‖ * ‖field‖ := by
  change ‖fieldExtension (CellValues 1) openUnitDisk openUnitDisk_isOpen.measurableSet
    (apDiskInjection 1 field)‖ ≤ _
  rw [fieldExtension_norm]
  exact (apDiskInjection 1).le_opNorm field

theorem diskZeroExtension_integral (field : DiskL2 1) (cell : ℤ) (vector : PhysicalValue 1)
    (test : Spatial → ℝ) :
    (∫ point in (Set.univ : Set Spatial), test point • inner ℂ vector (diskZeroExtension field point cell)) =
      if cell = 0 then diskIntegral field vector test else 0 := by
  change (∫ point in (Set.univ : Set Spatial), test point • inner ℂ vector
    (fieldExtension (CellValues 1) openUnitDisk openUnitDisk_isOpen.measurableSet
      (apDiskInjection 1 field) point cell)) = _
  rw [integral_extension]
  by_cases zero : cell = 0
  · rw [if_pos zero]
    apply integral_congr_ae
    filter_upwards [apDiskInjection_ae field] with point injection
    rw [injection, cellSingle_apply, if_pos zero]
  · rw [if_neg zero]
    calc
      _ = ∫ point in openUnitDisk, (0 : ℂ) := by
        apply integral_congr_ae
        filter_upwards [apDiskInjection_ae field] with point injection
        rw [injection, cellSingle_apply, if_neg zero, inner_zero_right, smul_zero]
      _ = 0 := integral_zero _ _

theorem cutoffDiskScalar_injection (field : DiskL2 1) :
    apDiskInjection 1 (diskScalar interiorCutoff.toFun interiorCutoff.smooth field) =
      SpatialMultiplier.fieldMultiplier 1 openUnitDisk openUnitDisk_isOpen
        (SpatialMultiplier.derivativeScalar
          (SpatialMultiplier.compactSymbol 1 openUnitDisk interiorCutoff.toFun
            interiorCutoff.smooth interiorCutoff.compact) (zeroIndex 1)) (apDiskInjection 1 field) := by
  apply Lp.ext
  filter_upwards [apDiskInjection_ae (diskScalar interiorCutoff.toFun interiorCutoff.smooth field),
    diskScalar_ae interiorCutoff.toFun interiorCutoff.smooth field,
    apDiskInjection_ae field,
    SpatialMultiplier.fieldMultiplier_ae 1 openUnitDisk openUnitDisk_isOpen
      (SpatialMultiplier.derivativeScalar
        (SpatialMultiplier.compactSymbol 1 openUnitDisk interiorCutoff.toFun
          interiorCutoff.smooth interiorCutoff.compact) (zeroIndex 1)) (apDiskInjection 1 field)]
      with point multipliedInjection multiplication injection multiplied
  apply lp.ext
  funext cell
  rw [multipliedInjection, multiplied cell, injection, multiplication, cellSingle_apply, cellSingle_apply]
  by_cases zero : cell = 0
  · simp only [if_pos zero]
    exact RCLike.real_smul_eq_coe_smul (K := ℂ) (interiorCutoff.toFun point) (field point)
  · simp only [if_neg zero, smul_zero]

theorem localizedWeakInverse_base_zeroExtension (parameter : ℝ) (source : highDiskL2) :
    base 1 1 Set.univ (fun _ => 0) (localizedWeakInverse parameter source) =
      diskZeroExtension (diskScalar interiorCutoff.toFun interiorCutoff.smooth
        (highDiskBulk (highRobinWeakInverse parameter source))) :=
  (localizedWeakInverse_base parameter source).trans
    (congrArg (fun localField : FieldL2 1 openUnitDisk =>
      fieldExtension (CellValues 1) openUnitDisk openUnitDisk_isOpen.measurableSet localField)
      (cutoffDiskScalar_injection (highDiskBulk (highRobinWeakInverse parameter source))).symm)

end Grad.InteriorLocalization
