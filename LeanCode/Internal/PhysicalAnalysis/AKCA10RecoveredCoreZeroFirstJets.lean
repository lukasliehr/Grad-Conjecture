import AKCA9ClosedRayFirstJetExclusion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff BigOperators
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.Cor18
open Grad.ActualNativeCellMoments Grad.ActualSmoothPhysicalField Grad.ActualPuncturedFamily Grad.ActualCartesianDescent
open Grad.SourceCollarDivision Grad.AnnularRestriction Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients

 theorem criticalDensity_eq_logSlope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (radius : ℝ) (positive : 0 < radius) (value : E) :
    ‖radius ^ (-(3 / 2 : ℝ)) • value‖ ^ 2 = radius⁻¹ * (radius⁻¹ * ‖value‖) ^ 2 := by
  have power : (radius ^ (-(3 / 2 : ℝ))) ^ 2 = radius⁻¹ * (radius⁻¹)^2 := by
    calc
      _ = radius ^ (-3 : ℝ) := by rw [← Real.rpow_two,← Real.rpow_mul positive.le]; norm_num
      _ = _ := by rw [Real.rpow_neg positive.le,Real.rpow_ofNat]; field_simp
  rw [norm_smul,Real.norm_of_nonneg (Real.rpow_nonneg positive.le _),mul_pow,power]
  ring

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow dimension (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second)=rows first)
include compatible

/-- Native critical energy and SAME physical reconstruction prove the original
constant and first Cartesian jets vanish. -/
 theorem recoveredCore_criticalEnergy_zeroFirstJets (core : ACore parameters dimension)
    (same : ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters core).value (point,(axial : CellCircle)) =
        gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (point.val,axial))
    (finite : (∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal
      (‖radius ^ (-(3 / 2 : ℝ)) • gluedWeightedFamilyCurve parameters lower positive cofinal rows curves 4 radius‖ ^ 2)) < ⊤) :
    ∀ cell : ℤ, ZeroCartesianFirstJets (core.val cell) := by
  let C := nativeFieldReadoutConstant parameters dimension
  let curve := gluedWeightedFamilyCurve parameters lower positive cofinal rows curves 4
  have Cnonnegative : 0 ≤ C := nativeFieldReadoutConstant_nonnegative parameters dimension
  have curveMeasurable : AEStronglyMeasurable curve (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (gluedWeightedFamilyCurve_continuous parameters lower positive bounded cofinal decreasing rows curves compatible 4).aestronglyMeasurable measurableSet_Ioc
  have weightedMeasurable : AEStronglyMeasurable (fun radius => radius ^ (-(3 / 2 : ℝ)) • curve radius)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (measurable_id.pow_const (-(3 / 2 : ℝ))).aestronglyMeasurable.smul curveMeasurable
  intro cell
  apply closedJet_criticalEnergy_zeroFirstJets
  intro direction
  have boundedIntegral : (∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal
      (radius⁻¹ * (radius⁻¹ * ‖closedJetRay (core.val cell) direction radius‖)^2)) ≤
      ENNReal.ofReal (C^2) * ∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal
        (‖radius ^ (-(3 / 2 : ℝ)) • curve radius‖ ^ 2) := by
    calc
      _ ≤ ∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal (C^2) * ENNReal.ofReal
          (‖radius ^ (-(3 / 2 : ℝ)) • curve radius‖ ^ 2) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius inside
        have pointNorm : ‖radius • spatialBasis direction‖ = radius := by
          rw [norm_smul,Grad.BoundaryLift.spatialBasis_norm,mul_one,Real.norm_of_nonneg inside.1.le]
        let point : ClosedDisk := ⟨radius • spatialBasis direction,by change ‖radius • spatialBasis direction‖ ≤ 1; rw [pointNorm]; exact inside.2⟩
        have rayAt : closedJetRay (core.val cell) direction radius = (core.val cell).value point :=
          smoothClosedExtension_value (core.val cell) point
        have rawBound := recoveredCoreCell_fourth_bound parameters lower positive bounded cofinal decreasing rows curves compatible core same point
          (by change 0 < ‖radius • spatialBasis direction‖; rw [pointNorm]; exact inside.1) cell
        change ‖(core.val cell).value point‖ ≤ C * ‖curve ‖radius • spatialBasis direction‖‖ at rawBound
        rw [pointNorm,← rayAt] at rawBound
        rw [← criticalDensity_eq_logSlope radius inside.1,← ENNReal.ofReal_mul (sq_nonneg C),← mul_pow]
        apply ENNReal.ofReal_le_ofReal
        apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg Cnonnegative (norm_nonneg _))).mpr
        rw [norm_smul,norm_smul]
        exact (mul_le_mul_of_nonneg_left rawBound (norm_nonneg _)).trans_eq (by ring)
      _ = _ := lintegral_const_mul'' _ (weightedMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal
  exact boundedIntegral.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top finite)

end Grad.OriginalCoreRealization
