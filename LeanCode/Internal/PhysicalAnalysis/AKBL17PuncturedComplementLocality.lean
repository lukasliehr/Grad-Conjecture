import AKBL16RoughClosedComplementRepresentative
import GC18RangeInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.CompactCutoff
open Grad.Constraints Grad.Constraints.Gauges Grad.PhysicalFamily Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.ActualCartesianWeakEquations

 theorem startupTangential_norm_locality (first second : ClosedDisk → PhysicalValue 2) (point : ClosedDisk)
    (same : ∀ other : ClosedDisk, ‖other.val‖ = ‖point.val‖ → first other = second other) :
    closedTangentialValue first point = closedTangentialValue second point := by
  have reflected : ∀ other : ClosedDisk,
      ‖other.val‖ = ‖(orthogonalClosedPoint cartesianReflectionEquiv point).val‖ → first other = second other := by
    intro other normSame
    exact same other (normSame.trans (LinearIsometryEquiv.norm_map cartesianReflectionEquiv point.val))
  unfold closedTangentialValue
  rw [closedEquivariantValue_norm_locality first second point same,
    closedEquivariantValue_norm_locality first second (orthogonalClosedPoint cartesianReflectionEquiv point) reflected]

 theorem startupComplement_norm_locality (first second : ClosedDisk → PhysicalValue 3) (point : ClosedDisk)
    (same : ∀ other : ClosedDisk, ‖other.val‖ = ‖point.val‖ → first other = second other) :
    cartesianComplementValue first point = cartesianComplementValue second point := by
  unfold cartesianComplementValue
  rw [startupTangential_norm_locality _ _ point (fun other sameNorm => congrArg planarPartMap (same other sameNorm)),
    closedCharacterProjection_norm_locality 0 _ _ point (fun other sameNorm => congrArg toroidalPartMap (same other sameNorm))]

/-- Existing compact localization, generalized only in the value dimension,
retains every value on the selected circle of a punctured continuous field. -/
 theorem startupCircle_continuousLocalization {dimension : ℕ} (raw : Spatial → PhysicalValue dimension)
    (continuousRaw : ContinuousOn raw (openUnitDisk \ {(0 : Spatial)}))
    (point : Spatial) (positive : 0 < ‖point‖) (inside : ‖point‖ < 1) :
    ∃ localized : C(ClosedDisk,PhysicalValue dimension),
      ∀ other : ClosedDisk, ‖other.val‖ = ‖point‖ → localized other = raw other.val := by
  let circle := Metric.sphere (0 : Spatial) ‖point‖
  have included : circle ⊆ openUnitDisk \ {(0 : Spatial)} := by
    intro other membership
    have sameNorm : ‖other‖ = ‖point‖ := by simpa only [circle,Metric.mem_sphere,dist_zero_right] using membership
    refine ⟨sameNorm.trans_lt inside,?_⟩
    intro zeroPoint
    have otherZero : other = 0 := Set.mem_singleton_iff.mp zeroPoint
    rw [otherZero,norm_zero] at sameNorm
    exact (ne_of_gt positive) sameNorm.symm
  let cutoff := compactCutoff circle (openUnitDisk \ {(0 : Spatial)}) (isCompact_sphere 0 ‖point‖)
    (openUnitDisk_isOpen.sdiff isClosed_singleton) included
  have continuousLocal := continuous_smul_of_tsupport_subset _ (openUnitDisk_isOpen.sdiff isClosed_singleton)
    cutoff.toFun cutoff.smooth.continuous cutoff.supported raw continuousRaw
  refine ⟨⟨fun other => cutoff.toFun other.val • raw other.val,continuousLocal.comp continuous_subtype_val⟩,?_⟩
  intro other sameNorm
  change cutoff.toFun other.val • raw other.val = raw other.val
  rw [cutoff.one_on (by simpa only [circle,Metric.mem_sphere,dist_zero_right] using sameNorm),one_smul]

/-- The fixed complement is idempotent on every actual punctured circle.
No continuity at the origin is imposed on the input. -/
 theorem startupComplement_punctured_idempotent (raw : Spatial → PhysicalValue 3)
    (continuousRaw : ContinuousOn raw (openUnitDisk \ {(0 : Spatial)}))
    (point : ClosedDisk) (positive : 0 < ‖point.val‖) (inside : ‖point.val‖ < 1) :
    cartesianComplementValue (cartesianComplementValue (fun other : ClosedDisk => raw other.val)) point =
      cartesianComplementValue (fun other : ClosedDisk => raw other.val) point := by
  obtain ⟨localized,same⟩ := startupCircle_continuousLocalization raw continuousRaw point.val positive inside
  have complementSame (other : ClosedDisk) (normSame : ‖other.val‖ = ‖point.val‖) :
      cartesianComplementValue (fun query : ClosedDisk => raw query.val) other = cartesianComplementValue localized other :=
    startupComplement_norm_locality _ _ other (fun query sameQuery => (same query (sameQuery.trans normSame)).symm)
  rw [startupComplement_norm_locality _ _ point complementSame,
    cartesianComplementValue_idempotent localized localized.continuous,complementSame point rfl]

end Grad.CartesianStartup
