import GC18CartesianPolar
import GC18CoreRealization

noncomputable section

set_option maxHeartbeats 1400000

open Set MeasureTheory
open scoped Topology BigOperators Interval

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Radial

theorem closedCharacterProjection_continuous {dimension : ℕ} (mode : ℤ)
    (field : ClosedDisk → ComplexEuclidean dimension) (continuous : Continuous field) :
    Continuous (closedCharacterProjection mode field) := by
  have joint : Continuous (fun pair : ClosedDisk × ℝ => angularCharacter mode pair.2 •
      field (Grad.GaugeCoefficients.Radial.rotatedPoint pair.2 pair.1)) :=
    ((angularCharacter_smooth mode).continuous.comp continuous_snd).smul
      (continuous.comp (Grad.GaugeCoefficients.Radial.continuous_rotatedPoint_joint.comp
        (continuous_snd.prodMk continuous_fst)))
  have integrated : Continuous (fun point : ClosedDisk => ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
      angularCharacter mode angle • field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)) :=
    continuous_parametric_integral_of_continuous joint isCompact_Icc
  have normalized := integrated.const_smul ((2 * Real.pi)⁻¹ : ℝ)
  change Continuous (fun point : ClosedDisk => (2 * Real.pi)⁻¹ • ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
      angularCharacter mode angle • field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)) at normalized
  have identity : closedCharacterProjection mode field =
      fun point : ClosedDisk => (2 * Real.pi)⁻¹ • ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
        angularCharacter mode angle • field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point) := by
    funext point
    rw [closedCharacterProjection_integral, intervalIntegral.integral_of_le (by positivity), integral_Icc_eq_integral_Ioc]
  rw [identity]
  exact normalized

theorem closedEquivariantValue_continuous (field : ClosedDisk → ComplexEuclidean 2) (continuous : Continuous field) :
    Continuous (closedEquivariantValue field) :=
  (positiveHelicity.continuous.comp (closedCharacterProjection_continuous 1 field continuous)).add
    (negativeHelicity.continuous.comp (closedCharacterProjection_continuous (-1) field continuous))

theorem closedTangentialValue_continuous (field : ClosedDisk → ComplexEuclidean 2) (continuous : Continuous field) :
    Continuous (closedTangentialValue field) := by
  have average := closedEquivariantValue_continuous field continuous
  have result := (average.sub (reflectionValueMap.continuous.comp
    (average.comp (continuous_orthogonalClosedPoint cartesianReflectionEquiv)))).const_smul (1 / 2 : ℂ)
  exact result

theorem cartesianComplementValue_continuous (field : ClosedDisk → ComplexEuclidean 3) (continuous : Continuous field) :
    Continuous (cartesianComplementValue field) :=
  (planarInclusionMap.continuous.comp
    (closedTangentialValue_continuous _ (planarPartMap.continuous.comp continuous))).add
    (toroidalInclusionMap.continuous.comp
      (closedCharacterProjection_continuous 0 _ (toroidalPartMap.continuous.comp continuous)))

theorem cartesianComplementValue_idempotent (field : ClosedDisk → ComplexEuclidean 3)
    (continuous : Continuous field) (point : ClosedDisk) :
    cartesianComplementValue (cartesianComplementValue field) point = cartesianComplementValue field point := by
  have polar : cartesianComplementValue field = fixedComplementValue field :=
    funext (cartesianComplementValue_eq_polar field continuous)
  rw [cartesianComplementValue_eq_polar _ (cartesianComplementValue_continuous field continuous),
    polar, fixedComplementValue_idempotent]

/-- A continuous physical-value realization of the actual Cartesian C0.
Its range below is not relabelled as the original AP2 weighted completion. -/
def cartesianComplementMap (field : C(ClosedDisk, ComplexEuclidean 3)) : C(ClosedDisk, ComplexEuclidean 3) :=
  ⟨cartesianComplementValue field, cartesianComplementValue_continuous field field.continuous⟩

def cartesianPhysicalRange : Set C(ClosedDisk, ComplexEuclidean 3) := Set.range cartesianComplementMap

theorem cartesianComplementMap_idempotent (field : C(ClosedDisk, ComplexEuclidean 3)) :
    cartesianComplementMap (cartesianComplementMap field) = cartesianComplementMap field := by
  apply ContinuousMap.ext
  exact cartesianComplementValue_idempotent field field.continuous

theorem mem_cartesianPhysicalRange_iff (field : C(ClosedDisk, ComplexEuclidean 3)) :
    field ∈ cartesianPhysicalRange ↔ cartesianComplementMap field = field := by
  constructor
  · rintro ⟨source, rfl⟩
    exact cartesianComplementMap_idempotent source
  · intro fixed
    exact ⟨field, fixed⟩

end Grad.GaugeCoefficients.Physical.RadialLedger
