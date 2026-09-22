import AIW18OriginalLowBF6Consumer
import AJS3SameLowCoordinateDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.GaugeCoefficients.Physical.WeightedTrace

theorem collarMeasure_le (lower upper : ℝ) (included : lower ≤ upper) :
    volume.restrict (Icc upper (1 : ℝ)) ≤ volume.restrict (Icc lower (1 : ℝ)) :=
  Measure.restrict_mono (Icc_subset_Icc included le_rfl) le_rfl

def collarL2RestrictionValue (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (field : CollarL2 (ComplexEuclidean dimension) lower) : CollarL2 (ComplexEuclidean dimension) upper :=
  (MemLp.mono_measure (collarMeasure_le lower upper included) (Lp.memLp field)).toLp field

theorem collarL2RestrictionValue_ae (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (field : CollarL2 (ComplexEuclidean dimension) lower) :
    collarL2RestrictionValue dimension lower upper included field =ᵐ[volume.restrict (Icc upper 1)] field :=
  (MemLp.mono_measure (collarMeasure_le lower upper included) (Lp.memLp field)).coeFn_toLp

theorem collarL2RestrictionValue_bound (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (field : CollarL2 (ComplexEuclidean dimension) lower) :
    ‖collarL2RestrictionValue dimension lower upper included field‖ ≤ ‖field‖ := by
  rw [collarL2RestrictionValue, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp field).2.ne
    (eLpNorm_mono_measure field (collarMeasure_le lower upper included))

def collarL2RestrictionLinear (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper) :
    CollarL2 (ComplexEuclidean dimension) lower →ₗ[ℂ] CollarL2 (ComplexEuclidean dimension) upper where
  toFun := collarL2RestrictionValue dimension lower upper included
  map_add' first second := by
    apply Lp.ext
    filter_upwards [collarL2RestrictionValue_ae dimension lower upper included (first + second),
      collarL2RestrictionValue_ae dimension lower upper included first,
      collarL2RestrictionValue_ae dimension lower upper included second,
      (Lp.coeFn_add first second).filter_mono (ae_mono (collarMeasure_le lower upper included)),
      Lp.coeFn_add (collarL2RestrictionValue dimension lower upper included first)
        (collarL2RestrictionValue dimension lower upper included second)] with radius sum firstLaw secondLaw added imageSum
    rw [sum, added, imageSum]
    simp only [Pi.add_apply, firstLaw, secondLaw]
  map_smul' scalar field := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [collarL2RestrictionValue_ae dimension lower upper included (scalar • field),
      collarL2RestrictionValue_ae dimension lower upper included field,
      (Lp.coeFn_smul scalar field).filter_mono (ae_mono (collarMeasure_le lower upper included)),
      Lp.coeFn_smul scalar (collarL2RestrictionValue dimension lower upper included field)]
      with radius scaled actual sourceScaled targetScaled
    rw [scaled, sourceScaled, targetScaled]
    simp only [Pi.smul_apply, actual]

/-- Literal restriction of the actual L2 representative to the smaller
positive collar, with no zero extension or new radial multiplier. -/
def collarL2Restriction (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper) :
    CollarL2 (ComplexEuclidean dimension) lower →L[ℂ] CollarL2 (ComplexEuclidean dimension) upper :=
  (collarL2RestrictionLinear dimension lower upper included).mkContinuous 1
    (fun field => by
      change ‖collarL2RestrictionValue dimension lower upper included field‖ ≤ 1 * ‖field‖
      rw [one_mul]
      exact collarL2RestrictionValue_bound dimension lower upper included field)

theorem collarL2Restriction_ae (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (field : CollarL2 (ComplexEuclidean dimension) lower) :
    collarL2Restriction dimension lower upper included field =ᵐ[volume.restrict (Icc upper 1)] field :=
  collarL2RestrictionValue_ae dimension lower upper included field

theorem collarL2Restriction_bound (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (field : CollarL2 (ComplexEuclidean dimension) lower) :
    ‖collarL2Restriction dimension lower upper included field‖ ≤ ‖field‖ :=
  collarL2RestrictionValue_bound dimension lower upper included field

theorem collarL2Restriction_id (dimension : ℕ) (lower : ℝ)
    (field : CollarL2 (ComplexEuclidean dimension) lower) :
    collarL2Restriction dimension lower lower le_rfl field = field :=
  Lp.ext (collarL2Restriction_ae dimension lower lower le_rfl field)

theorem collarL2Restriction_comp (dimension : ℕ) (lower middle upper : ℝ)
    (first : lower ≤ middle) (second : middle ≤ upper)
    (field : CollarL2 (ComplexEuclidean dimension) lower) :
    collarL2Restriction dimension middle upper second (collarL2Restriction dimension lower middle first field) =
      collarL2Restriction dimension lower upper (first.trans second) field := by
  apply Lp.ext
  exact ((collarL2Restriction_ae dimension middle upper second _).trans
    ((collarL2Restriction_ae dimension lower middle first field).filter_mono
      (ae_mono (collarMeasure_le middle upper second)))).trans
    (collarL2Restriction_ae dimension lower upper (first.trans second) field).symm

end Grad.AnnularRestriction
