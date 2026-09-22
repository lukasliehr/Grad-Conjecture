import ADW1ActualOmegaBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularOmegaGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularGrades Grad.AnnularFluxTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- A global continuous coefficient agreeing with the original omega at
 every point of the physical collar. -/
def annularOmegaCurve (lower length : ℝ) (positive : 0 < lower) (mode : HighAnnularMode) : C(ℝ, ℝ) :=
  ⟨fun radius => annularOmega length (max lower radius) mode,
    Real.continuous_sqrt.comp
      (((continuous_const.div (continuous_const.max continuous_id)
        (fun radius => (positive.trans_le (le_max_left lower radius)).ne')).pow 2).add continuous_const)⟩

theorem annularOmegaCurve_pos (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (radius : ℝ) : 0 < annularOmegaCurve lower length positive mode radius :=
  annularOmega_pos length (max lower radius) (positive.trans_le (le_max_left _ _)) mode

def annularOmegaOverNuCurve (lower length : ℝ) (positive : 0 < lower) (mode : HighAnnularMode) : C(ℝ, ℝ) :=
  ⟨fun radius => annularOmegaCurve lower length positive mode radius /
    Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2,
    (annularOmegaCurve lower length positive mode).continuous.div_const _⟩

def annularNuOverOmegaCurve (lower length : ℝ) (positive : 0 < lower) (mode : HighAnnularMode) : C(ℝ, ℝ) :=
  ⟨fun radius => Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 /
    annularOmegaCurve lower length positive mode radius,
    continuous_const.div (annularOmegaCurve lower length positive mode).continuous
      (fun radius => (annularOmegaCurve_pos lower length positive mode radius).ne')⟩

theorem annularOmegaOverNu_bound (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |annularOmegaOverNuCurve lower length positive mode radius| ≤ (1 + length⁻¹) / lower := by
  have frequencyPositive := Grad.AnnularFluxTrace.annularFrequency_pos mode
  change |annularOmega length (max lower radius) mode / Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2| ≤ _
  rw [max_eq_right inside.1, abs_of_pos (div_pos (annularOmega_pos length radius (positive.trans_le inside.1) mode) frequencyPositive)]
  apply (div_le_iff₀ frequencyPositive).mpr
  exact (annularOmega_le_nu length radius lengthPositive (positive.trans_le inside.1) inside.2 mode).trans
    (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (by positivity) positive inside.1) frequencyPositive.le)

theorem annularNuOverOmega_bound (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |annularNuOverOmegaCurve lower length positive mode radius| ≤ 2 + length := by
  change |Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 / annularOmega length (max lower radius) mode| ≤ _
  rw [max_eq_right inside.1, abs_of_pos (div_pos (Grad.AnnularFluxTrace.annularFrequency_pos mode)
    (annularOmega_pos length radius (positive.trans_le inside.1) mode))]
  exact (div_le_iff₀ (annularOmega_pos length radius (positive.trans_le inside.1) mode)).mpr
    (annularNu_le_omega length radius lengthPositive (positive.trans_le inside.1) inside.2 mode)

def annularOmegaToNu (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  annularScalarFamily lower (annularOmegaOverNuCurve lower length positive)
    ((1 + length⁻¹) / lower) (by positivity) (annularOmegaOverNu_bound lower length positive lengthPositive)

def annularNuToOmega (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  annularScalarFamily lower (annularNuOverOmegaCurve lower length positive)
    (2 + length) (by positivity) (annularNuOverOmega_bound lower length positive lengthPositive)

theorem annularOmegaCurves_inverse (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (radius : ℝ) :
    annularNuOverOmegaCurve lower length positive mode radius * annularOmegaOverNuCurve lower length positive mode radius = 1 := by
  change (_ / annularOmegaCurve lower length positive mode radius) *
    (annularOmegaCurve lower length positive mode radius / Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) = 1
  field_simp [(annularOmegaCurve_pos lower length positive mode radius).ne', (Grad.AnnularFluxTrace.annularFrequency_pos mode).ne']

theorem scalarRadialMaps_inverse (lower : ℝ) (first second : C(ℝ, ℝ))
    (firstBound secondBound : ℝ)
    (firstLaw : ∀ radius ∈ Icc lower 1, |first radius| ≤ firstBound)
    (secondLaw : ∀ radius ∈ Icc lower 1, |second radius| ≤ secondBound)
    (inverse : ∀ radius, first radius * second radius = 1) (field : RadialL2 1 lower) :
    scalarRadialMap lower first firstBound firstLaw (scalarRadialMap lower second secondBound secondLaw field) = field := by
  apply Lp.ext
  filter_upwards [scalarRadialMap_ae lower first firstBound firstLaw
      (scalarRadialMap lower second secondBound secondLaw field),
    scalarRadialMap_ae lower second secondBound secondLaw field] with radius outer inner
  rw [outer, inner, smul_smul, inverse, one_smul]

theorem annularNuToOmega_left (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : AnnularBulk lower) :
    annularNuToOmega lower length positive lengthPositive (annularOmegaToNu lower length positive lengthPositive field) = field := by
  apply lp.ext
  funext mode
  exact scalarRadialMaps_inverse lower (annularNuOverOmegaCurve lower length positive mode)
    (annularOmegaOverNuCurve lower length positive mode) (2 + length) ((1 + length⁻¹) / lower)
    (annularNuOverOmega_bound lower length positive lengthPositive mode)
    (annularOmegaOverNu_bound lower length positive lengthPositive mode)
    (annularOmegaCurves_inverse lower length positive mode) (field mode)

theorem annularOmegaToNu_right (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : AnnularBulk lower) :
    annularOmegaToNu lower length positive lengthPositive (annularNuToOmega lower length positive lengthPositive field) = field := by
  apply lp.ext
  funext mode
  exact scalarRadialMaps_inverse lower (annularOmegaOverNuCurve lower length positive mode)
    (annularNuOverOmegaCurve lower length positive mode) ((1 + length⁻¹) / lower) (2 + length)
    (annularOmegaOverNu_bound lower length positive lengthPositive mode)
    (annularNuOverOmega_bound lower length positive lengthPositive mode)
    (fun radius => (mul_comm _ _).trans (annularOmegaCurves_inverse lower length positive mode radius)) (field mode)

theorem annularOmegaToNu_injective (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    Function.Injective (annularOmegaToNu lower length positive lengthPositive) :=
  Function.LeftInverse.injective (annularNuToOmega_left lower length positive lengthPositive)

end Grad.AnnularOmegaGraph
