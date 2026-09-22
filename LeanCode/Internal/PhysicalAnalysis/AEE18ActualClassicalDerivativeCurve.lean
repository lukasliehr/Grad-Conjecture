import AEE17OriginalLowReferenceClosedRange

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators ENNReal
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

def scalarClosedExtension (lower : ℝ) (bounded : lower ≤ 1)
    (value : ℝ → ℂ) (continuousValue : ContinuousOn value (Icc lower 1)) : C(ℝ, ℂ) :=
  let sectionValue : C(Icc lower 1, ℂ) :=
    ⟨fun point => value point.val, continuousOn_iff_continuous_domRestrict.mp continuousValue⟩
  ⟨curveExtension lower 1 bounded sectionValue, curveExtension_continuous lower 1 bounded sectionValue⟩

theorem scalarClosedExtension_actual (lower : ℝ) (bounded : lower ≤ 1)
    (value : ℝ → ℂ) (continuousValue : ContinuousOn value (Icc lower 1))
    (radius : ℝ) (member : radius ∈ Icc lower 1) :
    scalarClosedExtension lower bounded value continuousValue radius = value radius := by
  let sectionValue : C(Icc lower 1, ℂ) :=
    ⟨fun point => value point.val, continuousOn_iff_continuous_domRestrict.mp continuousValue⟩
  change curveExtension lower 1 bounded sectionValue radius = value radius
  exact curveExtension_of_mem lower 1 bounded sectionValue radius member

/-- The actual reference derivative has a continuous extension suitable for
the already accepted radial primitive realization. -/
def lowClassicalDerivativeCurve (parameters : PhaseParameters) (length lower : ℝ) (positive : 0 < lower)
    (mode : LowAnnularMode) (row : Fin 2) (first second forcing : C(ℝ, ℂ)) : C(ℝ, ℂ) where
  toFun radius := lowMuCurve lower length positive mode.val.2 radius •
    (lowNormalizedReferenceCurve parameters length lower positive mode row 0 radius • first radius +
      lowNormalizedReferenceCurve parameters length lower positive mode row 1 radius • second radius + forcing radius)
  continuous_toFun := (lowMuCurve lower length positive mode.val.2).continuous.smul
    ((((lowNormalizedReferenceCurve parameters length lower positive mode row 0).continuous.smul first.continuous).add
      ((lowNormalizedReferenceCurve parameters length lower positive mode row 1).continuous.smul second.continuous)).add forcing.continuous)

theorem lowClassicalDerivativeCurve_actual (parameters : PhaseParameters) (length lower : ℝ) (positive : 0 < lower)
    (mode : LowAnnularMode) (row : Fin 2) (first second forcing : C(ℝ, ℂ)) (radius : ℝ) (inside : lower ≤ radius) :
    lowClassicalDerivativeCurve parameters length lower positive mode row first second forcing radius =
      lowReferenceMatrix parameters length radius mode row 0 • first radius +
        lowReferenceMatrix parameters length radius mode row 1 • second radius +
        lowMu length radius mode.val.2 • forcing radius := by
  change lowMuCurve lower length positive mode.val.2 radius •
    (lowNormalizedReferenceCurve parameters length lower positive mode row 0 radius • first radius +
      lowNormalizedReferenceCurve parameters length lower positive mode row 1 radius • second radius + forcing radius) = _
  rw [lowNormalizedReferenceCurve_actual parameters length lower positive mode row 0 radius inside,
    lowNormalizedReferenceCurve_actual parameters length lower positive mode row 1 radius inside]
  have frequency : lowMuCurve lower length positive mode.val.2 radius = lowMu length radius mode.val.2 := by
    change lowMu length (max lower radius) mode.val.2 = _
    rw [max_eq_right inside]
  rw [frequency, smul_add, smul_add, smul_smul, smul_smul]
  have firstCancel : lowMu length radius mode.val.2 *
      (lowReferenceMatrix parameters length radius mode row 0 / lowMu length radius mode.val.2) =
      lowReferenceMatrix parameters length radius mode row 0 := by
    field_simp [(lowMu_pos length radius mode.val.2 (positive.trans_le inside)).ne']
  have secondCancel : lowMu length radius mode.val.2 *
      (lowReferenceMatrix parameters length radius mode row 1 / lowMu length radius mode.val.2) =
      lowReferenceMatrix parameters length radius mode row 1 := by
    field_simp [(lowMu_pos length radius mode.val.2 (positive.trans_le inside)).ne']
  rw [firstCancel, secondCancel]

end Grad.AnnularLowCompletion
