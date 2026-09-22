import AJU5FullMixedFourierSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff Interval ENNReal BigOperators
namespace Grad.AnnularPhysicalFourier
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularJointRegularity Grad.AnnularRegularity

section MixedDerivatives
variable (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (jet : PhysicalFourierJet lower positive bounded)

/-- Genuine angular differentiation in the uniform closed-radial norm. -/
theorem physicalMixedFourierSection_angular (radial angular cell : ℕ) (polar axial : ℝ) :
    HasDerivAt (fun angle => physicalMixedFourierSection lower positive bounded jet radial angular cell (angle, axial))
      (physicalMixedFourierSection lower positive bounded jet radial (angular + 1) cell (polar, axial)) polar := by
  have majorant := jet.summable radial (angular + 1 + cell)
  have each (mode : (ℤ × ℤ)) (angle : ℝ) :=
    (physicalFourierCoefficient_angular angular cell mode angle axial).smul_const
      (jet.sections radial mode)
  have bound (mode : (ℤ × ℤ)) (angle : ℝ) :
      ‖physicalFourierCoefficient (angular + 1) cell mode (angle, axial) •
          jet.sections radial mode‖ ≤
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2) ^ (angular + 1 + cell) *
          ‖jet.sections radial mode‖ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (physicalFourierCoefficient_norm_le (angular + 1) cell mode (angle, axial)) (norm_nonneg _)
  exact hasDerivAt_tsum majorant each bound
    (physicalFourierSection_terms_summable lower positive bounded jet radial angular cell (0, axial)) polar

/-- Genuine cell-angle differentiation, with the original cell frequency. -/
theorem physicalMixedFourierSection_cell (radial angular cell : ℕ) (polar axial : ℝ) :
    HasDerivAt (fun angle => physicalMixedFourierSection lower positive bounded jet radial angular cell (polar, angle))
      (physicalMixedFourierSection lower positive bounded jet radial angular (cell + 1) (polar, axial)) axial := by
  have majorant := jet.summable radial (angular + (cell + 1))
  have each (mode : (ℤ × ℤ)) (angle : ℝ) :=
    (physicalFourierCoefficient_cell angular cell mode polar angle).smul_const
      (jet.sections radial mode)
  have bound (mode : (ℤ × ℤ)) (angle : ℝ) :
      ‖physicalFourierCoefficient angular (cell + 1) mode (polar, angle) •
          jet.sections radial mode‖ ≤
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2) ^ (angular + (cell + 1)) *
          ‖jet.sections radial mode‖ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (physicalFourierCoefficient_norm_le angular (cell + 1) mode (polar, angle)) (norm_nonneg _)
  exact hasDerivAt_tsum majorant each bound
    (physicalFourierSection_terms_summable lower positive bounded jet radial angular cell (polar, 0)) axial

/-- All mixed derivative values are jointly continuous through both radial
endpoints; this is continuity on the actual closed product domain. -/
theorem physicalMixedFourierValue_continuous (radial angular cell : ℕ) :
    Continuous (fun point : (Icc lower (1 : ℝ)) × (ℝ × ℝ) =>
      physicalMixedFourierSection lower positive bounded jet radial angular cell point.2 point.1) := by
  exact continuous_eval.comp
    (((physicalMixedFourierSection_continuous lower positive bounded jet radial angular cell).comp
      continuous_snd).prodMk continuous_fst)

theorem physicalMixedFourierValue_angular (radial angular cell : ℕ)
    (radius : Icc lower (1 : ℝ)) (polar axial : ℝ) :
    HasDerivAt (fun angle => physicalMixedFourierSection lower positive bounded jet radial angular cell (angle, axial) radius)
      (physicalMixedFourierSection lower positive bounded jet radial (angular + 1) cell (polar, axial) radius) polar :=
  (ContinuousMap.evalCLM ℝ radius : RadialContinuousSection 1 lower →L[ℝ] ComplexEuclidean 1).hasFDerivAt.comp_hasDerivAt polar
    (physicalMixedFourierSection_angular lower positive bounded jet radial angular cell polar axial)

theorem physicalMixedFourierValue_cell (radial angular cell : ℕ)
    (radius : Icc lower (1 : ℝ)) (polar axial : ℝ) :
    HasDerivAt (fun angle => physicalMixedFourierSection lower positive bounded jet radial angular cell (polar, angle) radius)
      (physicalMixedFourierSection lower positive bounded jet radial angular (cell + 1) (polar, axial) radius) axial :=
  (ContinuousMap.evalCLM ℝ radius : RadialContinuousSection 1 lower →L[ℝ] ComplexEuclidean 1).hasFDerivAt.comp_hasDerivAt axial
    (physicalMixedFourierSection_cell lower positive bounded jet radial angular cell polar axial)

end MixedDerivatives
end Grad.AnnularPhysicalFourier
