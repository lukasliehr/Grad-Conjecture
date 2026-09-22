import AKDK2JointOriginalSourceAllocation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.OriginalTerminalAllocation
open Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.SourceCollarRestriction Grad.SourceCollarFullSource
open Grad.AnnularGeneralSourceRegularity Grad.PhaseAlgebra

/-- The SAME phase-weighted Cartesian curve has every mixed radial and
tangential derivative at its exact total original grade on a fixed collar. -/
theorem actualCartesianCurve_mixedCollarEnergy {dimension grade power radial : ℕ}
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (paid : power + radial ≤ grade) (field : ACore parameters dimension) :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖cartesianWeightedRadialCurve parameters lower positive bounded field power radial radius‖^2)) ≤
    ENNReal.ofReal ((lower⁻¹ * Real.sqrt (restrictionRowConstant power radial) *
      ‖GradeCore.ofCoreLinear (grade := grade) field‖)^2) := by
  let row := cartesianWeightedRadialRow parameters lower positive bounded field power radial
  have same : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      cartesianWeightedRadialCurve parameters lower positive bounded field power radial radius mode =
      (annularFrequency mode.1 mode.2 : ℂ)^power •
        ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
          originalRowCoefficient parameters power lower row radius mode) := by
    have stored (mode : ℤ × ℤ) := radialToLp_ae lower
      (radialCoefficientJet (originalPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2))) mode.1 radial)
      (radialCoefficientJet_smooth _ (originalPolarValue_smooth _) _ _).continuous
    have scaled (mode : ℤ × ℤ) := Lp.coeFn_smul ((annularFrequency mode.1 mode.2 : ℂ)^power)
      (radialToLp lower
        (radialCoefficientJet (originalPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2))) mode.1 radial)
        (radialCoefficientJet_smooth _ (originalPolarValue_smooth _) _ _).continuous)
    filter_upwards [ae_all_iff.mpr stored,ae_all_iff.mpr scaled,ae_restrict_mem measurableSet_Icc]
      with radius stored scaled inside
    intro mode
    rw [cartesianWeightedRadialCurve_coefficient parameters lower positive bounded field power radial mode radius inside]
    change (annularFrequency mode.1 mode.2 : ℂ)^power • _ = _
    have root : (Real.sqrt radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (positive.trans_le inside.1)).ne'
    have phase : (Real.exp (radialPhase parameters radius mode.2) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
    have frequency : (annularFrequency mode.1 mode.2 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Grad.SourceBoundaryTrace.annularFrequency_pos mode).ne'
    change _ = (annularFrequency mode.1 mode.2 : ℂ)^power •
      ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
        ((originalRowWeight parameters power radius mode : ℂ)⁻¹ •
          (restrictionModeLp lower power radial parameters field mode) radius))
    unfold restrictionModeLp
    rw [scaled mode]
    simp only [Pi.smul_apply]
    rw [stored mode]
    simp only [← Complex.coe_smul]
    simp only [originalRowWeight,Complex.ofReal_mul,Complex.ofReal_pow,smul_smul]
    congr 1
    field_simp
  have energy := originalSourceCurve_collarEnergy parameters lower positive power row _ same
  have normBound := completedRestrictionRow_bound lower positive bounded.le parameters paid
    (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field))
  rw [cartesianRestrictionRow_exact parameters lower positive bounded,aGradeEta_norm] at normBound
  have payment := mul_le_mul_of_nonneg_left normBound (inv_nonneg.mpr positive.le)
  rw [← mul_assoc] at payment
  exact energy.trans (ENNReal.ofReal_le_ofReal
    ((sq_le_sq₀ (by positivity) (by positivity)).mpr payment))

end Grad.OriginalTerminalAllocation
