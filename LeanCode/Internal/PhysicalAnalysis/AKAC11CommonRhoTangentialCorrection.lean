import AKAC10OriginalScalarCorrectionNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularPhysicalFourier Grad.AnnularKernelL2 Grad.SourceCollarFullSource Grad.SourceCollarAngular
open Grad.AnnularCurrentLow Grad.AnnularCurrentEnergy Grad.Constraints.Gauges

/-- Conversion between the original r dr coordinate and the original low
common rho. It depends only on radius and cell, so angular shifts commute. -/
def commonRhoConversion (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (radius : ℝ) (cell : ℤ) : ℂ :=
  (lowRhoPhysicalWeight parameters lower positive radius (0,cell) : ℂ)⁻¹ *
    (originalRowWeight parameters 0 radius (0,cell) : ℂ)

theorem lowRhoPhysicalCoefficient_original {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (row : DivisionRow dimension lower) (radius : ℝ)
    (radiusPositive : 0 < radius) (mode : ℤ × ℤ) :
    lowRhoPhysicalCoefficient parameters lower positive row radius mode =
      commonRhoConversion parameters lower positive radius mode.2 •
        originalRowCoefficient parameters 0 lower row radius mode := by
  have weight : originalRowWeight parameters 0 radius mode = originalRowWeight parameters 0 radius (0,mode.2) := by
    simp [originalRowWeight]
  have nonzero : (originalRowWeight parameters 0 radius (0,mode.2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (originalRowWeight_pos parameters 0 radius radiusPositive _).ne'
  unfold lowRhoPhysicalCoefficient commonRhoConversion originalRowCoefficient
  rw [weight,smul_smul,mul_assoc,mul_inv_cancel₀ nonzero,mul_one]
  rfl

theorem lowRhoPhysicalCoefficient_tangential (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (field : DivisionRow 2 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      lowRhoPhysicalCoefficient parameters lower positive (tangentialRowContraction lower positive 0 field) radius mode =
      planarComponentMap 1 ((2 : ℂ)⁻¹ •
        (lowRhoPhysicalCoefficient parameters lower positive field radius (mode.1 - 1,mode.2) +
          lowRhoPhysicalCoefficient parameters lower positive field radius (mode.1 + 1,mode.2))) -
      planarComponentMap 0 ((2 * Complex.I : ℂ)⁻¹ •
        (lowRhoPhysicalCoefficient parameters lower positive field radius (mode.1 - 1,mode.2) -
          lowRhoPhysicalCoefficient parameters lower positive field radius (mode.1 + 1,mode.2))) := by
  filter_upwards [tangentialRowContraction_decoded_ae parameters lower positive field,ae_restrict_mem measurableSet_Icc]
    with radius actual inside
  intro mode
  have radiusPositive := positive.trans_le inside.1
  simp only [lowRhoPhysicalCoefficient_original parameters lower positive _ radius radiusPositive]
  rw [actual mode]
  apply PiLp.ext
  intro component
  fin_cases component
  simp [planarComponentMap,smul_smul]
  ring

theorem lowRhoPhysicalCoefficient_projection {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (field : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      lowRhoPhysicalCoefficient parameters lower positive (meanFreeRow lower field) radius mode =
        if mode.1 = 0 then 0 else lowRhoPhysicalCoefficient parameters lower positive field radius mode := by
  filter_upwards [originalRowCoefficient_meanFree_ae parameters 0 lower field,ae_restrict_mem measurableSet_Icc]
    with radius actual inside
  intro mode
  simp only [lowRhoPhysicalCoefficient_original parameters lower positive _ radius (positive.trans_le inside.1)]
  rw [actual mode]
  split_ifs <;> simp

end Grad.ActualSmoothPhysicalField
