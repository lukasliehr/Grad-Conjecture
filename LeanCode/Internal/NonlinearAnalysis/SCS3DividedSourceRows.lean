import SCS2PolarRows

noncomputable section

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.CompatibleCompletion Grad.ConstrainedGrades Grad.AxisCore
open Grad.QuotientProjection Grad.SourceCollarBulk Grad.SourceCollarDivision Grad.SourceCollarCoefficients

theorem originalSourcePlanar_lower {lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (source : ZAmbient parameters upper) :
    completedInclusion parameters ordered (originalSourcePlanar parameters upper source) =
      originalSourcePlanar parameters lower (zLowering parameters ordered source) := by
  refine isClosed_property (quotientEta_denseRange parameters upper)
    (isClosed_eq ((completedInclusion parameters ordered).continuous.comp
      (originalSourcePlanar parameters upper).continuous)
      ((originalSourcePlanar parameters lower).continuous.comp (zLowering parameters ordered).continuous)) ?_ source
  intro core
  simp only [Function.comp_apply]
  rw [originalSourcePlanar_core, completedInclusion_apply_eta, zLowering_core, originalSourcePlanar_core]
  rfl

def dividedPlanar {grade power : ℕ} (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + 3 ≤ grade) (source : ZAmbient parameters grade) :
    DivisionRow 2 lower :=
  completedDivisionRow (power := power) (radial := 0) lower positive bounded parameters paid
    (originalSourcePlanar parameters grade source)

def dividedFourth {grade power : ℕ} (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (L : ℝ) (paid : power + 3 ≤ grade) (source : ZAmbient parameters grade) :
    DivisionRow 1 lower :=
  (L : ℂ)⁻¹ • completedDivisionRow (power := power) (radial := 0) lower positive bounded parameters paid (source 3)

/-- Ordered as (F1/r,F0/r,F2/r), including the original physical L in F2. -/
def dividedSourceRows {grade power : ℕ} (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (L : ℝ) (paid : power + 3 ≤ grade) (source : ZAmbient parameters grade) :
    Fin 3 → DivisionRow 1 lower :=
  ![radialRowContraction lower positive power (dividedPlanar lower positive bounded parameters paid source),
    tangentialRowContraction lower positive power (dividedPlanar lower positive bounded parameters paid source),
    dividedFourth lower positive bounded parameters L paid source]

theorem dividedSourceRows_compatible {grade power : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (L : ℝ) (paid : power + 3 ≤ grade)
    (source : ZAmbient parameters grade) (component : Fin 3) :
    RadialRowsCompatible lower power
      (dividedSourceRows lower positive bounded parameters L paid source component)
      (dividedSourceRows (power := 0) lower positive bounded parameters L (by omega) source component) := by
  have planar := completedDivisionRow_compatible lower positive bounded parameters paid
    (originalSourcePlanar parameters grade source)
  have fourth := completedDivisionRow_compatible lower positive bounded parameters paid (source 3)
  fin_cases component
  · exact planar.radial positive
  · exact planar.tangential positive
  · exact fourth.smul _

def sourceDivisionConstant (power : ℕ) (L : ℝ) : ℝ :=
  (2 * 2 ^ power + |L⁻¹|) * Real.sqrt (finiteAngularBoundConstant power 0)

theorem sourceDivisionConstant_nonnegative (power : ℕ) (L : ℝ) :
    0 ≤ sourceDivisionConstant power L := by unfold sourceDivisionConstant; positivity

theorem dividedPlanar_bound {grade power : ℕ} (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + 3 ≤ grade) (source : ZAmbient parameters grade) :
    ‖dividedPlanar lower positive bounded parameters paid source‖ ≤
      Real.sqrt (finiteAngularBoundConstant power 0) * ‖source‖ :=
  (completedDivisionRow_bound lower positive bounded parameters paid _).trans
    (mul_le_mul_of_nonneg_left (originalSourcePlanar_bound parameters grade source) (Real.sqrt_nonneg _))

theorem dividedSourceRows_bound {grade power : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (L : ℝ) (paid : power + 3 ≤ grade)
    (source : ZAmbient parameters grade) (component : Fin 3) :
    ‖dividedSourceRows lower positive bounded parameters L paid source component‖ ≤
      sourceDivisionConstant power L * ‖source‖ := by
  have planar := dividedPlanar_bound lower positive bounded parameters paid source
  have fourth := (completedDivisionRow_bound (power := power) (radial := 0) lower positive bounded parameters paid (source 3)).trans
    (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le source 3) (Real.sqrt_nonneg _))
  have rootNonnegative := Real.sqrt_nonneg (finiteAngularBoundConstant power 0)
  have sourceNonnegative := norm_nonneg source
  fin_cases component
  · exact (radialRowContraction_bound lower positive power _).trans (by
      unfold sourceDivisionConstant
      nlinarith [mul_le_mul_of_nonneg_left planar (by positivity : (0 : ℝ) ≤ 2 * 2 ^ power),
        mul_nonneg (abs_nonneg L⁻¹) (mul_nonneg rootNonnegative sourceNonnegative)])
  · exact (tangentialRowContraction_bound lower positive power _).trans (by
      unfold sourceDivisionConstant
      nlinarith [mul_le_mul_of_nonneg_left planar (by positivity : (0 : ℝ) ≤ 2 * 2 ^ power),
        mul_nonneg (abs_nonneg L⁻¹) (mul_nonneg rootNonnegative sourceNonnegative)])
  · change ‖(L : ℂ)⁻¹ • completedDivisionRow (power := power) (radial := 0)
      lower positive bounded parameters paid (source 3)‖ ≤ _
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, ← abs_inv]
    unfold sourceDivisionConstant
    nlinarith [mul_le_mul_of_nonneg_left fourth (abs_nonneg L⁻¹),
      mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * 2 ^ power) (mul_nonneg rootNonnegative sourceNonnegative)]

end Grad.SourceCollarFullSource
