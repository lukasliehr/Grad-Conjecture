import AKAC14OriginalCovariantRotationRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceCollarAngular Grad.AnnularCurrentEnergy Grad.AnnularCurrentLow
open Grad.AnnularGeneralSourceRegularity Grad.AnnularSmoothCore Grad.PhaseAlgebra

/-- Pure angular translation leaves the original cell phase and rho exactly
unchanged. -/
theorem lowRhoPhysicalCoefficient_shift {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (field : DivisionRow dimension lower) (shift : ℤ)
    (radius : ℝ) (mode : ℤ × ℤ) :
    lowRhoPhysicalCoefficient parameters lower positive (annularRowShift lower 0 shift field) radius mode =
      lowRhoPhysicalCoefficient parameters lower positive field radius (mode.1-shift,mode.2) := by
  unfold lowRhoPhysicalCoefficient
  simp only [annularRowShift_apply,annularShiftScalar,pow_zero,Complex.ofReal_one,one_smul]
  rfl

def SmoothLowPhysicalRow.angularShift {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row) (shift : ℤ) :
    SmoothLowPhysicalRow parameters lower positive (annularRowShift lower 0 shift row) where
  curve grade radius := weightedAngularHilbertShift parameters dimension grade shift (curves.curve grade radius)
  smooth grade := (weightedAngularHilbertShift parameters dimension grade shift).restrictScalars ℝ |>.contDiff.comp_contDiffOn (curves.smooth grade)
  same grade := by
    filter_upwards [curves.same grade] with radius same
    intro mode
    rw [weightedAngularHilbertShift_weighted parameters grade shift _ _ same mode,lowRhoPhysicalCoefficient_shift]

def SmoothLowPhysicalRow.sub {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {first second : DivisionRow dimension lower}
    (a : SmoothLowPhysicalRow parameters lower positive first) (b : SmoothLowPhysicalRow parameters lower positive second) :
    SmoothLowPhysicalRow parameters lower positive (first-second) where
  curve grade radius := a.curve grade radius-b.curve grade radius
  smooth grade := (a.smooth grade).sub (b.smooth grade)
  same grade := by
    filter_upwards [a.same grade,b.same grade,lowRhoPhysicalCoefficient_sub_ae parameters lower positive first second]
      with radius one two subtracted
    intro mode
    change a.curve grade radius mode-b.curve grade radius mode = _
    rw [one mode,two mode,subtracted mode,smul_sub,smul_sub]

def SmoothLowPhysicalRow.smul {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row) (scalar : ℂ) :
    SmoothLowPhysicalRow parameters lower positive (scalar • row) where
  curve grade radius := scalar • curves.curve grade radius
  smooth grade := (curves.smooth grade).const_smul scalar
  same grade := by
    have stored (mode : ℤ × ℤ) := Lp.coeFn_smul scalar (row mode)
    filter_upwards [curves.same grade,ae_all_iff.mpr stored] with radius same scaled
    intro mode
    change scalar • curves.curve grade radius mode = _
    rw [same mode]
    unfold lowRhoPhysicalCoefficient
    change _ = _ • (_ • (_ • (scalar • row mode) radius))
    rw [scaled mode]
    simp only [Pi.smul_apply,smul_smul]
    congr 1
    ring

def SmoothLowPhysicalRow.cosine {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row) :
    SmoothLowPhysicalRow parameters lower positive (cosineRow lower 0 row) :=
  ((curves.angularShift 1).add (curves.angularShift (-1))).smul (2 : ℂ)⁻¹

def SmoothLowPhysicalRow.sine {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row) :
    SmoothLowPhysicalRow parameters lower positive (sineRow lower 0 row) :=
  ((curves.angularShift 1).sub (curves.angularShift (-1))).smul (2 * Complex.I : ℂ)⁻¹

/-- The exact Cartesian covariant, with all original weighted radial grades,
is obtained by the required Q rotation of the actual polar covariant. -/
def SmoothLowPhysicalRow.cartesianCovariant {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) :
    SmoothLowPhysicalRow parameters lower positive (cartesianCovariantRow lower row) :=
  ((((curves.cosine.bulkUnit (0 : Fin 3) 0).sub (curves.sine.bulkUnit (0 : Fin 3) 1)).add
    (curves.sine.bulkUnit (1 : Fin 3) 0)).add (curves.cosine.bulkUnit (1 : Fin 3) 1)).add
      (curves.bulkUnit (2 : Fin 3) 2)

end Grad.ActualSmoothPhysicalField
