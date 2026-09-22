import AJI19ActualRadialSystemOperator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.GaugeCoefficients.Physical.Ledger

def frequencyNumerator (axis : Option Bool) (mode : ℤ × ℤ) : ℂ :=
  match axis with | none => 1 | some false => Complex.I * (mode.1 : ℂ) | some true => Complex.I * (mode.2 : ℂ)

theorem frequencyRatio_weighted (axis : Option Bool) (mode : ℤ × ℤ) (grade : ℕ) (value : ComplexEuclidean 1) :
    frequencyRatioSymbol axis mode • (((annularFrequency mode.1 mode.2 ^ (grade + 1) : ℝ) : ℂ) • value) =
      ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • (frequencyNumerator axis mode • value) := by
  have nonzero : (annularFrequency mode.1 mode.2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Grad.SourceBoundaryTrace.annularFrequency_pos mode).ne'
  have scalarLaw (a b : ℂ) (nonzero : b ≠ 0) : (a / b) * b ^ (grade + 1) = b ^ grade * a := by
    rw [pow_succ]
    field_simp
  change (frequencyNumerator axis mode / (annularFrequency mode.1 mode.2 : ℂ)) •
      (((annularFrequency mode.1 mode.2 ^ (grade + 1) : ℝ) : ℂ) • value) = _
  rw [smul_smul, Complex.ofReal_pow, scalarLaw _ _ nonzero, mul_smul, ← Complex.ofReal_pow]

/-- Literal physical unknown input (x,Rxi/r,xi_zeta,xi/r,0,0,0). -/
def rawPhysicalSevenVector (radius : ℝ) (mode : ℤ × ℤ) (x xi : ComplexEuclidean 1) : ComplexEuclidean 7 :=
  ((matrixUnit (0 : Fin 7) (0 : Fin 1) x +
    (radius : ℂ)⁻¹ • matrixUnit (1 : Fin 7) (0 : Fin 1) (frequencyNumerator (some false) mode • xi)) +
    matrixUnit (2 : Fin 7) (0 : Fin 1) (frequencyNumerator (some true) mode • xi)) +
    (radius : ℂ)⁻¹ • matrixUnit (3 : Fin 7) (0 : Fin 1) xi

theorem rawUnknownSevenOperator_coefficient (parameters : PhaseParameters) (radius : ℝ)
    (field : PhysicalHilbertPair) (mode : ℤ × ℤ) :
    rawUnknownSevenOperator parameters radius field mode =
      ((matrixUnit (0 : Fin 7) (0 : Fin 1) (frequencyRatioSymbol none mode • field.1 mode) +
        (radius : ℂ)⁻¹ • matrixUnit (1 : Fin 7) (0 : Fin 1) (frequencyRatioSymbol (some false) mode • field.2 mode)) +
        matrixUnit (2 : Fin 7) (0 : Fin 1) (frequencyRatioSymbol (some true) mode • field.2 mode)) +
        (radius : ℂ)⁻¹ • matrixUnit (3 : Fin 7) (0 : Fin 1) (frequencyRatioSymbol none mode • field.2 mode) := rfl

theorem rawUnknownSevenOperator_weighted (parameters : PhaseParameters) (radius : ℝ) (grade : ℕ)
    (field : PhysicalHilbertPair) (mode : ℤ × ℤ) (x xi : ComplexEuclidean 1)
    (sameX : field.1 mode = ((annularFrequency mode.1 mode.2 ^ (grade + 1) : ℝ) : ℂ) • x)
    (sameXi : field.2 mode = ((annularFrequency mode.1 mode.2 ^ (grade + 1) : ℝ) : ℂ) • xi) :
    rawUnknownSevenOperator parameters radius field mode =
      ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • rawPhysicalSevenVector radius mode x xi := by
  rw [rawUnknownSevenOperator_coefficient, sameX, sameXi,
    frequencyRatio_weighted, frequencyRatio_weighted, frequencyRatio_weighted, frequencyRatio_weighted]
  simp only [frequencyNumerator, one_smul, map_smul, rawPhysicalSevenVector, smul_add]
  simp only [smul_comm ((radius : ℂ)⁻¹) ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ)]

open Grad.AnnularCoupledInverse Grad.AnnularHighGenerators

/-- The SAME full coupled field supplies the literal physical unknown input
at the next polynomial grade; no new field is solved for. -/
theorem sameCoupledUnknownInput_coefficient (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (grade : ℕ) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    rawUnknownSevenOperator parameters radius.val
      (sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive (grade + 2) field radius,
        sameCoupledPhysicalXiSection parameters lower length positive bounded lengthPositive (grade + 2) field radius) mode =
      ((annularFrequency mode.1 mode.2 ^ (grade + 1) : ℝ) : ℂ) • rawPhysicalSevenVector radius.val mode
        (sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive 0 field radius mode)
        (sameCoupledPhysicalXiSection parameters lower length positive bounded lengthPositive 0 field radius mode) := by
  exact rawUnknownSevenOperator_weighted parameters radius.val (grade + 1) _ mode _ _
    (sameCoupledPhysicalXSection_grade parameters lower length positive bounded lengthPositive field allGrades (grade + 2) radius mode)
    (sameCoupledPhysicalXiSection_grade parameters lower length positive bounded lengthPositive field allGrades (grade + 2) radius mode)

end Grad.AnnularSmoothCore
