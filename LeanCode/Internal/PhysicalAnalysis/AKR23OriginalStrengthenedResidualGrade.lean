import AKR22LiteralFullResidualHilbertCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.PhaseAlgebra
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow Grad.AnnularLowEnergy Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger

open Grad.AnnularCurrentLow Grad.AnnularCurrentSource Grad.AnnularHighTilt

def originalAngularStrengthSymbol (mode : ℤ × ℤ) : ℂ :=
  ((1 + |(mode.1 : ℝ)| : ℝ) : ℂ) / (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)

theorem originalAngularStrengthSymbol_bound (mode : ℤ × ℤ) : ‖originalAngularStrengthSymbol mode‖ ≤ 1 := by
  rw [originalAngularStrengthSymbol,norm_div,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (by positivity : 0 ≤ 1 + |(mode.1 : ℝ)|),
    Real.norm_of_nonneg (Grad.SourceBoundaryTrace.annularFrequency_pos mode).le]
  apply (div_le_one (Grad.SourceBoundaryTrace.annularFrequency_pos mode)).mpr
  change 1 + |(mode.1 : ℝ)| ≤ 1 + |(mode.1 : ℝ)| + |(mode.2 : ℝ)|
  exact le_add_of_nonneg_right (abs_nonneg _)

def originalAngularStrengthReserve (parameters : PhaseParameters) : CellL2 1 →L[ℂ] CellL2 1 :=
  boundedHilbertMultiplier parameters 1 originalAngularStrengthSymbol 1 zero_le_one originalAngularStrengthSymbol_bound

theorem originalAngularStrengthReserve_weighted (parameters : PhaseParameters) (grade : ℕ)
    (field : CellL2 1) (mode : ℤ × ℤ) (value : ComplexEuclidean 1)
    (same : field mode = ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ (grade+1) : ℝ) : ℂ) • value) :
    originalAngularStrengthReserve parameters field mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        (((1 + |(mode.1 : ℝ)| : ℝ) : ℂ) • value) := by
  change originalAngularStrengthSymbol mode • field mode = _
  rw [same,originalAngularStrengthSymbol,smul_smul,smul_smul]
  congr 1
  have nonzero : (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Grad.SourceBoundaryTrace.annularFrequency_pos mode).ne'
  simp only [Complex.ofReal_pow]
  change ((1 + |(mode.1 : ℝ)| : ℝ) : ℂ) / (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ) *
    (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^(grade+1) =
      (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^grade * ((1 + |(mode.1 : ℝ)| : ℝ) : ℂ)
  rw [pow_succ]
  field_simp

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (tuple : OriginalSmoothTuple parameters lower)

def tupleStrengthenedG3Curve (grade : ℕ) (radius : ℝ) : CellL2 1 :=
  originalAngularStrengthReserve parameters
    (tupleConjugatedG3Curve parameters length compact lower positive bounded state tuple (grade+1) radius)

theorem tupleStrengthenedG3Curve_continuous (grade : ℕ) :
    ContinuousOn (tupleStrengthenedG3Curve parameters length compact lower positive bounded state tuple grade) (Icc lower 1) :=
  (originalAngularStrengthReserve parameters).continuous.comp_continuousOn
    (tupleConjugatedG3Curve_continuous parameters length compact lower positive bounded state tuple (grade+1))

theorem tupleStrengthenedG3Curve_coefficient (grade : ℕ) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    tupleStrengthenedG3Curve parameters length compact lower positive bounded state tuple grade radius.val mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        ((Real.exp (radialPhase parameters radius.val mode.2) : ℂ) •
          (((1 + |(mode.1 : ℝ)| : ℝ) : ℂ) • originalTupleG3 parameters length compact lower positive state tuple radius mode)) := by
  rw [tupleStrengthenedG3Curve,originalAngularStrengthReserve_weighted parameters grade _ mode _
    (tupleConjugatedG3Curve_coefficient parameters length compact lower positive bounded state tuple (grade+1) radius mode)]
  exact congrArg (fun value : ComplexEuclidean 1 =>
    ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • value) (smul_comm _ _ _)

theorem tupleConjugatedF1Curve_grade (grade : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    tupleConjugatedF1Curve parameters length compact lower positive bounded state tuple grade radius mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        tupleConjugatedF1Curve parameters length compact lower positive bounded state tuple 0 radius mode := by
  rw [tupleConjugatedF1Curve_coefficient parameters length compact lower positive bounded state tuple grade ⟨radius,inside⟩,
    tupleConjugatedF1Curve_coefficient parameters length compact lower positive bounded state tuple 0 ⟨radius,inside⟩]
  simp only [pow_zero,Complex.ofReal_one,one_smul]

theorem tupleStrengthenedG3Curve_grade (grade : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    tupleStrengthenedG3Curve parameters length compact lower positive bounded state tuple grade radius mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        tupleStrengthenedG3Curve parameters length compact lower positive bounded state tuple 0 radius mode := by
  rw [tupleStrengthenedG3Curve_coefficient parameters length compact lower positive bounded state tuple grade ⟨radius,inside⟩,
    tupleStrengthenedG3Curve_coefficient parameters length compact lower positive bounded state tuple 0 ⟨radius,inside⟩]
  simp only [pow_zero,Complex.ofReal_one,one_smul]

end Grad.AnnularOriginalCoreRealization
