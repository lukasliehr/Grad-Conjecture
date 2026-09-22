import AAZJ3UniformPhysicalJetSections
import FT3Reconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularJointRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace









open Grad.AnnularRadialJets Grad.AnnularRegularity



/-- The exact two-dimensional summability reserve in AG12. -/
theorem annularLattice_inverse_four_summable :
    Summable (fun mode : ℤ × ℤ =>
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2) ^ 4)⁻¹) := by
  have productSummable := Grad.FourierGrade.integerSquareDecay_summable.mul_of_nonneg
    Grad.FourierGrade.integerSquareDecay_summable Grad.FourierGrade.integerSquareDecay_nonneg
    Grad.FourierGrade.integerSquareDecay_nonneg
  apply Summable.of_nonneg_of_le (fun mode => by positivity) _ productSummable
  intro mode
  let frequency := Grad.AnnularVariational.annularFrequency mode.1 mode.2
  have frequencyPositive : 0 < frequency := by
    dsimp [frequency, Grad.AnnularVariational.annularFrequency]
    positivity
  have first : 1 + (mode.1 : ℝ) ^ 2 ≤ frequency ^ 2 := by
    dsimp [frequency, Grad.AnnularVariational.annularFrequency]
    nlinarith [abs_nonneg (mode.1 : ℝ), abs_nonneg (mode.2 : ℝ), sq_abs (mode.1 : ℝ)]
  have second : 1 + (mode.2 : ℝ) ^ 2 ≤ frequency ^ 2 := by
    dsimp [frequency, Grad.AnnularVariational.annularFrequency]
    nlinarith [abs_nonneg (mode.1 : ℝ), abs_nonneg (mode.2 : ℝ), sq_abs (mode.2 : ℝ)]
  have product : (1 + (mode.1 : ℝ) ^ 2) * (1 + (mode.2 : ℝ) ^ 2) ≤ frequency ^ 4 := by
    calc
      _ ≤ frequency ^ 2 * frequency ^ 2 :=
        mul_le_mul first second (by positivity) (sq_nonneg _)
      _ = _ := by ring
  have inverse := (inv_le_inv₀ (pow_pos frequencyPositive 4) (by positivity :
    0 < (1 + (mode.1 : ℝ) ^ 2) * (1 + (mode.2 : ℝ) ^ 2))).mpr product
  simpa only [mul_inv_rev, mul_comm, Grad.FourierGrade.integerSquareDecay] using inverse

theorem annularHigh_inverse_four_summable :
    Summable (fun mode : HighAnnularMode =>
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ 4)⁻¹) :=
  annularLattice_inverse_four_summable.comp_injective Subtype.val_injective

/-- Cauchy--Schwarz uses exactly two extra inserted tangential grades. -/
theorem annularRaw_twoExtra_summable (lower : ℝ) (grade : ℕ) (field : AnnularRawFamily lower)
    (member : HasAnnularRawGrade lower (grade + 2) field) :
    Summable (fun mode : HighAnnularMode =>
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ grade * ‖field mode‖) := by
  let weighted : HighAnnularMode → ℝ := fun mode =>
    (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ (grade + 2) * ‖field mode‖
  let decay : HighAnnularMode → ℝ := fun mode =>
    ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ 2)⁻¹
  have normSummable := member.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
  have weightedSquare : Summable (fun mode => weighted mode ^ (2 : ℝ)) := by
    apply normSummable.congr
    intro mode
    change ‖(annularGradeWeight 0 0 (grade + 2) mode : ℂ) • field mode‖ ^ (2 : ENNReal).toReal = _
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (annularGradeWeight_pos 0 0 (grade + 2) mode).le,
      annularGradeWeight_literal]
    simp only [pow_zero, mul_one, ENNReal.toReal_ofNat]
    rfl
  have decaySquare : Summable (fun mode => decay mode ^ (2 : ℝ)) := by
    apply annularHigh_inverse_four_summable.congr
    intro mode
    dsimp [decay]
    simp only [Real.rpow_two, ← inv_pow, ← pow_mul]
  have product := Real.summable_mul_of_Lp_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 by rw [Real.holderConjugate_iff]; norm_num)
    (fun mode => show 0 ≤ weighted mode from mul_nonneg
      (pow_nonneg (zero_le_one.trans (annularRawFrequency_one_le mode)) _) (norm_nonneg _))
    (fun mode => show 0 ≤ decay mode by dsimp [decay]; positivity)
    weightedSquare decaySquare
  apply product.congr
  intro mode
  dsimp [weighted, decay]
  rw [pow_add]
  have nonzero : (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (lt_of_lt_of_le zero_lt_one (annularRawFrequency_one_le mode)).ne'
  calc
    _ = ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ grade * ‖field mode‖) *
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ 2 *
        ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ 2)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ nonzero, mul_one]

/-- A summable majorant for every radial and tangential derivative on the
entire closed collar, derived from the same actual physical jets. -/
theorem annularPhysicalJetSection_weighted_summable (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (jet : ℕ → AnnularRawFamily lower)
    (weak : ∀ order, AnnularPhysicalWeakDerivative parameters lower positive (jet order) (jet (order + 1)))
    (order grade : ℕ) (first : HasAnnularRawGrade lower (grade + 2) (jet order))
    (second : HasAnnularRawGrade lower (grade + 2) (jet (order + 1))) :
    Summable (fun mode : HighAnnularMode =>
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ grade *
        ‖annularPhysicalJetSection parameters lower positive bounded jet weak order mode‖) := by
  have source := ((annularRaw_twoExtra_summable lower grade (jet order) first).add
    (annularRaw_twoExtra_summable lower grade (jet (order + 1)) second)).mul_left (sourceEndpointConstant lower)
  apply Summable.of_nonneg_of_le (fun mode => mul_nonneg (pow_nonneg (le_trans zero_le_one (annularRawFrequency_one_le mode)) _) (norm_nonneg _)) _ source
  intro mode
  have bound := mul_le_mul_of_nonneg_left
    (annularPhysicalJetSection_norm_le parameters lower positive bounded jet weak order mode)
    (pow_nonneg (le_trans zero_le_one (annularRawFrequency_one_le mode)) grade)
  exact bound.trans_eq (by ring)

end Grad.AnnularJointRegularity
