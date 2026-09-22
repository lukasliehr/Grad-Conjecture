import AEN11PrimitiveLinearityAndSupport
import ANB9OriginalWeightedRows

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.ExceptionalNative
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ActualExceptionalInverse Grad.CircularHighWeak
open Grad.BoundedScalarInverse
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.RadialLedger
variable {L sigma gamma ell : ℝ}

def primitiveBandConstant (L gamma ceiling : ℝ) (grade : ℕ) (gain : ℝ) : ℝ :=
  originalBandRowConstant L gamma ceiling (grade + 1) * gain * bandMultiplicationConstant L gamma ceiling grade

theorem primitiveBandConstant_nonnegative (admissible : Admissible L sigma gamma ell)
    (ceiling : ℝ) (grade : ℕ) (gain : ℝ) (positiveGain : 0 ≤ gain) : 0 ≤ primitiveBandConstant L gamma ceiling grade gain :=
  mul_nonneg (mul_nonneg (originalBandRowConstant_nonnegative L gamma ceiling (admissible_gamma_nonnegative admissible) _) positiveGain)
    (bandMultiplicationConstant_nonnegative L gamma ceiling (admissible_gamma_nonnegative admissible) grade)

theorem regularPrimitive_original_row (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (cell : ℤ)
    (band : InCellBand L ell ceiling cell) (grade : ℕ) (large : 1 ≤ grade)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (forcing : ClosedJet 1) (pure : angularClosedJet sign forcing = forcing) :
    ‖apRowLinear (grade := grade + 1) L sigma gamma ell cell (regularSecondPrimitive sign forcing)‖ ≤
      primitiveBandConstant L gamma ceiling grade (regularPrimitiveGainConstant grade) *
        ‖apRowLinear (grade := grade) L sigma gamma ell cell forcing‖ := by
  have flatPure : angularClosedJet sign (flatWeightedJet sigma cell forcing) = flatWeightedJet sigma cell forcing := by
    rw [flatWeightedJet, angularClosedJet_smul, pure]
  have flat : flatWeightedJet sigma cell (regularSecondPrimitive sign forcing) =
      regularSecondPrimitive sign (flatWeightedJet sigma cell forcing) := (regularPrimitive_smul sign _ forcing).symm
  have output := originalBandRow_le_flat admissible ceiling cell band (grade + 1) (regularSecondPrimitive sign forcing)
  rw [flat] at output
  have native := (regularPrimitive_sharp grade large sign signed _ flatPure).trans
    (mul_le_mul_of_nonneg_left (flat_le_originalBandRow admissible ceiling cell band grade forcing)
      (regularPrimitiveGainConstant_nonnegative grade))
  exact output.trans ((mul_le_mul_of_nonneg_left native
    (originalBandRowConstant_nonnegative L gamma ceiling (admissible_gamma_nonnegative admissible) _)).trans_eq (by
      unfold primitiveBandConstant
      ring))

theorem pinnedPrimitive_original_row (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (cell : ℤ)
    (band : InCellBand L ell ceiling cell) (grade : ℕ) (large : 3 ≤ grade)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (forcing : ClosedJet 1) (pure : angularClosedJet (2 * sign) forcing = forcing) :
    ‖apRowLinear (grade := grade + 1) L sigma gamma ell cell (pinnedSpinPrimitive sign forcing)‖ ≤
      primitiveBandConstant L gamma ceiling grade (pinnedPrimitiveGainConstant grade) *
        ‖apRowLinear (grade := grade) L sigma gamma ell cell forcing‖ := by
  have flatPure : angularClosedJet (2 * sign) (flatWeightedJet sigma cell forcing) = flatWeightedJet sigma cell forcing := by
    rw [flatWeightedJet, angularClosedJet_smul, pure]
  have flat : flatWeightedJet sigma cell (pinnedSpinPrimitive sign forcing) =
      pinnedSpinPrimitive sign (flatWeightedJet sigma cell forcing) := (pinnedPrimitive_smul sign _ forcing).symm
  have output := originalBandRow_le_flat admissible ceiling cell band (grade + 1) (pinnedSpinPrimitive sign forcing)
  rw [flat] at output
  have native := (pinnedPrimitive_sharp grade large sign signed _ flatPure).trans
    (mul_le_mul_of_nonneg_left (flat_le_originalBandRow admissible ceiling cell band grade forcing)
      (pinnedPrimitiveGainConstant_nonnegative grade))
  exact output.trans ((mul_le_mul_of_nonneg_left native
    (originalBandRowConstant_nonnegative L gamma ceiling (admissible_gamma_nonnegative admissible) _)).trans_eq (by
      unfold primitiveBandConstant
      ring))

theorem regularSmooth_original_gain (admissible : Admissible L sigma gamma ell) (ceiling : ℝ)
    (grade : ℕ) (large : 1 ≤ grade) (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (forcing field : APSmooth L sigma gamma ell 1) (pure : HasSmoothMode admissible sign forcing)
    (supported : SmoothCellSupported admissible (InCellBand L ell ceiling) forcing)
    (literal : ∀ cell, apSmoothJet admissible 1 cell field = regularSecondPrimitive sign (apSmoothJet admissible 1 cell forcing)) :
    ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) field‖ ≤
      primitiveBandConstant L gamma ceiling grade (regularPrimitiveGainConstant grade) *
        ‖apSmoothGrade L sigma gamma ell 1 grade forcing‖ := by
  apply smoothNorm_of_cellBounds admissible forcing field grade (grade + 1) _
    (primitiveBandConstant_nonnegative admissible ceiling grade _ (regularPrimitiveGainConstant_nonnegative grade))
  intro cell
  rw [literal]
  by_cases band : InCellBand L ell ceiling cell
  · exact regularPrimitive_original_row admissible ceiling cell band grade large sign signed _ (pure cell)
  · rw [supported cell band, regularPrimitive_zero, map_zero, norm_zero, map_zero, norm_zero, mul_zero]

theorem pinnedSmooth_original_gain (admissible : Admissible L sigma gamma ell) (ceiling : ℝ)
    (grade : ℕ) (large : 3 ≤ grade) (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (forcing : APSmooth L sigma gamma ell 1) (pure : HasSmoothMode admissible (2 * sign) forcing)
    (supported : SmoothCellSupported admissible (InCellBand L ell ceiling) forcing) :
    ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) (smoothPinnedPrimitive admissible 1 sign forcing)‖ ≤
      primitiveBandConstant L gamma ceiling grade (pinnedPrimitiveGainConstant grade) *
        ‖apSmoothGrade L sigma gamma ell 1 grade forcing‖ := by
  apply smoothNorm_of_cellBounds admissible forcing _ grade (grade + 1) _
    (primitiveBandConstant_nonnegative admissible ceiling grade _ (pinnedPrimitiveGainConstant_nonnegative grade))
  intro cell
  have literal := smoothPinnedPrimitive_jet admissible sign forcing cell
  have normEquality := congrArg (fun jet : ClosedJet 1 => ‖apRowLinear (grade := grade + 1) L sigma gamma ell cell jet‖) literal
  apply normEquality.le.trans
  by_cases band : InCellBand L ell ceiling cell
  · exact pinnedPrimitive_original_row admissible ceiling cell band grade large sign signed _ (pure cell)
  · rw [supported cell band, pinnedPrimitive_zero, map_zero, norm_zero, map_zero, norm_zero, mul_zero]

end Grad.ExceptionalNative
