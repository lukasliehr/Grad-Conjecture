import AEN12OriginalBandPrimitiveGain

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.ExceptionalNative
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ActualExceptionalInverse Grad.RawCircularSectors
open Grad.BoundedScalarInverse Grad.FlatSourceProjection
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Frame
variable {L sigma gamma ell : ℝ}

theorem linear_norm_smul_bound {E F : Type*} [AddCommGroup E] [Module ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (linear : E →ₗ[ℂ] F) (scalar : ℂ) (field : E) (coefficient : ℝ) (bounded : ‖scalar‖ ≤ coefficient) :
    ‖linear (scalar • field)‖ ≤ coefficient * ‖linear field‖ := by
  rw [map_smul, norm_smul]
  exact mul_le_mul_of_nonneg_right bounded (norm_nonneg _)

theorem linear_norm_add_bound {E F : Type*} [AddCommGroup E] [Module ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (linear : E →ₗ[ℂ] F) (first second : E) : ‖linear (first + second)‖ ≤ ‖linear first‖ + ‖linear second‖ := by
  rw [map_add]
  exact norm_add_le _ _

theorem linear_norm_sub_bound {E F : Type*} [AddCommGroup E] [Module ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (linear : E →ₗ[ℂ] F) (first second : E) : ‖linear (first - second)‖ ≤ ‖linear first‖ + ‖linear second‖ := by
  rw [map_sub]
  exact norm_sub_le _ _

theorem smoothAxial_band_bound (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (ceiling : ℝ) (field : APSmooth L sigma gamma ell dimension)
    (supported : SmoothCellSupported admissible (InCellBand L ell ceiling) field) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell dimension grade (apSmoothAxial L sigma gamma ell dimension field)‖ ≤
      bandFrequencySize ceiling * ‖apSmoothGrade L sigma gamma ell dimension grade field‖ := by
  apply smoothNorm_of_cellBounds admissible field _ grade grade _ (by exact (zero_le_one.trans (bandFrequencySize_one_le ceiling)))
  intro cell
  have literal := apSmoothAxial_jet admissible field cell
  have normEquality := congrArg (fun jet : ClosedJet dimension => ‖apRowLinear (grade := grade) L sigma gamma ell cell jet‖) literal
  apply normEquality.le.trans
  by_cases band : InCellBand L ell ceiling cell
  · exact linear_norm_smul_bound (apRowLinear (grade := grade) L sigma gamma ell cell) _ _ _
      ((seedScaledFrequency_norm_le L ell cell).trans (band_scaled_frequency L ell ceiling cell band))
  · rw [supported cell band, smul_zero, map_zero, norm_zero, mul_zero]

def ExceptionalSourceBand (admissible : Admissible L sigma gamma ell) (ceiling : ℝ)
    (source : SmoothCapSource L sigma gamma ell) : Prop :=
  SmoothCellSupported admissible (InCellBand L ell ceiling) source.1 ∧
    SmoothCellSupported admissible (InCellBand L ell ceiling) source.2.1 ∧
      SmoothCellSupported admissible (InCellBand L ell ceiling) source.2.2

def exceptionalSourceSize (L sigma gamma ell : ℝ) (grade : ℕ) (source : SmoothCapSource L sigma gamma ell) : ℝ :=
  ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) source.1‖ +
    ‖apSmoothGrade L sigma gamma ell 1 grade source.2.1‖ +
      ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) source.2.2‖

theorem exceptionalSourceSize_nonnegative (grade : ℕ) (source : SmoothCapSource L sigma gamma ell) :
    0 ≤ exceptionalSourceSize L sigma gamma ell grade source := add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)

theorem exceptionalSourceSize_slots (grade : ℕ) (source : SmoothCapSource L sigma gamma ell) :
    ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) source.1‖ ≤ exceptionalSourceSize L sigma gamma ell grade source ∧
    ‖apSmoothGrade L sigma gamma ell 1 grade source.2.1‖ ≤ exceptionalSourceSize L sigma gamma ell grade source ∧
    ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) source.2.2‖ ≤ exceptionalSourceSize L sigma gamma ell grade source := by
  unfold exceptionalSourceSize
  constructor
  · linarith [norm_nonneg (apSmoothGrade L sigma gamma ell 1 grade source.2.1), norm_nonneg (apSmoothGrade L sigma gamma ell 1 (grade + 1) source.2.2)]
  constructor
  · linarith [norm_nonneg (apSmoothGrade L sigma gamma ell 2 (grade + 1) source.1), norm_nonneg (apSmoothGrade L sigma gamma ell 1 (grade + 1) source.2.2)]
  · linarith [norm_nonneg (apSmoothGrade L sigma gamma ell 2 (grade + 1) source.1), norm_nonneg (apSmoothGrade L sigma gamma ell 1 grade source.2.1)]

def exceptionalPsiConstant (L gamma ceiling : ℝ) (grade : ℕ) : ℝ :=
  primitiveBandConstant L gamma ceiling (grade + 1) (regularPrimitiveGainConstant (grade + 1)) * smoothSpinConstant

theorem exceptionalPsiConstant_nonnegative (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (grade : ℕ) :
    0 ≤ exceptionalPsiConstant L gamma ceiling grade :=
  mul_nonneg (primitiveBandConstant_nonnegative admissible ceiling (grade + 1) _ (regularPrimitiveGainConstant_nonnegative _))
    smoothSpinConstant_nonnegative

theorem exceptionalPsi_native (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (grade : ℕ)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) (band : ExceptionalSourceBand admissible ceiling source) :
    ‖apSmoothGrade L sigma gamma ell 1 (grade + 2) (exceptionalPsi admissible sign source)‖ ≤
      exceptionalPsiConstant L gamma ceiling grade * exceptionalSourceSize L sigma gamma ell grade source := by
  have negative : -sign = 1 ∨ -sign = -1 := by rcases signed with rfl | rfl <;> norm_num
  have pure : HasSmoothMode admissible sign (smoothSpin L sigma gamma ell (-sign) source.1) := by
    simpa only [show 2 * sign + -sign = sign by omega] using rawSource_smoothSpin admissible (2 * sign) (-sign) negative source raw
  have regular := regularSmooth_original_gain admissible ceiling (grade + 1) (by omega) sign signed
    (smoothSpin L sigma gamma ell (-sign) source.1) (exceptionalPsi admissible sign source) pure
    (smoothSupport_spin admissible _ (-sign) source.1 band.1) (fun cell =>
      (exceptionalPsi_jet admissible sign source cell).trans
        (congrArg (regularSecondPrimitive sign) (smoothSpin_jet admissible (-sign) source.1 cell)).symm)
  have spin := (smoothSpin_bound (-sign) negative source.1 (grade + 1)).trans
    (mul_le_mul_of_nonneg_left (exceptionalSourceSize_slots grade source).1 smoothSpinConstant_nonnegative)
  exact regular.trans ((mul_le_mul_of_nonneg_left spin
    (primitiveBandConstant_nonnegative admissible ceiling _ _ (regularPrimitiveGainConstant_nonnegative _))).trans_eq
      (mul_assoc _ _ _).symm)

theorem exceptionalTheta_native (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (grade : ℕ)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) (band : ExceptionalSourceBand admissible ceiling source) :
    ‖apSmoothGrade L sigma gamma ell 1 (grade + 2) (exceptionalTheta admissible sign source)‖ ≤
      exceptionalPsiConstant L gamma ceiling grade * exceptionalSourceSize L sigma gamma ell grade source := by
  have scalar := linear_norm_smul_bound (apSmoothGrade L sigma gamma ell 1 (grade + 2))
    (2 * Complex.I * (sign : ℂ))⁻¹ (exceptionalPsi admissible sign source) 1 (signedHalfInverse_norm sign signed)
  exact scalar.trans ((one_mul _).le.trans (exceptionalPsi_native admissible ceiling grade sign signed source raw band))

def exceptionalFixedConstant (L gamma ceiling : ℝ) (grade : ℕ) : ℝ :=
  smoothSignedDerivativeConstant L gamma (grade + 1) * exceptionalPsiConstant L gamma ceiling grade + smoothSpinConstant

theorem exceptionalFixedConstant_nonnegative (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (grade : ℕ) :
    0 ≤ exceptionalFixedConstant L gamma ceiling grade :=
  add_nonneg (mul_nonneg (smoothSignedDerivativeConstant_nonnegative admissible _) (exceptionalPsiConstant_nonnegative admissible _ _))
    smoothSpinConstant_nonnegative

theorem exceptionalFixed_native (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (grade : ℕ)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) (band : ExceptionalSourceBand admissible ceiling source) :
    ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) (exceptionalFixedSpin admissible sign source)‖ ≤
      exceptionalFixedConstant L gamma ceiling grade * exceptionalSourceSize L sigma gamma ell grade source := by
  let project := apSmoothGrade L sigma gamma ell 1 (grade + 1)
  have scalar := linear_norm_smul_bound project (4 * Complex.I * (sign : ℂ))⁻¹
    (smoothSignedDerivative admissible 1 (-sign) (exceptionalPsi admissible sign source) - smoothSpin L sigma gamma ell sign source.1)
    1 (signedQuarterInverse_norm sign signed)
  have difference := linear_norm_sub_bound project
    (smoothSignedDerivative admissible 1 (-sign) (exceptionalPsi admissible sign source)) (smoothSpin L sigma gamma ell sign source.1)
  have derivative := (smoothSignedDerivative_bound admissible (-sign) (by rcases signed with rfl | rfl <;> norm_num)
    (exceptionalPsi admissible sign source) (grade + 1)).trans
      (mul_le_mul_of_nonneg_left (exceptionalPsi_native admissible ceiling grade sign signed source raw band)
        (smoothSignedDerivativeConstant_nonnegative admissible _))
  have spin := (smoothSpin_bound sign signed source.1 (grade + 1)).trans
    (mul_le_mul_of_nonneg_left (exceptionalSourceSize_slots grade source).1 smoothSpinConstant_nonnegative)
  exact scalar.trans ((one_mul _).le.trans (difference.trans ((add_le_add derivative spin).trans_eq (by
    unfold exceptionalFixedConstant
    ring))))

def exceptionalToroidalConstant (L gamma ceiling : ℝ) (grade : ℕ) : ℝ :=
  1 + bandFrequencySize ceiling * apLoweringConstant (grade + 1) * exceptionalPsiConstant L gamma ceiling grade

theorem exceptionalToroidalConstant_nonnegative (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (grade : ℕ) :
    0 ≤ exceptionalToroidalConstant L gamma ceiling grade := add_nonneg zero_le_one
  (mul_nonneg (mul_nonneg (zero_le_one.trans (bandFrequencySize_one_le ceiling)) (apLoweringConstant_nonnegative _))
    (exceptionalPsiConstant_nonnegative admissible _ _))

theorem exceptionalToroidal_native (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (grade : ℕ)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) (band : ExceptionalSourceBand admissible ceiling source) :
    ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) (exceptionalToroidal admissible sign source)‖ ≤
      exceptionalToroidalConstant L gamma ceiling grade * exceptionalSourceSize L sigma gamma ell grade source := by
  let project := apSmoothGrade L sigma gamma ell 1 (grade + 1)
  have scalar := linear_norm_smul_bound project (2 * Complex.I * (sign : ℂ))⁻¹
    (source.2.2 + apSmoothAxial L sigma gamma ell 1 (exceptionalPsi admissible sign source)) 1 (signedHalfInverse_norm sign signed)
  have lower := (smoothOriginal_lower admissible (by omega : grade + 1 ≤ grade + 2) (exceptionalPsi admissible sign source)).trans
    (mul_le_mul_of_nonneg_left (exceptionalPsi_native admissible ceiling grade sign signed source raw band) (apLoweringConstant_nonnegative _))
  have axial := (smoothAxial_band_bound admissible ceiling (exceptionalPsi admissible sign source)
    (exceptionalPsi_support admissible _ sign source band.1) (grade + 1)).trans
      (mul_le_mul_of_nonneg_left lower (zero_le_one.trans (bandFrequencySize_one_le ceiling)))
  exact scalar.trans ((one_mul _).le.trans ((linear_norm_add_bound project _ _).trans
    ((add_le_add (exceptionalSourceSize_slots grade source).2.2 axial).trans_eq (by unfold exceptionalToroidalConstant; ring))))

end Grad.ExceptionalNative
