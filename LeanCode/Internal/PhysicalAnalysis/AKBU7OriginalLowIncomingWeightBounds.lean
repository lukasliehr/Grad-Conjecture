import AKBU4OriginalIncomingFrequencyWeights

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.OriginalPhysicalKernelUniqueness
open Grad.CartesianState Grad.AnnularLowEnergy Grad.AnnularCurrentLow

/-- The exact sqrt(mu)/lambda factor is bounded at original width, with
only the fixed original length entering the constant. -/
theorem originalLowMu_sqrt_payment (length radius : ℝ) (lengthPositive : 0<length)
    (positive : 0<radius) (bounded : radius≤1) (cell : ℤ) :
    Real.sqrt (lowMu length radius cell)/cellFrequency cell≤(1+length⁻¹)*radius^(-(1/2:ℝ)) := by
  let C := 1+length⁻¹
  have COne : 1≤C := by dsimp [C]; linarith [inv_nonneg.mpr lengthPositive.le]
  have kOne := cellFrequency_one_le cell
  have kPos := cellFrequency_pos cell
  have axial := originalCell_abs_le cell
  have mu := originalLowMu_upper length radius lengthPositive positive cell
  have paid : lowMu length radius cell*radius≤C*cellFrequency cell := by
    calc
      _ ≤ (|(cell:ℝ)|/length+radius⁻¹)*radius := mul_le_mul_of_nonneg_right mu positive.le
      _ = (|(cell:ℝ)|/length)*radius+1 := by rw [add_mul,inv_mul_cancel₀ positive.ne']
      _ ≤ |(cell:ℝ)|/length+1 := by
        have bound := mul_le_of_le_one_right (div_nonneg (abs_nonneg (cell:ℝ)) lengthPositive.le) bounded
        linarith only [bound]
      _ ≤ C*cellFrequency cell := by
        dsimp only [C]
        have scaled := mul_le_mul_of_nonneg_right axial (inv_nonneg.mpr lengthPositive.le)
        rw [div_eq_mul_inv]
        nlinarith only [scaled,kOne]
  have productOne : 1≤C*cellFrequency cell := one_le_mul_of_one_le_of_one_le COne kOne
  have rootSquare : (Real.sqrt (lowMu length radius cell)*Real.sqrt radius)^2=lowMu length radius cell*radius := by
    rw [mul_pow,Real.sq_sqrt (lowMu_nonneg _ _ _),Real.sq_sqrt positive.le]
  have product : Real.sqrt (lowMu length radius cell)*Real.sqrt radius≤C*cellFrequency cell := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg (lowMu length radius cell)) (Real.sqrt_nonneg radius)]
  have squareRoot : 0<Real.sqrt radius := Real.sqrt_pos.mpr positive
  calc
    _ = (Real.sqrt (lowMu length radius cell)*Real.sqrt radius)/(cellFrequency cell*Real.sqrt radius) := by field_simp
    _ ≤ (C*cellFrequency cell)/(cellFrequency cell*Real.sqrt radius) := div_le_div_of_nonneg_right product (mul_nonneg kPos.le squareRoot.le)
    _ = C*(Real.sqrt radius)⁻¹ := by field_simp
    _ = _ := by rw [Real.sqrt_eq_rpow,Real.rpow_neg positive.le]

/-- The exact low xi coefficient has the r^-9/4 weight needed for the
accepted original Xi r^(5/2) estimate. -/
theorem originalLowXi_weight_bound (length gamma radius : ℝ) (lengthPositive : 0<length)
    (positive : 0<radius) (bounded : radius≤1) (mode : LowAnnularMode) :
    lowAmplitude length gamma mode*radius^(-(7/4:ℝ))*Real.sqrt (lowMu length radius mode.val.2)/cellFrequency mode.val.2≤
      ((lowBalanceConstant length gamma+2)*(1+length⁻¹))*radius^(-(9/4:ℝ)) := by
  have amplitude := lowAmplitude_upper length gamma mode
  have frequency := originalLowMu_sqrt_payment length radius lengthPositive positive bounded mode.val.2
  have amplitudeNonnegative := (lowAmplitude_pos length gamma mode).le
  have balanceNonnegative : 0≤lowBalanceConstant length gamma+2 := by unfold lowBalanceConstant; positivity
  calc
    _ = lowAmplitude length gamma mode*radius^(-(7/4:ℝ))*(Real.sqrt (lowMu length radius mode.val.2)/cellFrequency mode.val.2) := by ring
    _ ≤ (lowBalanceConstant length gamma+2)*radius^(-(7/4:ℝ))*((1+length⁻¹)*radius^(-(1/2:ℝ))) :=
      mul_le_mul (mul_le_mul_of_nonneg_right amplitude (Real.rpow_nonneg positive.le _)) frequency (div_nonneg (Real.sqrt_nonneg _) (cellFrequency_pos _).le) (mul_nonneg balanceNonnegative (Real.rpow_nonneg positive.le _))
    _ = _ := by
      have powers : radius^(-(7/4:ℝ))*radius^(-(1/2:ℝ))=radius^(-(9/4:ℝ)) := by rw [←Real.rpow_add positive]; norm_num
      calc
        _ = ((lowBalanceConstant length gamma+2)*(1+length⁻¹))*(radius^(-(7/4:ℝ))*radius^(-(1/2:ℝ))) := by ring
        _ = _ := by rw [powers]

/-- The exact low x coefficient has the r^-5/4 weight needed for its
accepted original r^(3/2) estimate. -/
theorem originalLowX_weight_bound (length radius : ℝ) (positive : 0<radius) (cell : ℤ) :
    radius^(-(7/4:ℝ))*(Real.sqrt (lowMu length radius cell))⁻¹/cellFrequency cell≤radius^(-(5/4:ℝ)) := by
  have frequency := originalLowMu_inverseSqrt length radius positive cell
  calc
    _ ≤ radius^(-(7/4:ℝ))*(Real.sqrt (lowMu length radius cell))⁻¹ := div_le_self (by positivity) (cellFrequency_one_le cell)
    _ ≤ radius^(-(7/4:ℝ))*Real.sqrt radius := mul_le_mul_of_nonneg_left frequency (Real.rpow_nonneg positive.le _)
    _ = _ := by rw [Real.sqrt_eq_rpow,←Real.rpow_add positive]; norm_num

end Grad.OriginalPhysicalKernelUniqueness
