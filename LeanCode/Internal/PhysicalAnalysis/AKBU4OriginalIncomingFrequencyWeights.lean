import AKBU2SameOriginalPhysicalGraphRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.OriginalPhysicalKernelUniqueness
open Grad.CartesianState Grad.AnnularVariational Grad.AnnularLowEnergy Grad.AnnularIncomingIntegrability

/-- The original cell weight controls the literal axial frequency. -/
theorem originalCell_abs_le (cell : ℤ) : |(cell:ℝ)|≤cellFrequency cell := by
  rw [cellFrequency_formula,←Real.sqrt_sq_eq_abs (cell:ℝ)]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_left zero_le_one)

/-- The exact BF high square-root frequency is paid by the original lambda
weight and the SAME angular derivative; no width or A4 loss. -/
theorem originalHighFrequency_payment (mode : ℤ×ℤ) :
    Real.sqrt (Grad.AnnularVariational.annularFrequency mode.1 mode.2)/cellFrequency mode.2≤2*(1+|(mode.1:ℝ)|) := by
  apply (div_le_iff₀ (cellFrequency_pos _)).mpr
  have root : Real.sqrt (Grad.AnnularVariational.annularFrequency mode.1 mode.2)≤Grad.AnnularVariational.annularFrequency mode.1 mode.2 := by
    have one := annularFrequency_one_le mode.1 mode.2
    have square := Real.sq_sqrt (zero_le_one.trans one)
    nlinarith [Real.sqrt_nonneg (Grad.AnnularVariational.annularFrequency mode.1 mode.2)]
  have one := cellFrequency_one_le mode.2
  have axial := originalCell_abs_le mode.2
  have product := mul_nonneg (sub_nonneg.mpr one) (abs_nonneg (mode.1:ℝ))
  unfold Grad.AnnularVariational.annularFrequency at root ⊢
  nlinarith [abs_nonneg (mode.1:ℝ)]

/-- The exact BE low frequency has its elementary original inverse-length
bound, uniformly at every positive collar radius. -/
theorem originalLowMu_upper (length radius : ℝ) (lengthPositive : 0<length) (positive : 0<radius) (cell : ℤ) :
    lowMu length radius cell≤|(cell:ℝ)|/length+radius⁻¹ := by
  have root := lowMu_sq length radius cell
  have left := lowMu_nonneg length radius cell
  have right : 0≤|(cell:ℝ)|/length+radius⁻¹ := by positivity
  have cross : 0≤(|(cell:ℝ)|/length)*radius⁻¹ := by positivity
  have square : (|(cell:ℝ)|/length)^2=((cell:ℝ)/length)^2 := by rw [div_pow,div_pow,sq_abs]
  nlinarith

/-- The genuine low inverse square-root weight gains exactly sqrt(r). -/
theorem originalLowMu_inverseSqrt (length radius : ℝ) (positive : 0<radius) (cell : ℤ) :
    (Real.sqrt (lowMu length radius cell))⁻¹≤Real.sqrt radius := by
  have mu := lowMu_pos length radius cell positive
  have inverse := lowMu_inverse_le_radius length radius cell positive
  have root := Real.sqrt_nonneg (lowMu length radius cell)
  have radiusRoot := Real.sqrt_nonneg radius
  have first : ((Real.sqrt (lowMu length radius cell))⁻¹)^2=(lowMu length radius cell)⁻¹ := by
    rw [inv_pow,Real.sq_sqrt mu.le]
  have second := Real.sq_sqrt positive.le
  have inverseRoot : 0≤(Real.sqrt (lowMu length radius cell))⁻¹ := inv_nonneg.mpr root
  nlinarith

end Grad.OriginalPhysicalKernelUniqueness
