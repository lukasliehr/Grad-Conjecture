import AKO1ActualIncomingSquareIntegrals

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped ENNReal BigOperators
namespace Grad.AnnularIncomingIntegrability
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.ClosedJets Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularLowEnergy
open Grad.AnnularSourceGraph Grad.CircularHighRegularity

variable (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)

/-- Genuine low H1 representative, never evaluation of an L2 class at a trace. -/
def lowIncomingRepresentative (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) : C(ℝ, ComplexEuclidean 1) :=
  radialSectionExtension 1 lower bounded.le (lowEnergySection lower length positive bounded field index)

theorem lowIncomingRepresentative_stored (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), field.val 0 index radius =
      lowStorageWeight lower positive radius • lowIncomingRepresentative lower length positive bounded field index radius := by
  have sectionLaw := radialSectionL2_ae 1 lower positive bounded.le (lowEnergySection lower length positive bounded field index)
  rw [lowEnergySection_bulk] at sectionLaw
  have encoded := lowStorage_encode_decode lower positive (field.val 0 index)
  filter_upwards [sectionLaw,collarScalar_ae 1 lower (lowStorageWeight lower positive)
    (lowEnergyValue lower positive index field.val)] with radius sectionLaw encoding
  change collarScalar 1 lower (lowStorageWeight lower positive)
    (collarScalar 1 lower (lowStorageInverse lower positive) (field.val 0 index)) radius = _ at encoding
  rw [encoded] at encoding
  exact encoding.trans (congrArg (fun value : ComplexEuclidean 1 => lowStorageWeight lower positive radius • value) sectionLaw.symm)

/-- Literal squared incoming BE norm at a moving radius, through the SAME
canonical representatives and original mu, with every cell retained. -/
def lowIncomingSquare (field : lowEnergyGraph lower length positive) (radius : ℝ) : ℝ≥0∞ :=
  ∑' index : LowAnnularIndex, ENNReal.ofReal (radius ^ (-(7 / 2 : ℝ)) * (lowMu length radius index.2.val.2)⁻¹ *
    ‖lowIncomingRepresentative lower length positive bounded field index radius‖ ^ 2)

private theorem lowCoefficientLogBound (radius mu square : ℝ) (positive : 0 < radius)
    (inverseBound : mu ≤ radius) (squareNonnegative : 0 ≤ square) :
    radius⁻¹ * (radius ^ (-(7 / 2 : ℝ)) * mu * square) ≤ radius ^ (-(7 / 2 : ℝ)) * square := by
  have scaled := mul_le_mul_of_nonneg_left inverseBound (inv_nonneg.mpr positive.le)
  rw [inv_mul_cancel₀ positive.ne'] at scaled
  have result := mul_le_mul_of_nonneg_right scaled (mul_nonneg (Real.rpow_nonneg positive.le (-(7 / 2 : ℝ))) squareNonnegative)
  nlinarith only [result]

/-- Radius-independent logarithmic incoming bound by the SAME stored value
energy. Tonelli handles the full countable nonnegative coordinate sum first. -/
theorem lowIncomingSquare_log_bound (field : lowEnergyGraph lower length positive) :
    (∫⁻ radius, ENNReal.ofReal radius⁻¹ * lowIncomingSquare lower length positive bounded field radius
      ∂volume.restrict (Icc lower 1)) ≤ ENNReal.ofReal (‖field.val 0‖ ^ 2) := by
  rw [← lp_lintegral_tsum_sq lower (field.val 0)]
  apply lintegral_mono_ae
  filter_upwards [ae_all_iff.mpr (lowIncomingRepresentative_stored lower length positive bounded field),
    ae_restrict_mem measurableSet_Icc] with radius stored inside
  have radiusPositive := positive.trans_le inside.1
  change ENNReal.ofReal radius⁻¹ * (∑' index : LowAnnularIndex, ENNReal.ofReal _) ≤ _
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro index
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr radiusPositive.le)]
  apply ENNReal.ofReal_le_ofReal
  have energy := congrArg (fun value : ComplexEuclidean 1 => ‖value‖ ^ 2) (stored index)
  rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,lowStorageWeight_sq lower positive radius inside] at energy
  exact (lowCoefficientLogBound radius (lowMu length radius index.2.val.2)⁻¹ _ radiusPositive
    (lowMu_inverse_le_radius length radius index.2.val.2 radiusPositive)
    (sq_nonneg _)).trans_eq energy.symm

end Grad.AnnularIncomingIntegrability
