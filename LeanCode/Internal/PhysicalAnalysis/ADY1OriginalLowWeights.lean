import AAQ17ActualWeightedFluxGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace
open Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Every original low angular mode, with every axial cell. -/
abbrev LowAnnularMode := {mode : ℤ × ℤ // |mode.1| = 1 ∨ |mode.1| = 2}
/-- The two entries are (a_m mu xi, x), in that order. -/
abbrev LowAnnularIndex := Fin 2 × LowAnnularMode

/-- BE2's exact low frequency. In particular this is positive at n=0. -/
def lowMu (length radius : ℝ) (cell : ℤ) : ℝ :=
  Real.sqrt (((cell : ℝ) / length) ^ 2 + radius⁻¹ ^ 2)

theorem lowMu_nonneg (length radius : ℝ) (cell : ℤ) : 0 ≤ lowMu length radius cell :=
  Real.sqrt_nonneg _

theorem lowMu_sq (length radius : ℝ) (cell : ℤ) :
    lowMu length radius cell ^ 2 = ((cell : ℝ) / length) ^ 2 + radius⁻¹ ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem lowMu_radial (length radius : ℝ) (cell : ℤ) (positive : 0 < radius) :
    radius⁻¹ ≤ lowMu length radius cell := by
  calc
    _ = Real.sqrt (radius⁻¹ ^ 2) := by rw [Real.sqrt_sq (inv_nonneg.mpr positive.le)]
    _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))

theorem lowMu_pos (length radius : ℝ) (cell : ℤ) (positive : 0 < radius) :
    0 < lowMu length radius cell := (inv_pos.mpr positive).trans_le (lowMu_radial length radius cell positive)

/-- Positive extension agrees with the physical radius throughout the collar. -/
def lowPowerCurve (lower power : ℝ) (positive : 0 < lower) : C(ℝ, ℝ) :=
  ⟨fun radius => (max lower radius) ^ power,
    (continuous_const.max continuous_id).rpow_const
      (fun radius => Or.inl (positive.trans_le (le_max_left lower radius)).ne')⟩

theorem lowPowerCurve_pos (lower power : ℝ) (positive : 0 < lower) (radius : ℝ) :
    0 < lowPowerCurve lower power positive radius :=
  Real.rpow_pos_of_pos (positive.trans_le (le_max_left _ _)) _

def lowMuCurve (lower length : ℝ) (positive : 0 < lower) (cell : ℤ) : C(ℝ, ℝ) :=
  ⟨fun radius => lowMu length (max lower radius) cell,
    Real.continuous_sqrt.comp (continuous_const.add
      (((continuous_const.max continuous_id).inv₀
        (fun radius => (positive.trans_le (le_max_left lower radius)).ne')).pow 2))⟩

theorem lowMuCurve_pos (lower length : ℝ) (positive : 0 < lower) (cell : ℤ) (radius : ℝ) :
    0 < lowMuCurve lower length positive cell radius :=
  lowMu_pos length (max lower radius) cell (positive.trans_le (le_max_left _ _))

/-- Square root of the literal BE18 density, with no additional high-sector tilt. -/
def lowStorageWeight (lower : ℝ) (positive : 0 < lower) : C(ℝ, ℝ) :=
  lowPowerCurve lower (-(7 / 4 : ℝ)) positive

def lowStorageInverse (lower : ℝ) (positive : 0 < lower) : C(ℝ, ℝ) :=
  lowPowerCurve lower (7 / 4 : ℝ) positive

theorem lowStorage_inverse (lower : ℝ) (positive : 0 < lower) (radius : ℝ) :
    lowStorageWeight lower positive radius * lowStorageInverse lower positive radius = 1 := by
  change (max lower radius) ^ (-(7 / 4 : ℝ)) * (max lower radius) ^ (7 / 4 : ℝ) = 1
  rw [← Real.rpow_add (positive.trans_le (le_max_left _ _)), neg_add_cancel, Real.rpow_zero]

theorem lowStorageWeight_sq (lower : ℝ) (positive : 0 < lower)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    lowStorageWeight lower positive radius ^ 2 = radius ^ (-(7 / 2 : ℝ)) := by
  change ((max lower radius) ^ (-(7 / 4 : ℝ))) ^ 2 = _
  rw [max_eq_right inside.1, pow_two, ← Real.rpow_add (positive.trans_le inside.1)]
  norm_num

/-- Invertibility of an actual radial multiplier, proved on L2 classes. -/
theorem collarScalar_injective_of_pos (lower : ℝ) (coefficient : C(ℝ, ℝ))
    (positive : ∀ radius, 0 < coefficient radius) :
    Function.Injective (collarScalar 1 lower coefficient) := by
  intro first second same
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower coefficient first,
    collarScalar_ae 1 lower coefficient second] with radius firstLaw secondLaw
  have pointwise := congrArg (fun field : CollarL2 (ComplexEuclidean 1) lower => field radius) same
  rw [firstLaw, secondLaw] at pointwise
  exact (smul_right_injective (ComplexEuclidean 1) (positive radius).ne') pointwise

theorem lowStorage_decode_encode (lower : ℝ) (positive : 0 < lower)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower (lowStorageInverse lower positive)
      (collarScalar 1 lower (lowStorageWeight lower positive) field) = field := by
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower (lowStorageInverse lower positive)
      (collarScalar 1 lower (lowStorageWeight lower positive) field),
    collarScalar_ae 1 lower (lowStorageWeight lower positive) field] with radius outer inner
  rw [outer, inner, smul_smul, mul_comm, lowStorage_inverse, one_smul]

theorem lowStorage_encode_decode (lower : ℝ) (positive : 0 < lower)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower (lowStorageWeight lower positive)
      (collarScalar 1 lower (lowStorageInverse lower positive) field) = field := by
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower (lowStorageWeight lower positive)
      (collarScalar 1 lower (lowStorageInverse lower positive) field),
    collarScalar_ae 1 lower (lowStorageInverse lower positive) field] with radius outer inner
  rw [outer, inner, smul_smul, lowStorage_inverse, one_smul]

end Grad.AnnularLowEnergy
