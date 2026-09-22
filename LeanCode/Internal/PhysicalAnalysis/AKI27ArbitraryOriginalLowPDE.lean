import AKI26OriginalLowFullRowConverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularFullGraph
open Grad.AnnularCurrentLow Grad.AnnularCurrentSource Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.BoundaryKernelAction
open Grad.AnnularLowEnergy Grad.AnnularLowClassical Grad.AnnularSmoothCore Grad.AnnularKnownLow

private theorem lowRawFlux_formula (length radius : ℝ) (nonzero : radius ≠ 0) (mode : ℤ × ℤ)
    (x c v g : ComplexEuclidean 1) :
    (-radius⁻¹) • x + (-Complex.I) • (((mode.2 : ℝ) / length) • c) +
      (-Complex.I) • (((mode.1 : ℝ) * radius⁻¹) • (v - radius • g)) =
      (-((radius : ℂ)⁻¹)) • x - (length : ℂ)⁻¹ • (frequencyNumerator (some true) mode • c) -
        (radius : ℂ)⁻¹ • (frequencyNumerator (some false) mode • v) + frequencyNumerator (some false) mode • g := by
  have radiusC : (radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  ext slot
  simp only [frequencyNumerator, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  have cast (t : ℝ) : (RCLike.ofReal t : ℂ) = (t : ℂ) := rfl
  simp only [cast]
  push_cast
  simp only [div_eq_mul_inv]
  field_simp [radiusC]
  ring

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0) (candidate : OriginalCoupledSpace lower length positive)
    (tuple : OriginalSmoothTuple parameters lower)
    (represented : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state tuple
      (originalFiveBlockObservation parameters lower length positive (data,candidate)))

private abbrev lowCandidate := originalCoupledEquivalence parameters lower length positive bounded.le lengthPositive candidate
private abbrev lowDatum := originalToStrong parameters lower length positive bounded.le lengthPositive 0 0 data
private abbrev lowInput := fullStrongSevenInput parameters length lower lengthPositive positive bounded.le
  (lowDatum parameters length lower positive bounded lengthPositive data)
  (lowCandidate parameters length lower positive bounded lengthPositive candidate)
private abbrev lowRow (index : Fin 3) := lowPhysicalRowAction parameters length compact lower positive bounded.le state index
  (lowInput parameters length lower positive bounded lengthPositive data candidate)
private abbrev lowKnown := strongKnownBulk parameters lower positive bounded.le
  (lowDatum parameters length lower positive bounded lengthPositive data)
private abbrev g := (strongToLow parameters lower positive bounded.le 0 0
  (lowDatum parameters length lower positive bounded lengthPositive data)).ofLp.1.ofLp.2

include represented

/-- The actual arbitrary tuple derivative is the full original low raw RHS. -/
theorem OriginalTupleObservation.lowSlope_actual (index : LowAnnularIndex) :
    originalTupleLowSlope parameters lower bounded tuple index =ᵐ[volume.restrict (Icc lower 1)]
      lowPhysicalRawSlope parameters lower length positive bounded
        (lowCandidate parameters length lower positive bounded lengthPositive candidate).ofLp.2
        (lowRow parameters length compact lower positive bounded lengthPositive state data candidate 0 +
          highSourceF lower (lowKnown parameters length lower positive bounded lengthPositive data))
        (lowRow parameters length compact lower positive bounded lengthPositive state data candidate 1)
        (lowRow parameters length compact lower positive bounded lengthPositive state data candidate 2 -
          radialRadiusRow lower positive (g parameters length lower positive bounded lengthPositive data)) index := by
  filter_upwards [represented.rawFirst parameters length compact lower positive bounded lengthPositive state data candidate tuple,
    represented.rawFlux parameters length compact lower positive bounded lengthPositive state data candidate tuple,
    lowRhoPhysicalCoefficient_add_ae parameters lower positive
      (lowRow parameters length compact lower positive bounded lengthPositive state data candidate 0)
      (highSourceF lower (lowKnown parameters length lower positive bounded lengthPositive data)),
    lowRhoPhysicalCoefficient_sub_ae parameters lower positive
      (lowRow parameters length compact lower positive bounded lengthPositive state data candidate 2)
      (radialRadiusRow lower positive (g parameters length lower positive bounded lengthPositive data)),
    lowRhoPhysicalCoefficient_radius_ae parameters lower positive (g parameters length lower positive bounded lengthPositive data),
    ae_restrict_mem measurableSet_Icc] with radius first flux added subtracted radial inside
  rcases index with ⟨entry,mode⟩
  have nonzero : mode.val.1 ≠ 0 := by have small := mode.property; intro zero; simp only [zero,abs_zero] at small; omega
  have notHigh : ¬ 3 ≤ |mode.val.1| := by have small := mode.property; omega
  have xSame : sameCoupledXCoefficient parameters lower length positive bounded lengthPositive
      (lowCandidate parameters length lower positive bounded lengthPositive candidate) 0 ⟨radius,inside⟩ mode.val =
      radialSectionExtension 1 lower bounded.le
        (lowPhysicalSection parameters lower length positive bounded
          (lowCandidate parameters length lower positive bounded lengthPositive candidate).ofLp.2 (1,mode)) radius := by
    rw [lowSectionExtension_eval lower bounded.le _ radius inside]
    simp only [sameCoupledXCoefficient,dif_neg notHigh,dif_pos mode.property,pow_zero,Complex.ofReal_one,one_smul]
  fin_cases entry
  · norm_num only [originalTupleLowSlope,lowPhysicalRawSlope,Fin.ext_iff,Fin.val_zero,Fin.val_one,if_true,if_false]
    rw [originalTupleSlopeCurve_same parameters lower bounded tuple 1 mode.val radius inside,
      first inside mode.val,added mode.val]
    simp only [angularMeanFreeMultiplier,if_neg nonzero,one_smul]
    rfl
  · norm_num only [originalTupleLowSlope,lowPhysicalRawSlope,Fin.ext_iff,Fin.val_zero,Fin.val_one,if_true,if_false,ContinuousMap.smul_apply]
    rw [originalTupleSlopeCurve_same parameters lower bounded tuple 0 mode.val radius inside,
      flux inside mode.val,subtracted mode.val,radial mode.val,xSame]
    exact (lowRawFlux_formula length radius (positive.trans_le inside.1).ne' mode.val _ _ _ _).symm

/-- The literal arbitrary represented tuple gives the ORIGINAL stored low
lowRow. Both derivative and its full-source equation are proved from AH24. -/
theorem OriginalTupleObservation.lowStoredRow :
    (lowCandidate parameters length lower positive bounded lengthPositive candidate).ofLp.2.val 1 =
      strongLowPhysicalRHS parameters length compact lower positive bounded.le lengthPositive state
        (lowDatum parameters length lower positive bounded lengthPositive data)
        (lowCandidate parameters length lower positive bounded lengthPositive candidate) := by
  exact lowFullRows_of_rawClassical parameters lower length positive bounded lengthPositive
    (lowCandidate parameters length lower positive bounded lengthPositive candidate).ofLp.2 _ _ _
    (originalTupleLowSlope parameters lower bounded tuple)
    (represented.low_derivative parameters lower bounded tuple length compact positive lengthPositive state data candidate)
    (represented.lowSlope_actual parameters length compact lower positive bounded lengthPositive state data candidate tuple)

end Grad.AnnularOriginalSmoothCore
