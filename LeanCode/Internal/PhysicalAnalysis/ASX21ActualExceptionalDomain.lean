import ASX20ActualSourceModes
import ANP8StoredJetCovariance

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.ActualCenterVolterra
open Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.RawCircularSectors Grad.FlatSourceProjection Grad.ActualMeanInverse
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.RadialLedger
variable {L sigma gamma ell : ℝ}

theorem rawVector_of_spins (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (mode : ℤ) (field : ClosedJet 2)
    (first : angularClosedJet (mode + sign) (valueMapJet (spinValue (sign : ℂ)) field) = valueMapJet (spinValue (sign : ℂ)) field)
    (second : angularClosedJet (mode + -sign) (valueMapJet (spinValue ((-sign : ℤ) : ℂ)) field) = valueMapJet (spinValue ((-sign : ℤ) : ℂ)) field) :
    rawVectorJet mode field = field := by
  apply spinJet_ext sign signed
  · exact (rawVectorJet_spin sign signed mode field).trans first
  · exact (rawVectorJet_spin (-sign) (by omega) mode field).trans second

theorem smoothRawVector_of_spins (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (mode : ℤ) (field : APSmooth L sigma gamma ell 2)
    (first : HasSmoothMode admissible (mode + sign) (smoothSpin L sigma gamma ell sign field))
    (second : HasSmoothMode admissible (mode + -sign) (smoothSpin L sigma gamma ell (-sign) field)) (cell : ℤ) :
    rawVectorJet mode (apSmoothJet admissible 2 cell field) = apSmoothJet admissible 2 cell field := by
  apply rawVector_of_spins sign signed
  · have law := first cell
    rw [smoothSpin_jet] at law
    exact law
  · have law := second cell
    rw [smoothSpin_jet] at law
    exact law

theorem exceptionalPlanar_modes (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) :
    HasSmoothMode admissible (3 * sign) (smoothSpin L sigma gamma ell sign (exceptionalPlanar admissible sign source)) ∧
    HasSmoothMode admissible sign (smoothSpin L sigma gamma ell (-sign) (exceptionalPlanar admissible sign source)) :=
  ⟨(congrArg (HasSmoothMode admissible (3 * sign)) (exceptionalPlanar_first admissible sign signed source)).mpr
      (exceptionalFixedSpin_mode admissible sign signed source raw),
    (congrArg (HasSmoothMode admissible sign) (exceptionalPlanar_second admissible sign signed source)).mpr
      (exceptionalFreeSpin_mode admissible sign signed source raw)⟩

theorem exceptionalState_planar_modes (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) :
    HasSmoothMode admissible (3 * sign) (smoothSpin L sigma gamma ell sign
      (apSmoothPlanar L sigma gamma ell (exceptionalState admissible sign source).2)) ∧
    HasSmoothMode admissible sign (smoothSpin L sigma gamma ell (-sign)
      (apSmoothPlanar L sigma gamma ell (exceptionalState admissible sign source).2)) := by
  have planar := exceptionalPlanar_modes admissible sign signed source raw
  have theta := exceptionalTheta_mode admissible sign signed source raw
  constructor
  · have derivative : HasSmoothMode admissible (3 * sign)
        (smoothSignedDerivative admissible 1 (-sign) (exceptionalTheta admissible sign source)) := by
      simpa only [show 2 * sign - -sign = 3 * sign by omega] using
        smoothMode_signedDerivative admissible (-sign) (by omega) (2 * sign) _ theta
    exact (congrArg (HasSmoothMode admissible (3 * sign)) (exceptionalState_spin admissible sign sign source)).mpr
      (smoothMode_sub admissible (3 * sign) _ _ planar.1 derivative)
  · have derivative : HasSmoothMode admissible sign
        (smoothSignedDerivative admissible 1 (- -sign) (exceptionalTheta admissible sign source)) := by
      simpa only [neg_neg, show 2 * sign - sign = sign by omega] using
        smoothMode_signedDerivative admissible sign signed (2 * sign) _ theta
    exact (congrArg (HasSmoothMode admissible sign) (exceptionalState_spin admissible sign (-sign) source)).mpr
      (smoothMode_sub admissible sign _ _ planar.2 derivative)

theorem exceptionalState_sector (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) :
    IsRawStateSector admissible (2 * sign) (exceptionalState admissible sign source) := by
  have planar := exceptionalState_planar_modes admissible sign signed source raw
  refine ⟨exceptionalTheta_mode admissible sign signed source raw, ?_, ?_⟩
  · apply smoothRawVector_of_spins admissible sign signed
    · simpa only [show 2 * sign + sign = 3 * sign by omega] using planar.1
    · simpa only [show 2 * sign + -sign = sign by omega] using planar.2
  · exact (congrArg (HasSmoothMode admissible (2 * sign)) (exceptionalState_scalar admissible sign source)).mpr
      (smoothMode_smul admissible (2 * sign) _ source.2.2 raw.2.2)

private theorem smoothFlat_add (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (first second : APSmooth L sigma gamma ell dimension)
    (a : APSmoothAxisFirstJetZero admissible first) (b : APSmoothAxisFirstJetZero admissible second) :
    APSmoothAxisFirstJetZero admissible (first + second) :=
  (mem_apSmoothAxisFirsts admissible _).mp ((apSmoothAxisFirsts admissible dimension).add_mem
    ((mem_apSmoothAxisFirsts admissible _).mpr a) ((mem_apSmoothAxisFirsts admissible _).mpr b))

private theorem smoothFlat_sub (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (first second : APSmooth L sigma gamma ell dimension)
    (a : APSmoothAxisFirstJetZero admissible first) (b : APSmoothAxisFirstJetZero admissible second) :
    APSmoothAxisFirstJetZero admissible (first - second) :=
  (mem_apSmoothAxisFirsts admissible _).mp ((apSmoothAxisFirsts admissible dimension).sub_mem
    ((mem_apSmoothAxisFirsts admissible _).mpr a) ((mem_apSmoothAxisFirsts admissible _).mpr b))

private theorem smoothFlat_smul (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (scalar : ℂ) (field : APSmooth L sigma gamma ell dimension) (flat : APSmoothAxisFirstJetZero admissible field) :
    APSmoothAxisFirstJetZero admissible (scalar • field) :=
  (mem_apSmoothAxisFirsts admissible _).mp ((apSmoothAxisFirsts admissible dimension).smul_mem scalar
    ((mem_apSmoothAxisFirsts admissible _).mpr flat))

theorem exceptionalPlanar_pinned (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) :
    APSmoothAxisFirstJetZero admissible (exceptionalPlanar admissible sign source) := by
  have first := smoothMode_pinned admissible (3 * sign) (by omega) (by omega) (by omega) _
    (exceptionalFixedSpin_mode admissible sign signed source raw)
  have second := smoothPinnedPrimitive_pinned admissible sign (exceptionalFreeForcing admissible sign source)
  exact smoothFlat_add admissible _ _
    (smoothFlat_smul admissible (1 / 2 : ℂ) _
      (apSmoothValueMap_preserves_firstJet admissible (matrixUnit 0 0) _ (smoothFlat_add admissible _ _ first second)))
    (smoothFlat_smul admissible (2 * Complex.I * (sign : ℂ))⁻¹ _
      (apSmoothValueMap_preserves_firstJet admissible (matrixUnit 1 0) _ (smoothFlat_sub admissible _ _ first second)))

theorem exceptionalCovariant_pinned (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) :
    APSmoothAxisFirstJetZero admissible (exceptionalCovariant admissible sign source) :=
  smoothFlat_add admissible _ _
    (apSmoothValueMap_preserves_firstJet admissible planarInclusionMap _ (exceptionalPlanar_pinned admissible sign signed source raw))
    (apSmoothValueMap_preserves_firstJet admissible toroidalInclusionMap _
      (smoothMode_pinned admissible (2 * sign) (by omega) (by omega) (by omega) _
        (exceptionalToroidal_mode admissible sign signed source raw)))

theorem exceptionalCovariant_complement_zero (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) :
    apSmoothComplement L sigma gamma ell (exceptionalCovariant admissible sign source) = 0 := by
  have modes := exceptionalPlanar_modes admissible sign signed source raw
  have vector (cell : ℤ) := smoothRawVector_of_spins admissible sign signed (2 * sign)
    (exceptionalPlanar admissible sign source)
    (by simpa only [show 2 * sign + sign = 3 * sign by omega] using modes.1)
    (by simpa only [show 2 * sign + -sign = sign by omega] using modes.2) cell
  have tangent : apSmoothTangential L sigma gamma ell (exceptionalPlanar admissible sign source) = 0 := by
    apply apSmoothJet_ext admissible
    intro cell
    have law := (congrArg tangentialJet (vector cell)).symm.trans
      ((tangential_rawVector_value (2 * sign) _).trans (if_neg (by omega : 2 * sign ≠ 0)))
    exact (apSmoothTangential_jet admissible _ cell).trans (law.trans (map_zero (apSmoothJet admissible 2 cell)).symm)
  have mean : apSmoothAngularMean L sigma gamma ell 1 (exceptionalToroidal admissible sign source) = 0 := by
    apply apSmoothJet_ext admissible
    intro cell
    exact (apSmoothAngularMean_jet admissible _ cell).trans
      ((smoothMode_meanZero admissible (2 * sign) (by omega) _
        (exceptionalToroidal_mode admissible sign signed source raw) cell).trans (map_zero (apSmoothJet admissible 1 cell)).symm)
  have planar := (apSmoothPlanar_complement admissible (exceptionalCovariant admissible sign source)).trans
    ((congrArg (apSmoothTangential L sigma gamma ell) (exceptionalCovariant_planar admissible sign source)).trans tangent)
  have scalar := (apSmoothScalar_complement admissible (exceptionalCovariant admissible sign source)).trans
    ((congrArg (apSmoothAngularMean L sigma gamma ell 1) (exceptionalCovariant_scalar admissible sign source)).trans mean)
  have first := (congrArg (apSmoothValueMap L sigma gamma ell planarInclusionMap) planar).trans (map_zero _)
  have second := (congrArg (apSmoothValueMap L sigma gamma ell toroidalInclusionMap) scalar).trans (map_zero _)
  exact (apSmooth_splitting admissible _).symm.trans
    ((congrArg₂ (fun first second : APSmooth L sigma gamma ell 3 => first + second) first second).trans (zero_add _))

/-- All original axis, mean and complementary gauges hold for the actual exceptional construction. -/
theorem exceptionalState_circularCore (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) :
    exceptionalState admissible sign source ∈ circularCompensatedCore admissible := by
  have theta := exceptionalTheta_mode admissible sign signed source raw
  refine ⟨(mem_compensatedFlatCore admissible _).mpr ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact smoothMode_meanZero admissible (2 * sign) (by omega) _ theta
  · exact smoothMode_pinned admissible (2 * sign) (by omega) (by omega) (by omega) _ theta
  · exact (congrArg (APSmoothAxisFirstJetZero admissible) (exceptionalState_reconstruct admissible sign source)).mpr
      (exceptionalCovariant_pinned admissible sign signed source raw)
  · exact (congrArg (apSmoothComplement L sigma gamma ell) (exceptionalState_reconstruct admissible sign source)).trans
      (exceptionalCovariant_complement_zero admissible sign signed source raw)

end Grad.ActualExceptionalInverse
