import ANP8StoredJetCovariance

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.RawCircularSectors
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
variable {L sigma gamma ell : ℝ}

def apSmoothRawStored (L sigma gamma ell : ℝ) (mode : ℤ) :
    APSmooth L sigma gamma ell 3 →ₗ[ℂ] APSmooth L sigma gamma ell 3 :=
  (apSmoothValueMap L sigma gamma ell planarInclusionMap).comp
    ((apSmoothRawVector L sigma gamma ell mode).comp (apSmoothPlanar L sigma gamma ell)) +
  (apSmoothValueMap L sigma gamma ell toroidalInclusionMap).comp
    ((apSmoothAngularMode L sigma gamma ell 1 mode).comp (apSmoothScalar L sigma gamma ell))

theorem apSmoothRawStored_jet (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (field : APSmooth L sigma gamma ell 3) (cell : ℤ) :
    apSmoothJet admissible 3 cell (apSmoothRawStored L sigma gamma ell mode field) =
      rawStoredJet mode (apSmoothJet admissible 3 cell field) := by
  have planar := (apSmoothRawVector_jet admissible mode (apSmoothPlanar L sigma gamma ell field) cell).trans
    (congrArg (rawVectorJet mode) (apSmoothValueMap_jet admissible planarPartMap field cell))
  have scalar := (apSmoothAngularMode_jet admissible mode (apSmoothScalar L sigma gamma ell field) cell).trans
    (congrArg (angularClosedJet mode) (apSmoothValueMap_jet admissible toroidalPartMap field cell))
  have first := (apSmoothValueMap_jet admissible planarInclusionMap _ cell).trans
    (congrArg (valueMapJet planarInclusionMap) planar)
  have second := (apSmoothValueMap_jet admissible toroidalInclusionMap _ cell).trans
    (congrArg (valueMapJet toroidalInclusionMap) scalar)
  exact (map_add (apSmoothJet admissible 3 cell) _ _).trans
    (congrArg₂ (fun first second : ClosedJet 3 => first + second) first second)

theorem apSmoothRawStored_planar (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (field : APSmooth L sigma gamma ell 3) :
    apSmoothPlanar L sigma gamma ell (apSmoothRawStored L sigma gamma ell mode field) =
      apSmoothRawVector L sigma gamma ell mode (apSmoothPlanar L sigma gamma ell field) := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothValueMap_jet admissible planarPartMap _ cell).trans
    ((congrArg (valueMapJet planarPartMap) (apSmoothRawStored_jet admissible mode field cell)).trans
      ((rawStoredJet_planar mode _).trans
        ((congrArg (rawVectorJet mode) (apSmoothValueMap_jet admissible planarPartMap field cell).symm).trans
          (apSmoothRawVector_jet admissible mode _ cell).symm)))

theorem apSmoothRawStored_scalar (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (field : APSmooth L sigma gamma ell 3) :
    apSmoothScalar L sigma gamma ell (apSmoothRawStored L sigma gamma ell mode field) =
      apSmoothAngularMode L sigma gamma ell 1 mode (apSmoothScalar L sigma gamma ell field) := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothValueMap_jet admissible toroidalPartMap _ cell).trans
    ((congrArg (valueMapJet toroidalPartMap) (apSmoothRawStored_jet admissible mode field cell)).trans
      ((rawStoredJet_scalar mode _).trans
        ((congrArg (angularClosedJet mode) (apSmoothValueMap_jet admissible toroidalPartMap field cell).symm).trans
          (apSmoothAngularMode_jet admissible mode _ cell).symm)))

theorem apSmoothRawStored_covariant (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (field : APSmooth L sigma gamma ell 1) :
    apSmoothRawStored L sigma gamma ell mode (apSmoothCovariant admissible field) =
      apSmoothCovariant admissible (apSmoothAngularMode L sigma gamma ell 1 mode field) := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothRawStored_jet admissible mode _ cell).trans
    ((congrArg (rawStoredJet mode) (apSmoothCovariant_jet admissible field cell)).trans
      ((rawStoredJet_covariant mode _ _).trans
        ((congrArg (covariantJet (Grad.GaugeCoefficients.Physical.Frame.seedScaledFrequency L ell cell))
          (apSmoothAngularMode_jet admissible mode field cell).symm).trans
            (apSmoothCovariant_jet admissible _ cell).symm)))

theorem apSmoothRawStored_complement (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (field : APSmooth L sigma gamma ell 3) :
    apSmoothRawStored L sigma gamma ell mode (apSmoothComplement L sigma gamma ell field) =
      apSmoothComplement L sigma gamma ell (apSmoothRawStored L sigma gamma ell mode field) := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothRawStored_jet admissible mode _ cell).trans
    ((congrArg (rawStoredJet mode) (apSmoothComplement_jet admissible field cell)).trans
      ((rawStoredJet_complement mode _).trans
        ((congrArg fixedComplementJet (apSmoothRawStored_jet admissible mode field cell).symm).trans
          (apSmoothComplement_jet admissible _ cell).symm)))

theorem apSmoothRawStored_firstJet_zero (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (field : APSmooth L sigma gamma ell 3) (zero : APSmoothAxisFirstJetZero admissible field) :
    APSmoothAxisFirstJetZero admissible (apSmoothRawStored L sigma gamma ell mode field) := by
  apply apSmoothAxisFirstJetZero_of_closed
  intro cell
  exact (congrArg ClosedFirstJetZero (apSmoothRawStored_jet admissible mode field cell)).mpr
    (rawStoredJet_firstJet_zero mode _ (apSmoothAxisFirstJetZero_closed admissible field zero cell))

/-- Original compensated coordinates are projected before reconstruction. -/
def rawStateProjector (L sigma gamma ell : ℝ) (mode : ℤ) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] CompensatedData L sigma gamma ell :=
  ((apSmoothAngularMode L sigma gamma ell 1 mode).comp (LinearMap.fst ℂ _ _)).prod
    ((apSmoothRawStored L sigma gamma ell mode).comp (LinearMap.snd ℂ _ _))

theorem rawStateProjector_reconstruct (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (state : CompensatedData L sigma gamma ell) :
    compensatedReconstruct admissible (rawStateProjector L sigma gamma ell mode state) =
      apSmoothRawStored L sigma gamma ell mode (compensatedReconstruct admissible state) :=
  (congrArg (fun field : APSmooth L sigma gamma ell 3 => field + apSmoothRawStored L sigma gamma ell mode state.2)
    (apSmoothRawStored_covariant admissible mode state.1).symm).trans
      (map_add (apSmoothRawStored L sigma gamma ell mode) (apSmoothCovariant admissible state.1) state.2).symm

/-- Both gauges and the actual compensated axis condition survive in the
original circular domain; the covariant gradient commutator is proved above. -/
theorem rawStateProjector_preserves (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (state : CompensatedData L sigma gamma ell) (member : state ∈ circularCompensatedCore admissible) :
    rawStateProjector L sigma gamma ell mode state ∈ circularCompensatedCore admissible := by
  have flat := (mem_compensatedFlatCore admissible state).mp member.1
  refine ⟨(mem_compensatedFlatCore admissible _).mpr ⟨⟨apSmoothAngularMode_mean_zero admissible mode state.1 flat.1.1,
    apSmoothAngularMode_firstJet_zero admissible mode state.1 flat.1.2⟩, ?_⟩, ?_⟩
  · exact (congrArg (APSmoothAxisFirstJetZero admissible) (rawStateProjector_reconstruct admissible mode state)).mpr
      (apSmoothRawStored_firstJet_zero admissible mode _ flat.2)
  · exact (congrArg (apSmoothComplement L sigma gamma ell) (rawStateProjector_reconstruct admissible mode state)).trans
      ((apSmoothRawStored_complement admissible mode _).symm.trans
        ((congrArg (apSmoothRawStored L sigma gamma ell mode) member.2).trans (map_zero _)))

theorem rawStateProjector_sector (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (state : CompensatedData L sigma gamma ell) :
    IsRawStateSector admissible mode (rawStateProjector L sigma gamma ell mode state) := by
  refine ⟨?_, ?_, ?_⟩
  · intro cell
    have law := apSmoothAngularMode_jet admissible mode state.1 cell
    exact (congrArg (fun jet : ClosedJet 1 => angularClosedJet mode jet = jet) law).mpr
      ((angularClosedJet_projection mode mode _).trans (if_pos rfl))
  · intro cell
    have law := (congrArg (apSmoothJet admissible 2 cell) (apSmoothRawStored_planar admissible mode state.2)).trans
      (apSmoothRawVector_jet admissible mode _ cell)
    exact (congrArg (fun jet : ClosedJet 2 => rawVectorJet mode jet = jet) law).mpr
      ((rawVectorJet_projection mode mode _).trans (if_pos rfl))
  · intro cell
    have law := (congrArg (apSmoothJet admissible 1 cell) (apSmoothRawStored_scalar admissible mode state.2)).trans
      (apSmoothAngularMode_jet admissible mode _ cell)
    exact (congrArg (fun jet : ClosedJet 1 => angularClosedJet mode jet = jet) law).mpr
      ((angularClosedJet_projection mode mode _).trans (if_pos rfl))

end Grad.RawCircularSectors
