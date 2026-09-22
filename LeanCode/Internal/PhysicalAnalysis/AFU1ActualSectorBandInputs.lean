import AFI6OriginalNonexceptionalInverse
import AEN16ActualNativeExceptionalConsumer
import ANM8ActualMeanConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.FullReferenceAssembly
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Envelope Grad.ActualForcingSupport Grad.BoundedScalarInverse Grad.RawCircularSectors
open Grad.ExceptionalNative Grad.ActualMeanInverse
variable {L sigma gamma ell : ℝ}

theorem rawSourceProjector_band (admissible : Admissible L sigma gamma ell) (ceiling : ℝ)
    (source : SmoothCapSource L sigma gamma ell) (band : OriginalCapSourceBand admissible ceiling source) (mode : ℤ) :
    OriginalCapSourceBand admissible ceiling (rawSourceProjector L sigma gamma ell mode source) := by
  intro cell outside
  have absent := band cell outside
  constructor
  · change apSmoothJet admissible 2 cell (apSmoothRawVector L sigma gamma ell mode source.1) = 0
    exact (apSmoothRawVector_jet admissible mode source.1 cell).trans
      ((congrArg (rawVectorJet mode) absent.1).trans (map_zero (rawVectorJetLinear mode)))
  constructor
  · change apSmoothJet admissible 1 cell (apSmoothAngularMode L sigma gamma ell 1 mode source.2.1) = 0
    exact (apSmoothAngularMode_jet admissible mode source.2.1 cell).trans
      ((congrArg (angularClosedJet mode) absent.2.1).trans (map_zero (angularClosedJetLinear 1 mode)))
  · change apSmoothJet admissible 1 cell (apSmoothAngularMode L sigma gamma ell 1 mode source.2.2) = 0
    exact (apSmoothAngularMode_jet admissible mode source.2.2 cell).trans
      ((congrArg (angularClosedJet mode) absent.2.2).trans (map_zero (angularClosedJetLinear 1 mode)))

theorem capSourceBand_add (admissible : Admissible L sigma gamma ell) (ceiling : ℝ)
    (first second : SmoothCapSource L sigma gamma ell)
    (firstBand : OriginalCapSourceBand admissible ceiling first) (secondBand : OriginalCapSourceBand admissible ceiling second) :
    OriginalCapSourceBand admissible ceiling (first + second) := by
  intro cell outside
  have left := firstBand cell outside
  have right := secondBand cell outside
  change apSmoothJet admissible 2 cell (first.1 + second.1) = 0 ∧
    apSmoothJet admissible 1 cell (first.2.1 + second.2.1) = 0 ∧ apSmoothJet admissible 1 cell (first.2.2 + second.2.2) = 0
  simp only [map_add, left.1, left.2.1, left.2.2, right.1, right.2.1, right.2.2, add_zero, and_self]

theorem capSourceBand_sub (admissible : Admissible L sigma gamma ell) (ceiling : ℝ)
    (first second : SmoothCapSource L sigma gamma ell)
    (firstBand : OriginalCapSourceBand admissible ceiling first) (secondBand : OriginalCapSourceBand admissible ceiling second) :
    OriginalCapSourceBand admissible ceiling (first - second) := by
  intro cell outside
  have left := firstBand cell outside
  have right := secondBand cell outside
  change apSmoothJet admissible 2 cell (first.1 - second.1) = 0 ∧
    apSmoothJet admissible 1 cell (first.2.1 - second.2.1) = 0 ∧ apSmoothJet admissible 1 cell (first.2.2 - second.2.2) = 0
  simp only [map_sub, left.1, left.2.1, left.2.2, right.1, right.2.1, right.2.2, sub_self, and_self]

theorem rawSourceComplement_band (admissible : Admissible L sigma gamma ell) (ceiling : ℝ)
    (source : SmoothCapSource L sigma gamma ell) (band : OriginalCapSourceBand admissible ceiling source) :
    OriginalCapSourceBand admissible ceiling (rawSourceComplement L sigma gamma ell source) :=
  capSourceBand_sub admissible ceiling source _ band
    (capSourceBand_add admissible ceiling _ _
      (capSourceBand_add admissible ceiling _ _ (rawSourceProjector_band admissible ceiling source band 0)
        (rawSourceProjector_band admissible ceiling source band 2))
      (rawSourceProjector_band admissible ceiling source band (-2)))

theorem capSourceBand_exceptional (admissible : Admissible L sigma gamma ell) (ceiling : ℝ)
    (source : SmoothCapSource L sigma gamma ell) (band : OriginalCapSourceBand admissible ceiling source) :
    ExceptionalSourceBand admissible ceiling source :=
  ⟨fun cell outside => (band cell outside).1, fun cell outside => (band cell outside).2.1,
    fun cell outside => (band cell outside).2.2⟩

theorem rawSource_zero_mean (admissible : Admissible L sigma gamma ell) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible 0 source) : IsRawMeanSource admissible source :=
  ⟨fun cell => (rawVectorJet_zero _).symm.trans (raw.1 cell), raw.2.1, raw.2.2⟩

end Grad.FullReferenceAssembly
