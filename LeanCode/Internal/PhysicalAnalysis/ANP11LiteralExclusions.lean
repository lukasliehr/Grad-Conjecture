import ANP10ProjectionAlgebra

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.RawCircularSectors
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.FlatSourceProjection
variable {L sigma gamma ell : ℝ}

def AvoidsExceptionalSource (source : SmoothCapSource L sigma gamma ell) : Prop :=
  ∀ mode, IsExceptionalRaw mode → rawSourceProjector L sigma gamma ell mode source = 0

def AvoidsExceptionalState (state : CompensatedData L sigma gamma ell) : Prop :=
  ∀ mode, IsExceptionalRaw mode → rawStateProjector L sigma gamma ell mode state = 0

theorem rawSourceComplement_avoids (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) : AvoidsExceptionalSource (rawSourceComplement L sigma gamma ell source) :=
  fun mode exceptional => rawSourceComplement_excludes admissible mode exceptional source

theorem rawStateComplement_avoids (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell) : AvoidsExceptionalState (rawStateComplement L sigma gamma ell state) :=
  fun mode exceptional => rawStateComplement_excludes admissible mode exceptional state

theorem rawSource_excluded_components (admissible : Admissible L sigma gamma ell) (mode : ℤ)
    (source : SmoothCapSource L sigma gamma ell) (excluded : rawSourceProjector L sigma gamma ell mode source = 0)
    (cell : ℤ) :
    rawVectorJet mode (apSmoothJet admissible 2 cell source.1) = 0 ∧
      angularClosedJet mode (apSmoothJet admissible 1 cell source.2.1) = 0 ∧
        angularClosedJet mode (apSmoothJet admissible 1 cell source.2.2) = 0 := by
  have first : apSmoothRawVector L sigma gamma ell mode source.1 = 0 := congrArg Prod.fst excluded
  have second : apSmoothAngularMode L sigma gamma ell 1 mode source.2.1 = 0 :=
    congrArg (fun value : SmoothCapSource L sigma gamma ell => value.2.1) excluded
  have third : apSmoothAngularMode L sigma gamma ell 1 mode source.2.2 = 0 :=
    congrArg (fun value : SmoothCapSource L sigma gamma ell => value.2.2) excluded
  exact ⟨(apSmoothRawVector_jet admissible mode source.1 cell).symm.trans
      ((congrArg (apSmoothJet admissible 2 cell) first).trans (map_zero _)),
    (apSmoothAngularMode_jet admissible mode source.2.1 cell).symm.trans
      ((congrArg (apSmoothJet admissible 1 cell) second).trans (map_zero _)),
    (apSmoothAngularMode_jet admissible mode source.2.2 cell).symm.trans
      ((congrArg (apSmoothJet admissible 1 cell) third).trans (map_zero _))⟩

theorem rawSource_excluded_spin (admissible : Admissible L sigma gamma ell) (mode sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (excluded : rawSourceProjector L sigma gamma ell mode source = 0) (cell : ℤ) :
    angularClosedJet (mode + sign) (valueMapJet (spinValue (sign : ℂ)) (apSmoothJet admissible 2 cell source.1)) = 0 :=
  (rawVectorJet_spin sign signed mode _).symm.trans
    ((congrArg (valueMapJet (spinValue (sign : ℂ)))
      (rawSource_excluded_components admissible mode source excluded cell).1).trans (valueMapJet_map_zero _))

theorem rawState_excluded_components (admissible : Admissible L sigma gamma ell) (mode : ℤ)
    (state : CompensatedData L sigma gamma ell) (excluded : rawStateProjector L sigma gamma ell mode state = 0)
    (cell : ℤ) :
    angularClosedJet mode (apSmoothJet admissible 1 cell state.1) = 0 ∧
      rawVectorJet mode (apSmoothJet admissible 2 cell (apSmoothPlanar L sigma gamma ell state.2)) = 0 ∧
        angularClosedJet mode (apSmoothJet admissible 1 cell (apSmoothScalar L sigma gamma ell state.2)) = 0 := by
  have first : apSmoothAngularMode L sigma gamma ell 1 mode state.1 = 0 := congrArg Prod.fst excluded
  have stored : apSmoothRawStored L sigma gamma ell mode state.2 = 0 := congrArg Prod.snd excluded
  have planar := (apSmoothRawStored_planar admissible mode state.2).symm.trans
    ((congrArg (apSmoothPlanar L sigma gamma ell) stored).trans (map_zero _))
  have scalar := (apSmoothRawStored_scalar admissible mode state.2).symm.trans
    ((congrArg (apSmoothScalar L sigma gamma ell) stored).trans (map_zero _))
  exact ⟨(apSmoothAngularMode_jet admissible mode state.1 cell).symm.trans
      ((congrArg (apSmoothJet admissible 1 cell) first).trans (map_zero _)),
    (apSmoothRawVector_jet admissible mode _ cell).symm.trans
      ((congrArg (apSmoothJet admissible 2 cell) planar).trans (map_zero _)),
    (apSmoothAngularMode_jet admissible mode _ cell).symm.trans
      ((congrArg (apSmoothJet admissible 1 cell) scalar).trans (map_zero _))⟩

theorem rawState_excluded_spin (admissible : Admissible L sigma gamma ell) (mode sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (state : CompensatedData L sigma gamma ell)
    (excluded : rawStateProjector L sigma gamma ell mode state = 0) (cell : ℤ) :
    angularClosedJet (mode + sign) (valueMapJet (spinValue (sign : ℂ))
      (apSmoothJet admissible 2 cell (apSmoothPlanar L sigma gamma ell state.2))) = 0 :=
  (rawVectorJet_spin sign signed mode _).symm.trans
    ((congrArg (valueMapJet (spinValue (sign : ℂ)))
      (rawState_excluded_components admissible mode state excluded cell).2.1).trans (valueMapJet_map_zero _))

theorem rawStateSector_spin (admissible : Admissible L sigma gamma ell) (mode sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (state : CompensatedData L sigma gamma ell)
    (pure : IsRawStateSector admissible mode state) (cell : ℤ) :
    angularClosedJet (mode + sign) (valueMapJet (spinValue (sign : ℂ))
      (apSmoothJet admissible 2 cell (apSmoothPlanar L sigma gamma ell state.2))) =
        valueMapJet (spinValue (sign : ℂ)) (apSmoothJet admissible 2 cell (apSmoothPlanar L sigma gamma ell state.2)) :=
  rawVectorSector_spin sign signed mode _ (pure.2.1 cell)

end Grad.RawCircularSectors
