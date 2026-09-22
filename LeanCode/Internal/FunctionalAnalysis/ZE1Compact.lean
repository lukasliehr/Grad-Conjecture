import ZE1Consumer
import CUT1Consumer

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue CellValues FieldL2)
open scoped ContDiff Topology

namespace Grad.WeightedJets.ZeroExtension

set_option maxHeartbeats 1200000

def compactLocalizer (domain support : Set Spatial) (compact : IsCompact support)
    (openDomain : IsOpen domain) (included : support ⊆ domain) : TestLocalizer domain support where
  cutoff := {
    toFun := (Grad.CompactCutoff.compactCutoff support domain compact openDomain included).toFun
    smooth := (Grad.CompactCutoff.compactCutoff support domain compact openDomain included).smooth
    compact := (Grad.CompactCutoff.compactCutoff support domain compact openDomain included).compact
    supported := (Grad.CompactCutoff.compactCutoff support domain compact openDomain included).supported }
  one_near := Grad.CompactCutoff.compactCutoff_germ support domain compact openDomain included

def compactExtension (dimension order : ℕ) (domain support : Set Spatial)
    (compact : IsCompact support) (openDomain : IsOpen domain) (included : support ⊆ domain)
    (exponent : JetIndex order → ℕ) :
    supportedJetSubmodule dimension order domain support exponent →ₗᵢ[ℂ] WJet dimension order Set.univ exponent :=
  jetExtension dimension order domain support openDomain.measurableSet
    (compactLocalizer domain support compact openDomain included) exponent

theorem compactExtension_norm (dimension order : ℕ) (domain support : Set Spatial)
    (compact : IsCompact support) (openDomain : IsOpen domain) (included : support ⊆ domain)
    (exponent : JetIndex order → ℕ) (jet : supportedJetSubmodule dimension order domain support exponent) :
    ‖compactExtension dimension order domain support compact openDomain included exponent jet‖ = ‖jet‖ :=
  (compactExtension dimension order domain support compact openDomain included exponent).norm_map jet

theorem compactExtension_restriction (dimension order : ℕ) (domain support : Set Spatial)
    (compact : IsCompact support) (openDomain : IsOpen domain) (included : support ⊆ domain)
    (exponent : JetIndex order → ℕ) (jet : supportedJetSubmodule dimension order domain support exponent) :
    Restriction.restriction dimension order (Set.subset_univ domain) MeasurableSet.univ exponent
        (compactExtension dimension order domain support compact openDomain included exponent jet) = jet.val :=
  restriction_extendJet dimension order domain support openDomain.measurableSet
    (compactLocalizer domain support compact openDomain included) exponent jet.val jet.property

open Classical in
theorem compactExtension_coordinates (dimension order : ℕ) (domain support : Set Spatial)
    (compact : IsCompact support) (openDomain : IsOpen domain) (included : support ⊆ domain)
    (exponent : JetIndex order → ℕ) (jet : supportedJetSubmodule dimension order domain support exponent) :
    ∀ᵐ point ∂volume, ∀ (index : JetIndex order) (cell : ℤ),
      (compactExtension dimension order domain support compact openDomain included exponent jet).val index point cell =
        if point ∈ domain then jet.val.val index point cell else 0 :=
  extendJet_coordinates dimension order domain support openDomain.measurableSet
    (compactLocalizer domain support compact openDomain included) exponent jet.val jet.property

theorem compactExtension_weak (dimension order : ℕ) (domain support : Set Spatial)
    (compact : IsCompact support) (openDomain : IsOpen domain) (included : support ⊆ domain)
    (exponent : JetIndex order → ℕ) (jet : supportedJetSubmodule dimension order domain support exponent)
    (index : JetIndex order) (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction Set.univ) :
    testPairing dimension Set.univ cell vector test
        (fieldExtension (CellValues dimension) domain openDomain.measurableSet
          (Realization.recoveredDerivative dimension order domain exponent index jet.val)) =
      (-1 : ℂ) ^ degree index * derivativeTestPairing dimension order Set.univ index cell vector test
        (fieldExtension (CellValues dimension) domain openDomain.measurableSet
          (base dimension order domain exponent jet.val)) :=
  jetExtension_weak dimension order domain support openDomain.measurableSet
    (compactLocalizer domain support compact openDomain included) exponent jet index cell vector test

def compactScalarExtension (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar)
    (included : tsupport scalar ⊆ domain) (exponent : JetIndex order → ℕ)
    (compatible : SpatialMultiplier.ExponentAntitone exponent) :
    WJet dimension order domain exponent →L[ℂ] WJet dimension order Set.univ exponent :=
  extendedMultiplier dimension order domain openDomain
    (SpatialMultiplier.compactSymbol order domain scalar smooth compact)
    (compactLocalizer domain (tsupport scalar) compact openDomain included) exponent compatible

theorem compactScalarExtension_norm (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar)
    (included : tsupport scalar ⊆ domain) (exponent : JetIndex order → ℕ)
    (compatible : SpatialMultiplier.ExponentAntitone exponent) (jet : WJet dimension order domain exponent) :
    ‖compactScalarExtension dimension order domain openDomain scalar smooth compact included exponent compatible jet‖ =
      ‖SpatialMultiplier.compactJetMultiplier dimension order domain openDomain scalar smooth compact
        exponent compatible jet‖ :=
  extendedMultiplier_norm dimension order domain openDomain
    (SpatialMultiplier.compactSymbol order domain scalar smooth compact)
    (compactLocalizer domain (tsupport scalar) compact openDomain included) exponent compatible jet

theorem compactScalarExtension_restriction (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (compact : HasCompactSupport scalar) (included : tsupport scalar ⊆ domain)
    (exponent : JetIndex order → ℕ) (compatible : SpatialMultiplier.ExponentAntitone exponent)
    (jet : WJet dimension order domain exponent) :
    Restriction.restriction dimension order (Set.subset_univ domain) MeasurableSet.univ exponent
        (compactScalarExtension dimension order domain openDomain scalar smooth compact included exponent compatible jet) =
      SpatialMultiplier.compactJetMultiplier dimension order domain openDomain scalar smooth compact exponent compatible jet :=
  extendedMultiplier_restriction dimension order domain openDomain
    (SpatialMultiplier.compactSymbol order domain scalar smooth compact)
    (compactLocalizer domain (tsupport scalar) compact openDomain included) exponent compatible jet

end Grad.WeightedJets.ZeroExtension

