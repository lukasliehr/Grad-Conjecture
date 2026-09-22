import ZE1Maps
import SM1Consumer

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue CellValues FieldL2)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets.ZeroExtension

set_option maxHeartbeats 1200000

theorem scalarDerivative_zero_off_support (index : ℕ × ℕ) (scalar : Spatial → ℝ)
    (point : Spatial) (outside : point ∉ tsupport scalar) :
    SpatialMultiplier.scalarDerivative index scalar point = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  exact fun membership => outside
    (Grad.WeakTesting.orderedTestDerivative_support_subset (index.1 + index.2)
      (Grad.WeakTesting.Commutation.canonicalWord index.1 index.2) scalar membership)

theorem jetMultiplier_supported (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : SpatialMultiplier.Symbol order domain)
    (exponent : JetIndex order → ℕ) (compatible : SpatialMultiplier.ExponentAntitone exponent)
    (jet : WJet dimension order domain exponent) :
    TupleSupported dimension order domain (tsupport symbol.toFun)
      (SpatialMultiplier.jetMultiplier dimension order domain openDomain symbol exponent compatible jet).val := by
  intro index
  filter_upwards [SpatialMultiplier.jetMultiplier_ae dimension order domain openDomain
    symbol exponent compatible jet] with point represented
  intro outside
  apply lp.ext
  funext cell
  change (SpatialMultiplier.jetMultiplier dimension order domain openDomain symbol exponent compatible jet).val
    index point cell = 0
  rw [represented index cell]
  apply Finset.sum_eq_zero
  intro lower _membership
  rw [scalarDerivative_zero_off_support (SpatialMultiplier.difference index lower).val
    symbol.toFun point outside]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_smul]

theorem compactJetMultiplier_supported (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (compact : HasCompactSupport scalar) (exponent : JetIndex order → ℕ)
    (compatible : SpatialMultiplier.ExponentAntitone exponent) (jet : WJet dimension order domain exponent) :
    TupleSupported dimension order domain (tsupport scalar)
      (SpatialMultiplier.compactJetMultiplier dimension order domain openDomain scalar smooth compact
        exponent compatible jet).val :=
  jetMultiplier_supported dimension order domain openDomain
    (SpatialMultiplier.compactSymbol order domain scalar smooth compact) exponent compatible jet

def supportedMultiplier (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : SpatialMultiplier.Symbol order domain)
    (exponent : JetIndex order → ℕ) (compatible : SpatialMultiplier.ExponentAntitone exponent) :
    WJet dimension order domain exponent →L[ℂ]
      supportedJetSubmodule dimension order domain (tsupport symbol.toFun) exponent :=
  (SpatialMultiplier.jetMultiplier dimension order domain openDomain symbol exponent compatible).codRestrict
    (supportedJetSubmodule dimension order domain (tsupport symbol.toFun) exponent)
    (jetMultiplier_supported dimension order domain openDomain symbol exponent compatible)

def extendedMultiplier (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : SpatialMultiplier.Symbol order domain)
    (localizer : TestLocalizer domain (tsupport symbol.toFun))
    (exponent : JetIndex order → ℕ) (compatible : SpatialMultiplier.ExponentAntitone exponent) :
    WJet dimension order domain exponent →L[ℂ] WJet dimension order Set.univ exponent :=
  (jetExtension dimension order domain (tsupport symbol.toFun) openDomain.measurableSet
    localizer exponent).toContinuousLinearMap.comp
    (supportedMultiplier dimension order domain openDomain symbol exponent compatible)

theorem extendedMultiplier_norm (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : SpatialMultiplier.Symbol order domain)
    (localizer : TestLocalizer domain (tsupport symbol.toFun))
    (exponent : JetIndex order → ℕ) (compatible : SpatialMultiplier.ExponentAntitone exponent)
    (jet : WJet dimension order domain exponent) :
    ‖extendedMultiplier dimension order domain openDomain symbol localizer exponent compatible jet‖ =
      ‖SpatialMultiplier.jetMultiplier dimension order domain openDomain symbol exponent compatible jet‖ :=
  extendJet_norm dimension order domain (tsupport symbol.toFun) openDomain.measurableSet localizer exponent
    (SpatialMultiplier.jetMultiplier dimension order domain openDomain symbol exponent compatible jet)
    (jetMultiplier_supported dimension order domain openDomain symbol exponent compatible jet)

theorem extendedMultiplier_opNorm_le (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : SpatialMultiplier.Symbol order domain)
    (localizer : TestLocalizer domain (tsupport symbol.toFun))
    (exponent : JetIndex order → ℕ) (compatible : SpatialMultiplier.ExponentAntitone exponent) :
    ‖extendedMultiplier dimension order domain openDomain symbol localizer exponent compatible‖ ≤
      SpatialMultiplier.matrixBound symbol := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro jet
  rw [extendedMultiplier_norm]
  exact SpatialMultiplier.tupleMultiplier_apply_norm_le dimension order domain openDomain symbol exponent jet.val

theorem extendedMultiplier_base (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : SpatialMultiplier.Symbol order domain)
    (localizer : TestLocalizer domain (tsupport symbol.toFun))
    (exponent : JetIndex order → ℕ) (compatible : SpatialMultiplier.ExponentAntitone exponent)
    (jet : WJet dimension order domain exponent) :
    base dimension order Set.univ exponent
        (extendedMultiplier dimension order domain openDomain symbol localizer exponent compatible jet) =
      fieldExtension (CellValues dimension) domain openDomain.measurableSet
        (SpatialMultiplier.fieldMultiplier dimension domain openDomain
          (SpatialMultiplier.derivativeScalar symbol (zeroIndex order))
          (base dimension order domain exponent jet)) := by
  change base dimension order Set.univ exponent
    (extendJet dimension order domain (tsupport symbol.toFun) openDomain.measurableSet localizer exponent
      (SpatialMultiplier.jetMultiplier dimension order domain openDomain symbol exponent compatible jet)
      (jetMultiplier_supported dimension order domain openDomain symbol exponent compatible jet)) = _
  rw [extendJet_base, SpatialMultiplier.jetMultiplier_base_apply]

theorem extendedMultiplier_restriction (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : SpatialMultiplier.Symbol order domain)
    (localizer : TestLocalizer domain (tsupport symbol.toFun))
    (exponent : JetIndex order → ℕ) (compatible : SpatialMultiplier.ExponentAntitone exponent)
    (jet : WJet dimension order domain exponent) :
    Restriction.restriction dimension order (Set.subset_univ domain) MeasurableSet.univ exponent
        (extendedMultiplier dimension order domain openDomain symbol localizer exponent compatible jet) =
      SpatialMultiplier.jetMultiplier dimension order domain openDomain symbol exponent compatible jet :=
  restriction_extendJet dimension order domain (tsupport symbol.toFun) openDomain.measurableSet localizer exponent
    (SpatialMultiplier.jetMultiplier dimension order domain openDomain symbol exponent compatible jet)
    (jetMultiplier_supported dimension order domain openDomain symbol exponent compatible jet)

end Grad.WeightedJets.ZeroExtension
