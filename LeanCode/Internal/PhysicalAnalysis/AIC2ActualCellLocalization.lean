import AIC1ActualWeakJet

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.InteriorLocalization
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.WeightedJets Grad.WeightedJets.ZeroExtension

/-- Actual cutoff and zero-extension of a completed AP cell. The original
weak derivative graph supplies all coordinates; existing zero-extension
machinery proves the global distributional identities. -/
def apCellLocalized (L sigma gamma ell : ℝ) (dimension grade : ℕ) (cell : ℤ)
    (cutoff : Grad.PDEBootstrap.Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff)
    (compact : HasCompactSupport cutoff) (supported : tsupport cutoff ⊆ openUnitDisk) :
    apGrade L sigma gamma ell dimension grade →L[ℂ]
      WJet dimension grade Set.univ (fun _ => 0) :=
  (compactScalarExtension dimension grade openUnitDisk openUnitDisk_isOpen cutoff smooth compact
    supported (fun _ => 0) (SpatialMultiplier.constantExponent_antitone grade 0)).comp
      (apCellWeakJet L sigma gamma ell dimension grade cell)

def apCellLocalizationConstant (L sigma gamma ell : ℝ) (dimension grade : ℕ) (cell : ℤ)
    (cutoff : Grad.PDEBootstrap.Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff)
    (compact : HasCompactSupport cutoff) : ℝ :=
  SpatialMultiplier.matrixBound (SpatialMultiplier.compactSymbol grade openUnitDisk cutoff smooth compact) *
    ‖apCellWeakJet L sigma gamma ell dimension grade cell‖

theorem apCellLocalizationConstant_nonnegative (L sigma gamma ell : ℝ) (dimension grade : ℕ) (cell : ℤ)
    (cutoff : Grad.PDEBootstrap.Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff)
    (compact : HasCompactSupport cutoff) :
    0 ≤ apCellLocalizationConstant L sigma gamma ell dimension grade cell cutoff smooth compact :=
  mul_nonneg (Real.sqrt_nonneg _)
    (norm_nonneg (apCellWeakJet L sigma gamma ell dimension grade cell))

theorem apCellLocalized_norm_le (L sigma gamma ell : ℝ) (dimension grade : ℕ) (cell : ℤ)
    (cutoff : Grad.PDEBootstrap.Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff)
    (compact : HasCompactSupport cutoff) (supported : tsupport cutoff ⊆ openUnitDisk)
    (field : apGrade L sigma gamma ell dimension grade) :
    ‖apCellLocalized L sigma gamma ell dimension grade cell cutoff smooth compact supported field‖ ≤
      apCellLocalizationConstant L sigma gamma ell dimension grade cell cutoff smooth compact * ‖field‖ := by
  let mapping := compactScalarExtension dimension grade openUnitDisk openUnitDisk_isOpen
    cutoff smooth compact supported (fun _ => 0) (SpatialMultiplier.constantExponent_antitone grade 0)
  have bound : ‖mapping‖ ≤ SpatialMultiplier.matrixBound
      (SpatialMultiplier.compactSymbol grade openUnitDisk cutoff smooth compact) :=
    extendedMultiplier_opNorm_le dimension grade openUnitDisk openUnitDisk_isOpen
      (SpatialMultiplier.compactSymbol grade openUnitDisk cutoff smooth compact)
      (compactLocalizer openUnitDisk (tsupport cutoff) compact openUnitDisk_isOpen supported)
      (fun _ => 0) (SpatialMultiplier.constantExponent_antitone grade 0)
  exact ((mapping.le_opNorm _).trans (mul_le_mul bound
    ((apCellWeakJet L sigma gamma ell dimension grade cell).le_opNorm field)
    (norm_nonneg _) (Real.sqrt_nonneg _))).trans_eq (mul_assoc _ _ _).symm

theorem apCellLocalized_base (L sigma gamma ell : ℝ) (dimension grade : ℕ) (cell : ℤ)
    (cutoff : Grad.PDEBootstrap.Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff)
    (compact : HasCompactSupport cutoff) (supported : tsupport cutoff ⊆ openUnitDisk)
    (field : apGrade L sigma gamma ell dimension grade) :
    base dimension grade Set.univ (fun _ => 0)
      (apCellLocalized L sigma gamma ell dimension grade cell cutoff smooth compact supported field) =
      fieldExtension (CellValues dimension) openUnitDisk openUnitDisk_isOpen.measurableSet
        (SpatialMultiplier.fieldMultiplier dimension openUnitDisk openUnitDisk_isOpen
          (SpatialMultiplier.derivativeScalar (SpatialMultiplier.compactSymbol grade openUnitDisk cutoff smooth compact)
            (zeroIndex grade))
          (apDiskInjection dimension (apUnscaledCoordinate L sigma gamma ell cell (zeroGradeIndex grade) field))) := by
  have identity := extendedMultiplier_base dimension grade openUnitDisk openUnitDisk_isOpen
    (SpatialMultiplier.compactSymbol grade openUnitDisk cutoff smooth compact)
    (compactLocalizer openUnitDisk (tsupport cutoff) compact openUnitDisk_isOpen supported)
    (fun _ => 0) (SpatialMultiplier.constantExponent_antitone grade 0)
    (apCellWeakJet L sigma gamma ell dimension grade cell field)
  exact identity.trans (congrArg
    (fun value => fieldExtension (CellValues dimension) openUnitDisk openUnitDisk_isOpen.measurableSet
      (SpatialMultiplier.fieldMultiplier dimension openUnitDisk openUnitDisk_isOpen
        (SpatialMultiplier.derivativeScalar (SpatialMultiplier.compactSymbol grade openUnitDisk cutoff smooth compact)
          (zeroIndex grade)) value))
    (apCellWeakJet_base L sigma gamma ell dimension grade cell field))

theorem apCellLocalized_weak (L sigma gamma ell : ℝ) (dimension grade : ℕ) (cell : ℤ)
    (cutoff : Grad.PDEBootstrap.Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff)
    (compact : HasCompactSupport cutoff) (supported : tsupport cutoff ⊆ openUnitDisk)
    (field : apGrade L sigma gamma ell dimension grade) (index : JetIndex grade)
    (testCell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction Set.univ) :
    testPairing dimension Set.univ testCell vector test
      (Realization.recoveredDerivative dimension grade Set.univ (fun _ => 0) index
        (apCellLocalized L sigma gamma ell dimension grade cell cutoff smooth compact supported field)) =
      (-1 : ℂ) ^ degree index * derivativeTestPairing dimension grade Set.univ index testCell vector test
        (base dimension grade Set.univ (fun _ => 0)
          (apCellLocalized L sigma gamma ell dimension grade cell cutoff smooth compact supported field)) :=
  Realization.recoveredDerivative_weak dimension grade Set.univ (fun _ => 0) index _ testCell vector test

end Grad.InteriorLocalization
