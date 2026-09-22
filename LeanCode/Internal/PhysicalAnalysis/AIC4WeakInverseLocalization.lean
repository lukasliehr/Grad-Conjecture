import AIC3InteriorCutoff
import ANH19PhysicalConsumer

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.InteriorLocalization
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.WeightedJets Grad.WeightedJets.ZeroExtension Grad.CircularHighWeak

/-- Genuine distributional H1 jet of the actual AN18 energy-space field. -/
def diskWeakJet : diskGrade →L[ℂ] WJet 1 1 openUnitDisk (fun _ => 0) :=
  (apCellWeakJet 1 0 0 1 1 1 0).comp diskGrade.subtypeL

theorem diskWeakJet_base (field : diskGrade) :
    base 1 1 openUnitDisk (fun _ => 0) (diskWeakJet field) = apDiskInjection 1 (diskBulk field) :=
  apCellWeakJet_base 1 0 0 1 1 1 0 field.val

/-- The cutoff of the actual full-disk H1 field, extended by zero to the
plane. It remains a genuine H1 field, with no boundary delta term. -/
def diskInterior : diskGrade →L[ℂ] WJet 1 1 Set.univ (fun _ => 0) :=
  (interiorAPCell 1 0 0 1 1 1 0).comp diskGrade.subtypeL

def diskInteriorConstant : ℝ :=
  apCellLocalizationConstant 1 0 0 1 1 1 0 interiorCutoff.toFun interiorCutoff.smooth interiorCutoff.compact

theorem diskInteriorConstant_nonnegative : 0 ≤ diskInteriorConstant :=
  apCellLocalizationConstant_nonnegative 1 0 0 1 1 1 0 _ _ _

theorem diskInterior_bound (field : diskGrade) :
    ‖diskInterior field‖ ≤ diskInteriorConstant * ‖field‖ :=
  interiorAPCell_bound 1 0 0 1 1 1 0 field.val

/-- Fixed localizer applied to the constructed weak inverse, with a
constant independent of k and the actual high L2 source. -/
def localizedWeakInverse (parameter : ℝ) : highDiskL2 →L[ℂ] WJet 1 1 Set.univ (fun _ => 0) :=
  diskInterior.comp (highDiskGrade.subtypeL.comp (highRobinWeakInverse parameter))

theorem localizedWeakInverse_bound (parameter : ℝ) (source : highDiskL2) :
    ‖localizedWeakInverse parameter source‖ ≤ (2 * diskInteriorConstant) * ‖source‖ := by
  exact ((diskInterior_bound (highRobinWeakInverse parameter source).val).trans
    (mul_le_mul_of_nonneg_left (weakSolution_bound parameter source) diskInteriorConstant_nonnegative)).trans_eq
    (by ring)

theorem localizedWeakInverse_base (parameter : ℝ) (source : highDiskL2) :
    base 1 1 Set.univ (fun _ => 0) (localizedWeakInverse parameter source) =
      fieldExtension (CellValues 1) openUnitDisk openUnitDisk_isOpen.measurableSet
        (SpatialMultiplier.fieldMultiplier 1 openUnitDisk openUnitDisk_isOpen
          (SpatialMultiplier.derivativeScalar
            (SpatialMultiplier.compactSymbol 1 openUnitDisk interiorCutoff.toFun
              interiorCutoff.smooth interiorCutoff.compact) (zeroIndex 1))
          (apDiskInjection 1 (highDiskBulk (highRobinWeakInverse parameter source)))) :=
  apCellLocalized_base 1 0 0 1 1 1 0 interiorCutoff.toFun interiorCutoff.smooth
    interiorCutoff.compact interiorCutoff_supported (highRobinWeakInverse parameter source).val.val

theorem localizedWeakInverse_weak (parameter : ℝ) (source : highDiskL2)
    (index : JetIndex 1) (cell : ℤ) (vector : PhysicalValue 1) (test : TestFunction Set.univ) :
    testPairing 1 Set.univ cell vector test
      (Realization.recoveredDerivative 1 1 Set.univ (fun _ => 0) index
        (localizedWeakInverse parameter source)) =
      (-1 : ℂ) ^ degree index * derivativeTestPairing 1 1 Set.univ index cell vector test
        (base 1 1 Set.univ (fun _ => 0) (localizedWeakInverse parameter source)) :=
  Realization.recoveredDerivative_weak 1 1 Set.univ (fun _ => 0) index _ cell vector test

end Grad.InteriorLocalization
