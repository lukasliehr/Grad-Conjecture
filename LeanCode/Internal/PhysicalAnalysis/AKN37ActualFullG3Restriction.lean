import AKN36ActualPrimitiveSourceRestriction

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.SourceCollarFullSource Grad.SourceCollarCoefficients Grad.AnnularCurrentSource
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.ConstrainedGrades
open Grad.SourceCollarBulk Grad.AnnularStrongData Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularRestriction Grad.SourceCollarAngular

theorem originalBulkRestriction_of_coefficient {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (lower upper : ℝ) (included : lower ≤ upper) (positiveUpper : 0 < upper)
    (source : DivisionRow dimension lower) (target : DivisionRow dimension upper)
    (same : ∀ᵐ radius ∂volume.restrict (Icc upper 1), ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters grade lower source radius mode =
        originalRowCoefficient parameters grade upper target radius mode) :
    originalBulkRestriction dimension lower upper included source = target := by
  apply lp.ext
  funext mode
  apply Lp.ext
  filter_upwards [originalBulkRestriction_ae dimension lower upper included source,
    same, ae_restrict_mem measurableSet_Icc] with radius restriction actual inside
  rw [restriction mode, ← originalRowCoefficient_weighted parameters grade lower source radius
    (positiveUpper.trans_le inside.1) mode, actual mode,
    originalRowCoefficient_weighted parameters grade upper target radius (positiveUpper.trans_le inside.1) mode]

theorem actualG3Value_restrict (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (lower upper : ℝ) (included : lower ≤ upper) (positiveLower : 0 < lower) (positiveUpper : 0 < upper)
    (boundedLower : lower ≤ 1) (boundedUpper : upper ≤ 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    originalBulkRestriction 1 lower upper included
      (g3ValueRow (order := grade) parameters L rho epsilon field small lower positiveLower boundedLower (by omega)
        (quotientEta parameters (grade + 6) source)) =
      g3ValueRow (order := grade) parameters L rho epsilon field small upper positiveUpper boundedUpper (by omega)
        (quotientEta parameters (grade + 6) source) := by
  apply originalBulkRestriction_of_coefficient parameters grade lower upper included positiveUpper
  filter_upwards [(actualG3Value_same_physical parameters L rho epsilon field small lower positiveLower boundedLower grade source flat).filter_mono
    (ae_mono (collarMeasure_le lower upper included)),
    actualG3Value_same_physical parameters L rho epsilon field small upper positiveUpper boundedUpper grade source flat,
    ae_restrict_mem measurableSet_Icc] with radius first second inside
  intro mode
  exact (first ⟨included.trans inside.1, inside.2⟩ mode).trans (second inside mode).symm

theorem actualOriginalG3Row_restrict (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (lower upper : ℝ) (included : lower ≤ upper) (positiveLower : 0 < lower) (positiveUpper : 0 < upper)
    (boundedLower : lower ≤ 1) (boundedUpper : upper ≤ 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    originalBulkRestriction 1 lower upper included
      (actualOriginalG3Row parameters L rho epsilon field small lower positiveLower boundedLower grade source) =
      actualOriginalG3Row parameters L rho epsilon field small upper positiveUpper boundedUpper grade source := by
  apply lp.ext
  funext mode
  change collarL2Restriction 1 lower upper included
    (actualOriginalG3Row parameters L rho epsilon field small lower positiveLower boundedLower grade source mode) = _
  rw [actualOriginalG3Row, strengthenedG_mode lower _ _
    (fun other => g3AngularRow_mode parameters L rho epsilon field small lower positiveLower boundedLower (by omega) _ other),
    actualOriginalG3Row, strengthenedG_mode upper _ _
    (fun other => g3AngularRow_mode parameters L rho epsilon field small upper positiveUpper boundedUpper (by omega) _ other), map_smul]
  exact congrArg (fun item : RadialL2 1 upper => ((1 + |(mode.1 : ℝ)| : ℝ) : ℂ) • item)
    (congrArg (fun row : DivisionRow 1 upper => row mode)
      (actualG3Value_restrict parameters L rho epsilon field small lower upper included positiveLower positiveUpper boundedLower boundedUpper grade source flat))

end Grad.ExhaustionSourceAllocation
