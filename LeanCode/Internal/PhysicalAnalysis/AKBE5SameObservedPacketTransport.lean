import AKBE4OriginalAngularWeakEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.ActualCartesianDescent Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.Allocation

/-- Change only the label of an equal completed row. The entire family of
physical curves is retained, so incoming-data transport does not choose a
new representative of the solved field. -/
def reindexPhysicalRow {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {first second : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive first)
    (same : first = second) : SmoothLowPhysicalRow parameters lower positive second where
  curve := curves.curve
  smooth := curves.smooth
  same := by
    rw [← same]
    exact curves.same

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (state : AnnularReconstructionState parameters length compact)
    {first second : DivisionRow 7 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive first) (same : first = second)

theorem reindexPhysicalRow_covariantField :
    ((reindexPhysicalRow curves same).covariant parameters length compact lower positive bounded state).cartesianCovariant.fullField bounded =
      (curves.covariant parameters length compact lower positive bounded state).cartesianCovariant.fullField bounded := by
  cases same
  rfl

theorem reindexPhysicalRow_covariantCartesian :
    ((reindexPhysicalRow curves same).covariant parameters length compact lower positive bounded state).cartesianCovariant.cartesianField bounded =
      (curves.covariant parameters length compact lower positive bounded state).cartesianCovariant.cartesianField bounded := by
  cases same
  rfl

theorem reindexPhysicalRow_originalPhysical (rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length) :
    (((reindexPhysicalRow curves same).covariant parameters length compact lower positive bounded state).physicalUFromPolar
      parameters length rho epsilon base small lower positive bounded).fullField bounded =
      ((curves.covariant parameters length compact lower positive bounded state).physicalUFromPolar
        parameters length rho epsilon base small lower positive bounded).fullField bounded := by
  cases same
  rfl

end Grad.ActualCartesianWeakEquations
