import AUB9ActualCompletedInverse

noncomputable section
set_option maxHeartbeats 1200000
namespace Grad.ActualUniformGlobal
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.OrdinaryDiskFaithfulness Grad.OrdinaryDiskCalculus
attribute [local instance] unitNormedSpace

/-- Every ordinary grade of the same actual all-mode inverse. -/
def smoothInverseFamily (parameters : PhaseParameters) (parameter : ℝ) (core : ClosedJet 1)
    (grade : ℕ) : unitDiskSobolev grade :=
  unitLower (Nat.le_add_right grade 2)
    (actualCompletedInverse grade parameters parameter (unitDiskCoreInto grade core))

theorem smoothInverseFamily_bulk (parameters : PhaseParameters) (parameter : ℝ) (core : ClosedJet 1)
    (grade : ℕ) :
    unitDiskBulk grade (smoothInverseFamily parameters parameter core grade) =
      fullWeakBulkOperator parameter (closedL2Core core) :=
  (unitLower_bulk (Nat.le_add_right grade 2) _).trans
    ((actualCompletedInverse_bulk grade parameters parameter _).trans
      (congrArg (fullWeakBulkOperator parameter) (unitDiskBulk_core grade core)))

/-- A single genuine smooth closed jet, chosen before the Sobolev grade,
representing the full actual inverse of the high part of the source. -/
def actualSmoothInverse (parameters : PhaseParameters) (parameter : ℝ) (core : ClosedJet 1) : ClosedJet 1 :=
  sameBulkClosedJet parameters (smoothInverseFamily parameters parameter core)
    (fullWeakBulkOperator parameter (closedL2Core core))
    (smoothInverseFamily_bulk parameters parameter core)

theorem actualSmoothInverse_bulk (parameters : PhaseParameters) (parameter : ℝ) (core : ClosedJet 1) :
    closedL2Core (actualSmoothInverse parameters parameter core) =
      fullWeakBulkOperator parameter (closedL2Core core) :=
  sameBulkClosedJet_bulk parameters _ _ _

theorem actualSmoothInverse_grade (parameters : PhaseParameters) (parameter : ℝ) (core : ClosedJet 1)
    (grade : ℕ) :
    unitDiskCoreInto (grade + 2) (actualSmoothInverse parameters parameter core) =
      actualCompletedInverse grade parameters parameter (unitDiskCoreInto grade core) := by
  apply ordinaryBulk_injective parameters (grade + 2)
  exact (unitDiskBulk_core (grade + 2) _).trans
    ((actualSmoothInverse_bulk parameters parameter core).trans
      ((congrArg (fullWeakBulkOperator parameter) (unitDiskBulk_core grade core).symm).trans
        (actualCompletedInverse_bulk grade parameters parameter _).symm))

theorem actualSmoothInverse_H1 (parameters : PhaseParameters) (parameter : ℝ) (core : ClosedJet 1) :
    diskCoreInto (actualSmoothInverse parameters parameter core) =
      (highRobinWeakInverse parameter (highL2Core core)).val := by
  apply diskBulk_injective
  exact (Grad.CircularHighWeak.diskBulk_core _).trans
    (actualSmoothInverse_bulk parameters parameter core)

theorem actualSmoothInverse_bound (grade : ℕ) (ceiling : ℝ) (parameters : PhaseParameters)
    (parameter : ℝ) (bounded : |parameter| ≤ ceiling) (core : ClosedJet 1) :
    ‖unitDiskCoreInto (grade + 2) (actualSmoothInverse parameters parameter core)‖ ≤
      finiteInverseConstant grade ceiling * ‖unitDiskCoreInto grade core‖ :=
  (congrArg (fun field : unitDiskSobolev (grade + 2) => ‖field‖)
    (actualSmoothInverse_grade parameters parameter core grade)).le.trans
    (actualCompletedInverse_bound grade ceiling parameters parameter bounded _)

def actualSmoothInverseLinear (parameters : PhaseParameters) (parameter : ℝ) : ClosedJet 1 →ₗ[ℂ] ClosedJet 1 :=
  linearOfBulk closedL2Core closedL2Core_injective
    ((fullWeakBulkOperator parameter).toLinearMap.comp closedL2Core)
    (actualSmoothInverse parameters parameter) (actualSmoothInverse_bulk parameters parameter)

end Grad.ActualUniformGlobal
