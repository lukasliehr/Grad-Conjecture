import AIM3CompletedDerivatives
import ANR5CompletedGreen

noncomputable section
namespace Grad.OrdinaryDiskCalculus
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.NonlinearQuotientBounds
attribute [local instance] unitNormedSpace

/-- The order-one ordinary closure is literally the already constructed
full-disk H1 carrier, with its original Cartesian coordinates. -/
def unitH1 : unitDiskSobolev 1 →L[ℂ] diskGrade := ContinuousLinearMap.id ℂ diskGrade

theorem unitH1_core (core : ClosedJet 1) : unitH1 (unitDiskCoreInto 1 core) = diskCoreInto core := rfl

def unitToH1 (grade : ℕ) : unitDiskSobolev (grade + 1) →L[ℂ] diskGrade :=
  unitH1.comp (unitLower (show 1 ≤ grade + 1 by omega))

theorem unitToH1_core (grade : ℕ) (core : ClosedJet 1) :
    unitToH1 grade (unitDiskCoreInto (grade + 1) core) = diskCoreInto core :=
  (congrArg unitH1 (unitLower_core (show 1 ≤ grade + 1 by omega) core)).trans (unitH1_core core)

theorem unitToH1_bulk (grade : ℕ) (field : unitDiskSobolev (grade + 1)) :
    diskBulk (unitToH1 grade field) = unitDiskBulk (grade + 1) field := by
  apply isClosed_property (unitDiskCoreInto_denseRange (grade + 1))
    (isClosed_eq (diskBulk.continuous.comp (unitToH1 grade).continuous)
      (unitDiskBulk (grade + 1)).continuous) _ field
  intro core
  exact (congrArg diskBulk (unitToH1_core grade core)).trans
    ((Grad.CircularHighWeak.diskBulk_core core).trans (unitDiskBulk_core (grade + 1) core).symm)

/-- The completed ordinary partial is the genuine weak derivative of the
same disk H1 bulk, rather than an unrelated high-grade coordinate. -/
theorem unitPartial_bulk (grade : ℕ) (direction : Fin 2) (field : unitDiskSobolev (grade + 1)) :
    unitDiskBulk grade (unitPartial grade direction field) = diskPartial direction (unitToH1 grade field) := by
  apply isClosed_property (unitDiskCoreInto_denseRange (grade + 1))
    (isClosed_eq ((unitDiskBulk grade).continuous.comp (unitPartial grade direction).continuous)
      ((diskPartial direction).continuous.comp (unitToH1 grade).continuous)) _ field
  intro core
  exact (congrArg (unitDiskBulk grade) (unitPartial_core grade direction core)).trans
    ((unitDiskBulk_core grade (partialJet direction core)).trans
      ((diskPartial_core direction core).symm.trans
        (congrArg (diskPartial direction) (unitToH1_core grade core).symm)))

end Grad.OrdinaryDiskCalculus
