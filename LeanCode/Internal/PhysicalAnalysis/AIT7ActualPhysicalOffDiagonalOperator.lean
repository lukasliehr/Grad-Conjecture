import AIT6ActualCoupledLowCorrespondence
import AIQ14CompleteHighCrossResponse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCoupledInverse
open Grad.ClosedJets Grad.CartesianState Grad.AnnularReconstruction
open Grad.AnnularCrossMaps Grad.AnnularLowEnergy Grad.AnnularCurrentLow
open Grad.AnnularPhysicalSolution Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy

variable (parameters : PhaseParameters) (lower length compact : ℝ)
  (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
  (widthHalf : parameters.gamma ≤ 1 / 2)
  (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
  (state : RetainedInverseState parameters length compact)
  (highSmall : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters length compact)

/-- Actual upper BF20 entry: the SAME physical high weak solver applied to
(f,qc,rqv,-beta) reconstructed from the original low graph. -/
def actualHighOffDiagonal :
    lowEnergyGraph lower length positive →L[ℂ] CrossHighSpace lower length positive lengthPositive :=
  actualHighCrossResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state highSmall ∘L
    lowToHighCross parameters lower length compact lengthPositive positive lowerHalf state

theorem actualHighOffDiagonal_energy (field : lowEnergyGraph lower length positive) :
    (actualHighOffDiagonal parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state highSmall field).ofLp.1 =
      graphDataEnergySolution parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state highSmall
        ((lowToHighCross parameters lower length compact lengthPositive positive lowerHalf state field).toGraphKnown parameters lower) := by
  exact actualHighCrossResponse_energy parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state highSmall _

theorem actualHighOffDiagonal_flux (field : lowEnergyGraph lower length positive) :
    (actualHighOffDiagonal parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state highSmall field).ofLp.2 =
      graphDataPhysicalFlux parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state highSmall
        ((lowToHighCross parameters lower length compact lengthPositive positive lowerHalf state field).toGraphKnown parameters lower) := by
  exact actualHighCrossResponse_flux parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state highSmall _

/-- The actual full BF20 operator on the complete original Hilbert graph.
Both entries are the accepted physical responses; no inverse is a premise. -/
def actualCoupledOffDiagonal :
    CoupledSpace lower length positive lengthPositive →L[ℂ] CoupledSpace lower length positive lengthPositive :=
  hilbertOffDiagonal
    (actualHighOffDiagonal parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state highSmall)
    (actualLowOffDiagonal parameters lower length compact lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state)

theorem actualCoupledOffDiagonal_high (field : CoupledSpace lower length positive lengthPositive) :
    (actualCoupledOffDiagonal parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state highSmall field).ofLp.1 =
      actualHighOffDiagonal parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state highSmall field.ofLp.2 := rfl

theorem actualCoupledOffDiagonal_low (field : CoupledSpace lower length positive lengthPositive) :
    (actualCoupledOffDiagonal parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state highSmall field).ofLp.2 =
      actualLowOffDiagonal parameters lower length compact lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state field.ofLp.1 := rfl

end Grad.AnnularCoupledInverse
