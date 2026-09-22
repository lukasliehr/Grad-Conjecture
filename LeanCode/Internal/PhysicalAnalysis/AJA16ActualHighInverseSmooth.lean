import AJA10SameHighInverseOrbit
import AJA14ActualFullJetTower
import AJA15GenericInverseSmooth

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace Grad.AnnularHighInverseOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit Grad.AnnularInverseCalculus
attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

theorem currentHighInverseOrbit_contDiff :
    ContDiff ℝ ∞ (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) :=
  sameInverse_contDiff
    (currentHighZeroFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (currentHighInverseOrbit_right parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (currentHighInverseOrbit_left parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (currentHighZeroFormOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)

end Grad.AnnularHighInverseOrbit
