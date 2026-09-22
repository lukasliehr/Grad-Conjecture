import AJA10SameHighInverseOrbit
import AJA11GenericInverseDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
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

/-- The derivative belongs to the SAME actual AEL inverse orbit on the
unchanged original primitive neighborhood. -/
theorem currentHighInverseOrbit_hasFDerivAt (tau : OrbitParameter) :
    HasFDerivAt (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
      ((inverseSandwich (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)).comp
        ((formRestriction (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)).comp
          (currentHighFormOrbitDerivative parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau))) tau := by
  exact sameInverse_hasFDerivAt
    (currentHighZeroFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (currentHighInverseOrbit_right parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (currentHighInverseOrbit_left parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) tau _
    (currentHighZeroFormOrbit_hasFDerivAt parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau)

end Grad.AnnularHighInverseOrbit
