import AKDW19SameAnnularCirclePlanarNorm
import AKDW17AffineLowerEndpointTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open MeasureTheory
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.CellWeights

/-- Actual phase multiplication respects an affine split of the SAME
field, regardless of how its natural moments were constructed. -/
theorem startupScaledPhaseFirstField_affine (sigma gamma scale : ℝ)
    (nonnegative : 0≤gamma) (scaleNonnegative : 0≤scale) (scaleOne : scale≤1)
    (direction : Fin 2) (scalar : ℂ) (field first second moment firstMoment secondMoment : StartupL2 3)
    (fieldSame : field=scalar • first+second)
    (momentSame : StartupRadialRelated (fun cell _ => cellWeight cell) moment field)
    (firstSame : StartupRadialRelated (fun cell _ => cellWeight cell) firstMoment first)
    (secondSame : StartupRadialRelated (fun cell _ => cellWeight cell) secondMoment second) :
    startupScaledPhaseFirstField sigma gamma scale nonnegative scaleNonnegative scaleOne direction moment=
      scalar • startupScaledPhaseFirstField sigma gamma scale nonnegative scaleNonnegative scaleOne direction firstMoment+
        startupScaledPhaseFirstField sigma gamma scale nonnegative scaleNonnegative scaleOne direction secondMoment := by
  apply Lp.ext
  filter_upwards [startupScaledPhaseFirstField_same sigma gamma scale nonnegative scaleNonnegative scaleOne direction field moment momentSame,
    startupScaledPhaseFirstField_same sigma gamma scale nonnegative scaleNonnegative scaleOne direction first firstMoment firstSame,
    startupScaledPhaseFirstField_same sigma gamma scale nonnegative scaleNonnegative scaleOne direction second secondMoment secondSame,
    Lp.coeFn_add (scalar • first) second,Lp.coeFn_smul scalar first,
    Lp.coeFn_add (scalar • startupScaledPhaseFirstField sigma gamma scale nonnegative scaleNonnegative scaleOne direction firstMoment)
      (startupScaledPhaseFirstField sigma gamma scale nonnegative scaleNonnegative scaleOne direction secondMoment),
    Lp.coeFn_smul scalar (startupScaledPhaseFirstField sigma gamma scale nonnegative scaleNonnegative scaleOne direction firstMoment)]
    with point actual one two inputAdd inputScale outputAdd outputScale
  apply lp.ext
  funext cell
  rw [actual cell,outputAdd,fieldSame,inputAdd]
  simp only [Pi.add_apply]
  rw [inputScale,outputScale]
  simp only [Pi.add_apply,Pi.smul_apply,lp.coeFn_add,lp.coeFn_smul,one cell,two cell,smul_add]
  exact congrArg (fun value => value+startupScaledPhaseSlope sigma gamma scale cell direction point • second point cell)
    (smul_comm _ _ _)

end Grad.CartesianStartup
