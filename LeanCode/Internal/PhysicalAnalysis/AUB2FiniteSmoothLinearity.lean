import AUB1ActualGlobalRecurrence

noncomputable section
set_option maxHeartbeats 800000
namespace Grad.ActualUniformGlobal
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.ActualFiniteGlobal Grad.OrdinaryDiskFaithfulness Grad.OrdinaryDiskCalculus
attribute [local instance] unitNormedSpace

/-- The actual finite inverse on arbitrary smooth input, with precisely the
five low modes removed by the accepted high projection. -/
def finiteSmoothInverse (parameters : PhaseParameters) (modes : Finset ℤ) (parameter : ℝ)
    (core : ClosedJet 1) : ClosedJet 1 :=
  finiteInverseClosedJet parameters modes parameter (highL2Core core)
    (excludedAngularJet lowAngularModes core) (highL2Projection_core core)

def finiteInverseBulkLinear (modes : Finset ℤ) (parameter : ℝ) : ClosedJet 1 →ₗ[ℂ] DiskL2 1 :=
  highDiskBulk.toLinearMap.comp ((highRobinWeakInverse parameter).toLinearMap.comp
    ((highL2SelectedModes modes).toLinearMap.comp highL2Core))

theorem finiteSmoothInverse_bulk (parameters : PhaseParameters) (modes : Finset ℤ) (parameter : ℝ)
    (core : ClosedJet 1) :
    closedL2Core (finiteSmoothInverse parameters modes parameter core) = finiteInverseBulkLinear modes parameter core :=
  finiteInverseClosedJet_bulk parameters modes parameter (highL2Core core)
    (excludedAngularJet lowAngularModes core) (highL2Projection_core core)

/-- Linearity follows from the actual weak inverse and faithful closed-jet
bulk, so no choice of the qualitative Sobolev representatives can alter it. -/
def finiteSmoothInverseLinear (parameters : PhaseParameters) (modes : Finset ℤ) (parameter : ℝ) :
    ClosedJet 1 →ₗ[ℂ] ClosedJet 1 where
  toFun := finiteSmoothInverse parameters modes parameter
  map_add' := by
    intro first second
    apply closedL2Core_injective
    rw [map_add, finiteSmoothInverse_bulk, finiteSmoothInverse_bulk, finiteSmoothInverse_bulk, map_add]
  map_smul' := by
    intro scalar core
    apply closedL2Core_injective
    rw [map_smul, finiteSmoothInverse_bulk, finiteSmoothInverse_bulk, map_smul]
    rfl

theorem finiteSmoothInverse_H1 (parameters : PhaseParameters) (modes : Finset ℤ) (parameter : ℝ)
    (core : ClosedJet 1) :
    diskCoreInto (finiteSmoothInverseLinear parameters modes parameter core) =
      (highRobinWeakInverse parameter (highL2SelectedModes modes (highL2Core core))).val :=
  finiteInverseClosedJet_H1 parameters modes parameter (highL2Core core)
    (excludedAngularJet lowAngularModes core) (highL2Projection_core core)

theorem finiteSmoothInverse_high_bulk (parameters : PhaseParameters) (modes : Finset ℤ) (parameter : ℝ)
    (core : ClosedJet 1) :
    closedL2Core (finiteSmoothInverseLinear parameters modes parameter core) ∈ highDiskL2 := by
  rw [show closedL2Core (finiteSmoothInverseLinear parameters modes parameter core) =
      finiteInverseBulkLinear modes parameter core from finiteSmoothInverse_bulk parameters modes parameter core]
  exact highDiskBulk_spectral _

end Grad.ActualUniformGlobal
