import AJE11GenuineGraphOuterTupleMap
import AJD7ActualCrossKnownFunctionalOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped ContDiff
namespace Grad.AnnularStrongOrbit
open Grad.AnnularKernelOrbit Grad.AnnularHighInverseOrbit Grad.AnnularCrossOrbit

theorem mappedOrbit_hasFDerivAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (mapping : E →L[ℝ] F)
    (family : OrbitParameter → E) (angular cell : E) (tau : OrbitParameter)
    (derivative : HasFDerivAt family (orbitColumns angular cell) tau) :
    HasFDerivAt (fun point => mapping (family point))
      (orbitColumns (mapping angular) (mapping cell)) tau := by
  have composed := HasFDerivAt.comp (𝕜 := ℝ) (E := OrbitParameter) (F := E) (G := F) tau
    (ContinuousLinearMap.hasFDerivAt (E := E) (F := F) mapping) derivative
  exact composed.congr_fderiv (orbitColumns_comp (E := E) (F := F) mapping angular cell)

section RealInput
variable {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

/-- Coefficient operators act on an arbitrary real source graph carrier
through its actual complex-valued data coordinate. -/
def realInputPrecompose (input : X →L[ℝ] E) :
    (E →L[ℂ] F) →L[ℝ] (X →L[ℝ] F) :=
  ((ContinuousLinearMap.compL ℝ X E F).flip input).comp
    (ContinuousLinearMap.restrictScalarsIsometry ℂ E F ℝ ℝ).toContinuousLinearMap

theorem realInputPrecompose_apply (input : X →L[ℝ] E) (mapping : E →L[ℂ] F) (source : X) :
    realInputPrecompose input mapping source = mapping (input source) := rfl

theorem realInputPrecompose_hasFDerivAt (input : X →L[ℝ] E)
    (family : OrbitParameter → E →L[ℂ] F) (angular cell : E →L[ℂ] F) (tau : OrbitParameter)
    (derivative : HasFDerivAt family (orbitColumns angular cell) tau) :
    HasFDerivAt (fun point => realInputPrecompose input (family point))
      (orbitColumns (realInputPrecompose input angular) (realInputPrecompose input cell)) tau := by
  have composed := (realInputPrecompose input).hasFDerivAt.comp tau derivative
  exact composed.congr_fderiv (orbitColumns_comp (realInputPrecompose input) angular cell)

theorem realInputPrecompose_bound (input : X →L[ℝ] E) (mapping : E →L[ℂ] F) :
    ‖realInputPrecompose input mapping‖ ≤ ‖mapping‖ * ‖input‖ := by
  change ‖(mapping.restrictScalars ℝ).comp input‖ ≤ _
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (by rw [ContinuousLinearMap.norm_restrictScalars])

end RealInput

section Pairing
variable {X V D : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup D] [InnerProductSpace ℂ D]
local instance sharedPairingRealInner : InnerProductSpace ℝ D := InnerProductSpace.rclikeToReal ℂ D

/-- Pair actual real source-coordinate operators with the original energy
test packet. This shares the checked AJD real pairing. -/
def pairedRealOperator (test : V →L[ℝ] D) :
    (X →L[ℝ] D) →L[ℝ] (X →L[ℝ] V →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ X D (V →L[ℝ] ℝ)) (realTestPairing test)

theorem pairedRealOperator_apply (test : V →L[ℝ] D) (mapping : X →L[ℝ] D) (source : X) (field : V) :
    pairedRealOperator test mapping source field = (inner ℂ (test field) (mapping source)).re :=
  inner_re_symm (𝕜 := ℂ) _ _

theorem pairedRealOperator_hasFDerivAt (test : V →L[ℝ] D)
    (family : OrbitParameter → X →L[ℝ] D) (angular cell : X →L[ℝ] D) (tau : OrbitParameter)
    (derivative : HasFDerivAt family (orbitColumns angular cell) tau) :
    HasFDerivAt (fun point => pairedRealOperator test (family point))
      (orbitColumns (pairedRealOperator test angular) (pairedRealOperator test cell)) tau := by
  have composed := HasFDerivAt.comp (𝕜 := ℝ) (E := OrbitParameter)
    (F := X →L[ℝ] D) (G := X →L[ℝ] V →L[ℝ] ℝ) tau
    (ContinuousLinearMap.hasFDerivAt (E := X →L[ℝ] D) (F := X →L[ℝ] V →L[ℝ] ℝ)
      (pairedRealOperator (X := X) test)) derivative
  exact composed.congr_fderiv (orbitColumns_comp (E := X →L[ℝ] D) (F := X →L[ℝ] V →L[ℝ] ℝ)
    (pairedRealOperator (X := X) (V := V) (D := D) test) angular cell)

end Pairing

section Tower
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def constantOrbitJet (value : E) (angular cell : ℕ) (_tau : OrbitParameter) : E :=
  if angular + cell = 0 then value else 0

theorem constantOrbitJet_hasFDerivAt (value : E) (angular cell : ℕ) (tau : OrbitParameter) :
    HasFDerivAt (constantOrbitJet value angular cell)
      (orbitColumns (constantOrbitJet value (angular + 1) cell tau)
        (constantOrbitJet value angular (cell + 1) tau)) tau := by
  have derivative : HasFDerivAt (fun _ : OrbitParameter => if angular + cell = 0 then value else 0)
      (0 : OrbitParameter →L[ℝ] E) tau := hasFDerivAt_const (if angular + cell = 0 then value else 0) tau
  change HasFDerivAt (fun _ : OrbitParameter => if angular + cell = 0 then value else 0) _ tau
  apply derivative.congr_fderiv
  apply ContinuousLinearMap.ext
  intro step
  simp [constantOrbitJet,orbitColumns_apply]

theorem differenceOrbit_hasFDerivAt (first second : OrbitParameter → E)
    (firstAngular firstCell secondAngular secondCell : E) (tau : OrbitParameter)
    (hf : HasFDerivAt first (orbitColumns firstAngular firstCell) tau)
    (hg : HasFDerivAt second (orbitColumns secondAngular secondCell) tau) :
    HasFDerivAt (fun point => first point - second point)
      (orbitColumns (firstAngular - secondAngular) (firstCell - secondCell)) tau := by
  have difference := hf.sub hg
  apply difference.congr_fderiv
  apply ContinuousLinearMap.ext
  intro step
  change (step.1 • firstAngular + step.2 • firstCell) - (step.1 • secondAngular + step.2 • secondCell) = _
  simp only [orbitColumns_apply,smul_sub]
  abel

end Tower
end Grad.AnnularStrongOrbit
