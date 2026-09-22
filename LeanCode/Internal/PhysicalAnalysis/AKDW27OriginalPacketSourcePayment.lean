import AKDW26ActualOriginalNormPacket

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace Grad.CartesianStartup.StartupOriginalUnitNormPacket
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.NonlinearProduct
open Grad.OriginalCoreRealization Grad.TensorBootstrap
variable {parameters : PhaseParameters} {length radius : ℝ}

def sourcePayment (grade : ℕ) (scale : ℝ) (packet : StartupOriginalUnitNormPacket parameters length radius) : ℝ :=
  (∑ index : TensorIndex,originalGradeNorm grade (packet.knownTensorCore index.1 index.2))+
    ∑ direction : Fin 2,originalGradeNorm grade (packet.knownFluxCore scale direction)

theorem sourcePayment_nonnegative (grade : ℕ) (scale : ℝ) (packet : StartupOriginalUnitNormPacket parameters length radius) :
    0≤sourcePayment grade scale packet :=
  add_nonneg (Finset.sum_nonneg (fun _ _ => originalGradeNorm_nonnegative _ _))
    (Finset.sum_nonneg (fun _ _ => originalGradeNorm_nonnegative _ _))

theorem knownTensor_paid (grade : ℕ) (scale : ℝ) (packet : StartupOriginalUnitNormPacket parameters length radius) (outer inner : Fin 2) :
    originalGradeNorm grade (packet.knownTensorCore outer inner)≤sourcePayment grade scale packet := by
  have first := Finset.single_le_sum (fun (index : TensorIndex) (_ : index∈Finset.univ) =>
    originalGradeNorm_nonnegative grade (packet.knownTensorCore index.1 index.2)) (Finset.mem_univ (outer,inner))
  exact first.trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => originalGradeNorm_nonnegative _ _)))

theorem knownFlux_paid (grade : ℕ) (scale : ℝ) (packet : StartupOriginalUnitNormPacket parameters length radius) (direction : Fin 2) :
    originalGradeNorm grade (packet.knownFluxCore scale direction)≤sourcePayment grade scale packet := by
  have second := Finset.single_le_sum (fun (index : Fin 2) (_ : index∈Finset.univ) =>
    originalGradeNorm_nonnegative grade (packet.knownFluxCore scale index)) (Finset.mem_univ direction)
  exact second.trans (le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => originalGradeNorm_nonnegative _ _)))

def sourceNorms (grade : ℕ) (packet : StartupOriginalUnitNormPacket parameters length radius) : ℝ :=
  originalGradeNorm grade packet.forceCore+originalGradeNorm grade packet.thirdCore+
    originalGradeNorm grade packet.determinantCore+originalGradeNorm (grade+1) packet.forceCore

/-- Every source remainder is paid by genuine original source norms,
with its fixed constant independent of the coefficient state and w. -/
theorem sourcePayment_bound (parameters : PhaseParameters) (grade : ℕ) (scale : ℝ) :
    ∃ constant : ℝ,0≤constant ∧ ∀ {length radius : ℝ} (packet : StartupOriginalUnitNormPacket parameters length radius),
      sourcePayment grade scale packet≤constant*sourceNorms grade packet := by
  let tensorCertificate := fun index : TensorIndex => startupKnownTensor_core_bound parameters grade index.1 index.2
  let fluxCertificate := fun direction : Fin 2 => startupKnownNativeFluxCore_bound parameters scale grade direction
  let tensorCost := fun index : TensorIndex => (tensorCertificate index).choose
  let fluxCost := fun direction : Fin 2 => (fluxCertificate direction).choose
  have tensor0 (index : TensorIndex) : 0≤tensorCost index := (tensorCertificate index).choose_spec.1
  have flux0 (direction : Fin 2) : 0≤fluxCost direction := (fluxCertificate direction).choose_spec.1
  refine ⟨(∑ index,tensorCost index)+(∑ direction,fluxCost direction),
    add_nonneg (Finset.sum_nonneg (fun index _ => tensor0 index)) (Finset.sum_nonneg (fun direction _ => flux0 direction)),?_⟩
  intro length radius packet
  have tensorPart : originalGradeNorm grade packet.forceCore+originalGradeNorm grade packet.thirdCore≤sourceNorms grade packet := by
    unfold sourceNorms
    linarith only [originalGradeNorm_nonnegative grade packet.determinantCore,originalGradeNorm_nonnegative (grade+1) packet.forceCore]
  have fluxPart : originalGradeNorm grade packet.determinantCore+originalGradeNorm (grade+1) packet.forceCore≤sourceNorms grade packet := by
    unfold sourceNorms
    linarith only [originalGradeNorm_nonnegative grade packet.forceCore,originalGradeNorm_nonnegative grade packet.thirdCore]
  have tensorBound (index : TensorIndex) : originalGradeNorm grade (packet.knownTensorCore index.1 index.2)≤tensorCost index*sourceNorms grade packet := by
    have original := (tensorCertificate index).choose_spec.2 packet.forceCore packet.thirdCore (packet.knownTensorCore index.1 index.2)
      (startupKnownTensor_core_exists parameters packet.forceCore packet.thirdCore index.1 index.2).choose_spec
    exact original.trans (mul_le_mul_of_nonneg_left tensorPart (tensor0 index))
  have fluxBound (direction : Fin 2) : originalGradeNorm grade (packet.knownFluxCore scale direction)≤fluxCost direction*sourceNorms grade packet := by
    have original := (fluxCertificate direction).choose_spec.2 packet.determinantCore packet.forceCore
    exact original.trans (mul_le_mul_of_nonneg_left fluxPart (flux0 direction))
  have combined := add_le_add (Finset.sum_le_sum (fun index (_ : index∈Finset.univ) => tensorBound index))
    (Finset.sum_le_sum (fun direction (_ : direction∈Finset.univ) => fluxBound direction))
  simpa only [sourcePayment,←Finset.sum_mul,←add_mul] using combined

end Grad.CartesianStartup.StartupOriginalUnitNormPacket
