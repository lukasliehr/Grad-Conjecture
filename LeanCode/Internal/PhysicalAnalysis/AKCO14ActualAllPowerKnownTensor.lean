import AKCO9ActualSignedPrincipalTensor
import AKCO13SignedOriginalPhaseTransfer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState Grad.WeightedJets
open Grad.ActualOriginalSourceFirst Grad.ActualScalarWeakEquations Grad.SpatialDilation
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.Constraints Grad.Constraints.Gauges

structure StartupSignedFirstFamily (dimension : ℕ) (L ell : ℝ) extends StartupSignedFamily dimension L ell where
  first : ℕ → StartupFirst dimension
  firstBase : ∀ power, base dimension 1 openUnitDisk (fun _ => 0) (first power) = moment power

namespace StartupSignedFirstFamily
variable {input output : ℕ} {L ell : ℝ}

def apply (family : StartupSignedFirstFamily input L ell) (operator : StartupSignedAction input output L ell) :
    StartupSignedFirstFamily output L ell where
  toStartupSignedFamily := operator.action family.toStartupSignedFamily
  first power := (operator.preservesFirst family.toStartupSignedFamily power
    (fun q _ => ⟨family.first q,family.firstBase q⟩)).choose
  firstBase power := (operator.preservesFirst family.toStartupSignedFamily power
    (fun q _ => ⟨family.first q,family.firstBase q⟩)).choose_spec

def add (first second : StartupSignedFirstFamily input L ell) : StartupSignedFirstFamily input L ell where
  toStartupSignedFamily := first.toStartupSignedFamily.add second.toStartupSignedFamily
  first power := first.first power + second.first power
  firstBase power := by rw [map_add,first.firstBase,second.firstBase]; rfl

def smul (family : StartupSignedFirstFamily input L ell) (scalar : ℂ) : StartupSignedFirstFamily input L ell where
  toStartupSignedFamily := family.toStartupSignedFamily.smul scalar
  first power := scalar • family.first power
  firstBase power := by rw [map_smul,family.firstBase]; rfl

def source {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (length : ℝ) (scale : Scale) : StartupSignedFirstFamily dimension length scale.val where
  field := base dimension 1 openUnitDisk (fun _ => 0) (scaledOriginalSourceFirst parameters field scale)
  moment power := base dimension 1 openUnitDisk (fun _ => 0) (originalSignedAxialFirst parameters field length scale power)
  same := originalSignedAxialFirst_same parameters field length scale
  first power := originalSignedAxialFirst parameters field length scale power
  firstBase _ := rfl

/-- Genuine known force with the original corrected radial projector. -/
def knownForce (parameters : PhaseParameters) (data : SmoothQuotient parameters)
    (length : ℝ) (positive : 0 < length) : StartupSignedFirstFamily 2 length (min 1 length / 4) :=
  (source parameters (cartesianSourceVector data) length (originalStartupScale length positive)).apply StartupSignedAction.qrad

def knownThird (parameters : PhaseParameters) (data : SmoothQuotient parameters)
    (length : ℝ) (positive : 0 < length) : StartupSignedFirstFamily 1 length (min 1 length / 4) :=
  (source parameters (data 3) length (originalStartupScale length positive)).smul (length⁻¹ : ℂ)

def determinant (parameters : PhaseParameters) (data : SmoothQuotient parameters)
    (length : ℝ) (positive : 0 < length) : StartupSignedFirstFamily 1 length (min 1 length / 4) :=
  (source parameters (data 2) length (originalStartupScale length positive)).smul (((min 1 length / 4)/length : ℝ) : ℂ)

/-- Actual ER known tensor at every signed power, with its existing
fixed inverse-covector factors and source flux correction. -/
def knownTensor (force : StartupSignedFirstFamily 2 L ell) (third : StartupSignedFirstFamily 1 L ell)
    (outer inner : Fin 2) : StartupSignedFirstFamily 3 L ell :=
  ((((force.smul (-1)).apply (StartupSignedAction.value planarInclusionMap)).apply
    (StartupSignedAction.principalFixed outer inner 0)).add
    ((third.apply (StartupSignedAction.value toroidalInclusionMap)).apply
      (StartupSignedAction.principalFixed outer inner 1))).add
    ((((force.apply ((StartupSignedAction.value quarterValueMap).comp StartupSignedAction.average)).smul (1/2)).apply
      (StartupSignedAction.value planarInclusionMap)).apply (StartupSignedAction.principalFixed outer inner 2))

theorem knownTensor_field (force : StartupSignedFirstFamily 2 L ell) (third : StartupSignedFirstFamily 1 L ell)
    (outer inner : Fin 2) :
    (knownTensor force third outer inner).field =
      startupThreeRowTensor (-force.field) third.field (startupERSourceFlux force.field) outer inner := by
  unfold startupThreeRowTensor
  rw [Fin.sum_univ_three]
  change startupPrincipalFixedKernel outer inner 0
      (originalValueKernel planarInclusionMap ((-1 : ℂ) • force.field)) +
    startupPrincipalFixedKernel outer inner 1 (originalValueKernel toroidalInclusionMap third.field) +
    startupPrincipalFixedKernel outer inner 2
      (originalValueKernel planarInclusionMap (startupERSourceFlux force.field)) = _
  rw [neg_one_smul]
  rfl

end StartupSignedFirstFamily
end Grad.CartesianStartup
