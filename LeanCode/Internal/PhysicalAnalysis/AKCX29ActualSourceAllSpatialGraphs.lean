import AKCX28ActualSourceOrderedCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualOriginalSourceFirst
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.PDEBootstrap Grad.GenericCarriers
open Grad.ActualOriginalSourceMoments Grad.CartesianStartup Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct Grad.WeakTesting Grad.WeakTesting.Commutation

private theorem scalarSource_orderedDerivative {dimension rank : ℕ}
    (function : Spatial → PhysicalValue dimension) (smooth : ContDiff ℝ ∞ function)
    (vector : PhysicalValue dimension) (word : CartesianWord rank) (point : Spatial) :
    wordDerivative rank word (fun point => inner ℂ vector (function point)) point =
      inner ℂ vector (cartesianDerivative rank word function point) := by
  let mapping := (innerSL ℂ vector).restrictScalars ℝ
  change iteratedFDeriv ℝ rank (mapping ∘ function) point
    (fun position => spatialDirection (word position)) = _
  rw [mapping.iteratedFDeriv_comp_left smooth.contDiffAt
    (by exact_mod_cast (le_top : (rank : ℕ∞) ≤ ⊤))]
  rfl

variable {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)

theorem originalSourceOrderedJoint_weak (rank : ℕ) (word : CartesianWord rank) :
    HasWeakOrderedDerivative dimension openUnitDisk rank word
      (originalSourceJointField parameters field 0) (originalSourceOrderedJoint parameters field rank word) := by
  apply (hasWeakOrderedDerivative_iff_integral dimension openUnitDisk rank word _ _).mpr
  intro cell vector test smooth compact supported
  let raw := originalWeightedSourceCell parameters field cell
  have rawSmooth : ContDiff ℝ ∞ raw := originalWeightedSourceCell_smooth parameters field cell
  have scalarSmooth : ContDiff ℝ ∞ (fun point => inner ℂ vector (raw point)) :=
    ((innerSL ℂ vector).restrictScalars ℝ).contDiff.comp rawSmooth
  have ibp := Grad.RepresentedKernel.WeakDerivatives.orderedScalar_ibp openUnitDisk openUnitDisk_isOpen
    rank word test smooth compact supported (fun point => inner ℂ vector (raw point)) scalarSmooth.contDiffOn
  have derivativeSame : (∫ point in openUnitDisk, test point • inner ℂ vector
      (originalSourceOrderedJoint parameters field rank word point cell)) =
      ∫ point in openUnitDisk, test point • wordDerivative rank word
        (fun point => inner ℂ vector (raw point)) point := by
    apply integral_congr_ae
    filter_upwards [originalSourceOrderedJoint_same parameters field rank word] with point same
    rw [same cell,scalarSource_orderedDerivative raw rawSmooth vector word point]
  rw [derivativeSame,ibp]
  congr 1
  apply integral_congr_ae
  filter_upwards [originalSourceJointField_weightedCell parameters field] with point same
  rw [same cell]

theorem originalSourceOrderedJoint_zero (word : CartesianWord 0) :
    originalSourceOrderedJoint parameters field 0 word = originalSourceJointField parameters field 0 := by
  apply Lp.ext
  filter_upwards [originalSourceOrderedJoint_same parameters field 0 word,
    originalSourceJointField_weightedCell parameters field] with point derivativeSame fieldSame
  apply lp.ext
  funext cell
  rw [derivativeSame cell,fieldSame cell]
  rfl

def originalSourceSpatialGraph (order : ℕ) : GraphGrade dimension order 0 openUnitDisk :=
  startupGraphFromWeak (originalSourceJointField parameters field 0)
    (fun index => originalSourceOrderedJoint parameters field (degree index) (derivativeWord index))
    (originalSourceOrderedJoint_zero parameters field _) (fun index => originalSourceOrderedJoint_weak parameters field (degree index) (derivativeWord index))

theorem originalSourceSpatialGraph_base (order : ℕ) :
    base dimension order openUnitDisk (fun _ => 0) (originalSourceSpatialGraph parameters field order) =
      (originalSourceMoments parameters field).field :=
  startupGraphFromWeak_base _ _ _ _

end Grad.ActualOriginalSourceFirst
