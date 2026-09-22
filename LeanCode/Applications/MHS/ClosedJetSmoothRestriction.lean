import ClosedJetOrthogonal

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace Grad.Constraints

open Grad.ClosedJets Grad.RepresentedKernel.SpatialProduct

theorem listDerivative_eqOn {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set SpatialPlane} (openDomain : IsOpen domain)
    {first second : SpatialPlane → Value} (agree : EqOn first second domain)
    (word : List (Fin 2)) :
    EqOn (listDerivative word first) (listDerivative word second) domain := by
  induction word with
  | nil => exact agree
  | cons direction rest inductionHypothesis =>
    exact directionDerivative_congr openDomain direction inductionHypothesis

def globalClosedValue {dimension : ℕ} (field : SpatialPlane → ComplexEuclidean dimension)
    (continuous : Continuous field) : C(ClosedDisk, ComplexEuclidean dimension) :=
  ⟨fun point => field point.val, continuous.comp continuous_subtype_val⟩

theorem globalClosedValue_lift_eqOn {dimension : ℕ}
    (field : SpatialPlane → ComplexEuclidean dimension) (continuous : Continuous field) :
    EqOn (closedDiskLift (globalClosedValue field continuous)) field openUnitDisk := by
  intro point pointIn
  simp only [closedDiskLift, openDiskMembershipClosed point pointIn, dite_true]
  rfl

def globalClosedDerivative {dimension : ℕ} (field : SpatialPlane → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ field) (order : ℕ) (word : CartesianWord order) :
    C(ClosedDisk, ComplexEuclidean dimension) :=
  globalClosedValue (listDerivative (List.ofFn word) field)
    ((contDiffOn_univ.mp (listDerivative_smooth isOpen_univ (List.ofFn word)
      smooth.contDiffOn)).continuous)

theorem globalClosedDerivative_spec {dimension : ℕ}
    (field : SpatialPlane → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (order : ℕ) (word : CartesianWord order) :
    IsCartesianExtension (globalClosedValue field smooth.continuous) order word
      (globalClosedDerivative field smooth order word) := by
  intro point pointIn
  have liftedSmooth : ContDiffOn ℝ ∞
      (closedDiskLift (globalClosedValue field smooth.continuous)) openUnitDisk :=
    smooth.contDiffOn.congr (globalClosedValue_lift_eqOn field smooth.continuous)
  have derivativeAgreement := listDerivative_eqOn openUnitDisk_isOpen
    (globalClosedValue_lift_eqOn field smooth.continuous).symm (List.ofFn word)
  exact (derivativeAgreement pointIn).trans
    (listDerivative_ofFn openUnitDisk_isOpen order word liftedSmooth pointIn)

/-- Restriction of a genuine global smooth function, with every literal
Cartesian boundary derivative retained. -/
def globalClosedJet {dimension : ℕ} (field : SpatialPlane → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ field) : ClosedJet dimension where
  value := globalClosedValue field smooth.continuous
  smoothInterior := smooth.contDiffOn.congr
    (globalClosedValue_lift_eqOn field smooth.continuous)
  derivativeExists order word :=
    ⟨globalClosedDerivative field smooth order word, globalClosedDerivative_spec field smooth order word⟩

@[simp] theorem globalClosedJet_value {dimension : ℕ}
    (field : SpatialPlane → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (point : ClosedDisk) : (globalClosedJet field smooth).value point = field point.val := rfl

theorem globalClosedJet_derivative {dimension order : ℕ}
    (field : SpatialPlane → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (word : CartesianWord order) (point : ClosedDisk) :
    closedDerivative (globalClosedJet field smooth) order word point =
      cartesianDerivative order word field point.val := by
  have chosenEquality : closedDerivative (globalClosedJet field smooth) order word =
      globalClosedDerivative field smooth order word :=
    (cartesianExtension_unique _ order word _ (globalClosedDerivative_spec field smooth order word)).symm
  rw [chosenEquality]
  exact listDerivative_ofFn isOpen_univ order word smooth.contDiffOn (mem_univ _)

theorem globalClosedJet_eq_of_restriction {dimension : ℕ}
    (field : SpatialPlane → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (original : ClosedJet dimension)
    (agrees : ∀ point : ClosedDisk, field point.val = original.value point) :
    globalClosedJet field smooth = original := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  exact agrees

end Grad.Constraints
