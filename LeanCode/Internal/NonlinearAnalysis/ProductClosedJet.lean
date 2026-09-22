import ProductInterface
import ClosedJetSmoothExtension

noncomputable section

open scoped ContDiff

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.Constraints

def jetMultilinearSmoothField {arity outputDimension : ℕ} {dimensions : Fin arity → ℕ}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ClosedJet (dimensions index))
    (point : SpatialPlane) : ComplexEuclidean outputDimension :=
  multiplication (fun index => smoothClosedExtension (fields index) point)

theorem jetMultilinearSmoothField_smooth {arity outputDimension : ℕ} {dimensions : Fin arity → ℕ}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ClosedJet (dimensions index)) :
    ContDiff ℝ ∞ (jetMultilinearSmoothField multiplication fields) := by
  exact (multiplication.restrictScalars ℝ).contDiff.comp
    (contDiff_pi.mpr (fun index => smoothClosedExtension_smooth (fields index)))

/-- The actual pointwise physical multiplication of closed jets, constructed
from the accepted global extension and then restricted back exactly. -/
def jetMultilinearProduct {arity outputDimension : ℕ} {dimensions : Fin arity → ℕ}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ClosedJet (dimensions index)) : ClosedJet outputDimension :=
  globalClosedJet (jetMultilinearSmoothField multiplication fields)
    (jetMultilinearSmoothField_smooth multiplication fields)

theorem jetMultilinearProduct_value {arity outputDimension : ℕ} {dimensions : Fin arity → ℕ}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ClosedJet (dimensions index)) (point : ClosedDisk) :
    (jetMultilinearProduct multiplication fields).value point =
      multiplication (fun index => (fields index).value point) := by
  simp only [jetMultilinearProduct, globalClosedJet_value, jetMultilinearSmoothField,
    smoothClosedExtension_value]

theorem jetMultilinearProduct_derivative {arity outputDimension order : ℕ}
    {dimensions : Fin arity → ℕ}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ClosedJet (dimensions index))
    (word : CartesianWord order) (point : ClosedDisk) :
    closedDerivative (jetMultilinearProduct multiplication fields) order word point =
      cartesianDerivative order word (jetMultilinearSmoothField multiplication fields) point.val :=
  globalClosedJet_derivative _ _ word point

end Grad.NonlinearProduct
