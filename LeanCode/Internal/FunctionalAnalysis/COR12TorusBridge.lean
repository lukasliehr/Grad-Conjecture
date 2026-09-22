import P0910Proof
import FTP1315Proof

noncomputable section

namespace Grad.COR12Extension

open Grad.DiskExtension.Operator
open Grad.FourierGrade

local instance cor12CellPeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

def spatialCircleToUnit : SpatialCircle ≃ₜ UnitAddCircle :=
  AddCircle.homeomorphAddCircle (4 : ℝ) 1 (by norm_num) one_ne_zero

def cellCircleToUnit : Grad.ClosedJets.CellCircle ≃ₜ UnitAddCircle :=
  AddCircle.homeomorphAddCircle (2 * Real.pi : ℝ) 1
    (mul_ne_zero (by norm_num) Real.pi_ne_zero) one_ne_zero

def torusCellToProduct : TorusCellDomain ≃ₜ ProductTorus where
  toFun point := ![spatialCircleToUnit point.1.1,
    spatialCircleToUnit point.1.2, cellCircleToUnit point.2]
  invFun point := ((spatialCircleToUnit.symm (point 0),
    spatialCircleToUnit.symm (point 1)), cellCircleToUnit.symm (point 2))
  left_inv point := by
    rcases point with ⟨⟨first, second⟩, cell⟩
    simp [spatialCircleToUnit, cellCircleToUnit]
  right_inv point := by
    funext coordinate
    fin_cases coordinate <;> simp [spatialCircleToUnit, cellCircleToUnit]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem torusCellToProduct_torusCellPoint (point : Grad.ClosedJets.SpatialCell) :
    torusCellToProduct (torusCellPoint point) =
      normalizedTorusPoint (point 0) (point 1) (point 2) := by
  funext coordinate
  fin_cases coordinate <;>
    simp [torusCellToProduct, spatialCircleToUnit, cellCircleToUnit,
      normalizedTorusPoint, torusCellPoint] <;>
    field_simp [Real.pi_ne_zero]

def torusSmoothNormalizedValue {dimension : ℕ}
    (field : TorusSmoothField dimension) :
    C(ProductTorus, Grad.ClosedJets.ComplexEuclidean dimension) :=
  field.value.comp ⟨torusCellToProduct.symm, torusCellToProduct.symm.continuous⟩

def reconstructedTorusCellValue {dimension : ℕ}
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension)) :
    C(TorusCellDomain, Grad.ClosedJets.ComplexEuclidean dimension) :=
  (reconstructedTorus values).comp ⟨torusCellToProduct, torusCellToProduct.continuous⟩

theorem reconstructedTorusCellValue_lift {dimension : ℕ}
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension))
    (point : Grad.ClosedJets.SpatialCell) :
    torusCellLift (reconstructedTorusCellValue values) point =
      reconstructedPhysical values (physicalPoint (point 0) (point 1) (point 2)) := by
  rw [reconstructedPhysical_physicalPoint]
  change reconstructedTorus values (torusCellToProduct (torusCellPoint point)) = _
  rw [torusCellToProduct_torusCellPoint]

/-- Apply the exact Fourier coefficient multiplier following an ordered word
of physical coordinate derivatives. -/
def physicalWordDerivativeCore {dimension : ℕ} (word : List (Fin 3))
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension)) :
    JCore (Grad.ClosedJets.ComplexEuclidean dimension) :=
  word.foldr partialDerivativeCore values

theorem mixedListDerivative_reconstructedPhysical {dimension : ℕ}
    (word : List (Fin 3))
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension)) :
    mixedListDerivative word (reconstructedPhysical values) =
      reconstructedPhysical (physicalWordDerivativeCore word values) := by
  induction word with
  | nil => rfl
  | cons direction rest inductionHypothesis =>
      change physicalPartialDerivative direction
          (mixedListDerivative rest (reconstructedPhysical values)) =
        reconstructedPhysical
          (partialDerivativeCore direction (physicalWordDerivativeCore rest values))
      rw [inductionHypothesis, physicalPartialDerivative_reconstructed]

theorem reconstructedTorusCellValue_lift_function {dimension : ℕ}
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension)) :
    torusCellLift (reconstructedTorusCellValue values) =
      reconstructedPhysical values := by
  funext point
  have physicalPointIdentity :
      physicalPoint (point 0) (point 1) (point 2) = point := by
    ext coordinate
    fin_cases coordinate <;> rfl
  rw [← physicalPointIdentity]
  exact reconstructedTorusCellValue_lift values point

/-- Every all-grade Fourier core reconstructs an actual P09 torus-smooth
field on the physical `(4,4,2π)` torus, with all ordered derivative
extensions supplied by the differentiated Fourier core. -/
def reconstructedTorusSmoothField {dimension : ℕ}
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension)) :
    TorusSmoothField dimension where
  value := reconstructedTorusCellValue values
  smoothLift := by
    rw [reconstructedTorusCellValue_lift_function]
    exact reconstructedPhysical_contDiff values
  derivativeExists order word := by
    refine ⟨reconstructedTorusCellValue
      (physicalWordDerivativeCore (List.ofFn word) values), ?_⟩
    intro point
    calc
      reconstructedTorusCellValue
          (physicalWordDerivativeCore (List.ofFn word) values)
          (torusCellPoint point) =
          reconstructedPhysical
            (physicalWordDerivativeCore (List.ofFn word) values) point := by
        exact congrFun
          (reconstructedTorusCellValue_lift_function
            (physicalWordDerivativeCore (List.ofFn word) values)) point
      _ = mixedListDerivative (List.ofFn word)
          (reconstructedPhysical values) point := by
        exact congrFun
          (mixedListDerivative_reconstructedPhysical (List.ofFn word) values).symm point
      _ = Grad.ClosedJets.mixedCartesianDerivative order word
          (reconstructedPhysical values) point := by
        exact mixedListDerivative_ofFn isOpen_univ order word
          (reconstructedPhysical_contDiff values).contDiffOn (Set.mem_univ point)
      _ = Grad.ClosedJets.mixedCartesianDerivative order word
          (torusCellLift (reconstructedTorusCellValue values)) point := by
        rw [reconstructedTorusCellValue_lift_function]

theorem torusSmoothNormalizedValue_reconstructed {dimension : ℕ}
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension)) :
    torusSmoothNormalizedValue (reconstructedTorusSmoothField values) =
      reconstructedTorus values := by
  apply ContinuousMap.ext
  intro point
  simp [torusSmoothNormalizedValue, reconstructedTorusSmoothField,
    reconstructedTorusCellValue]

theorem reconstructedTorusSmoothField_coefficient {dimension : ℕ}
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension))
    (mode : FourierMode) :
    UnitAddTorus.mFourierCoeff
        (torusSmoothNormalizedValue (reconstructedTorusSmoothField values))
        (modeVector mode) = values.1 mode := by
  rw [torusSmoothNormalizedValue_reconstructed]
  exact euclidean_reconstructedTorus_coefficient values mode

end Grad.COR12Extension
