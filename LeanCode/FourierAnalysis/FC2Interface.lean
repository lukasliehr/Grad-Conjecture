import COR01Proof
import AW2Proof

noncomputable section

open Set
open scoped ContDiff Topology

namespace Grad.CartesianState

open Grad.ClosedJets

/-- The fixed geometric and analytic parameters used by every original Cartesian grade. -/
structure PhaseParameters where
  length : ℝ
  sigma0 : ℝ
  gamma : ℝ
  length_pos : 0 < length
  sigma0_pos : 0 < sigma0
  gamma_pos : 0 < gamma
  gamma_lt_min : gamma < min 1 sigma0

/-- The exact cell frequency `lambda_n = sqrt (1 + n^2)`. -/
def cellFrequency (cell : ℤ) : ℝ :=
  Grad.CellWeights.cellWeight cell

/-- The auxiliary polynomial weight `mu_n = 1 + |n|`. -/
def cellPolynomialWeight (cell : ℤ) : ℝ :=
  1 + |(cell : ℝ)|

/-- The literal original phase on the Euclidean disk plane. -/
def cartesianPhase (parameters : PhaseParameters) (cell : ℤ) (point : SpatialPlane) : ℝ :=
  Grad.AnalyticWeights.Calculus.physicalPhase parameters.sigma0 parameters.gamma 1 cell point

/-- The positive phase multiplier `exp (Phi_n(y))`. -/
def cartesianWeight (parameters : PhaseParameters) (cell : ℤ) (point : SpatialPlane) : ℝ :=
  Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma 1 cell point

/-- Each unordered two-dimensional multi-index of total order at most `grade`, exactly once. -/
abbrev GradeMultiIndex (grade : ℕ) :=
  {coordinates : Fin (grade + 1) × Fin (grade + 1) //
    coordinates.1.val + coordinates.2.val ≤ grade}

def GradeMultiIndex.toCartesian {grade : ℕ} (index : GradeMultiIndex grade) :
    CartesianMultiIndex :=
  (index.val.1.val, index.val.2.val)

/-- The literal value relation for multiplication by `exp (Phi_n)`. -/
def IsPhaseWeighted {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (weighted field : ClosedJet dimension) : Prop :=
  ∀ point : ClosedDisk,
    weighted.value point = cartesianWeight parameters cell point.val • field.value point

def BlockGoal : Prop :=
  (∀ cell : ℤ, 1 ≤ cellFrequency cell) ∧
  (∀ cell : ℤ, cellFrequency (-cell) = cellFrequency cell) ∧
  (∀ parameters cell point, cartesianPhase parameters (-cell) point =
    cartesianPhase parameters cell point) ∧
  (∀ parameters cell point, 0 < cartesianWeight parameters cell point) ∧
  (∀ parameters cell (point : ClosedDisk), 1 ≤ cartesianWeight parameters cell point.val) ∧
  (∀ grade, Nonempty (GradeMultiIndex grade ≃
    {index : CartesianMultiIndex // cartesianOrder index ≤ grade})) ∧
  ∀ dimension parameters cell (field : ClosedJet dimension),
    ∃! weighted : ClosedJet dimension, IsPhaseWeighted parameters cell weighted field

end Grad.CartesianState
