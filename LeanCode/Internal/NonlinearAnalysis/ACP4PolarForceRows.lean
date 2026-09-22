import ACP3MappedForce

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1600000
namespace Grad.ActualCurrentPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollar
open Grad.SourceCollarCoefficients Grad.SourceCollarAngular
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger

/-- Kind0 is delta r0 and kind1 is r2. The matrix is (R F_C)^T F_C^{-T};
the circular -2e1 row was removed algebraically, not estimated as small. -/
def forcePolarComponent (kind : Fin 2) (angle : ℝ)
    (matrix : Matrix (Fin 3) (Fin 3) ℂ) (component : Fin 3) : ℂ :=
  matrixPairing
    (if kind = 0 then (2 : ℂ) • physicalTangentialVector angle
      else (-2 : ℂ) • physicalToroidalVector) matrix
    (if component = 0 then physicalRadialVector angle
      else if component = 1 then physicalTangentialVector angle else physicalToroidalVector)

def forceLaurentLeft (kind : Fin 2) (index : Fin 2) : Fin 3 → ℂ :=
  if kind = 0 then (2 : ℂ) • tangentialLaurentVector index
  else if index = 0 then (-2 : ℂ) • physicalToroidalVector else 0

def forceLaurentFrequency (kind : Fin 2) (component : Fin 3) (slot : Fin 2 × Fin 2) : ℤ :=
  (if kind = 0 then polarLaurentSign slot.1 else 0) +
    if component = 2 then 0 else polarLaurentSign slot.2

theorem forcePolarComponent_laurent (kind : Fin 2) (angle : ℝ)
    (matrix : Matrix (Fin 3) (Fin 3) ℂ) (component : Fin 3) :
    forcePolarComponent kind angle matrix component =
      ∑ slot : Fin 2 × Fin 2, cellExponential (forceLaurentFrequency kind component slot) angle *
        matrixPairing (forceLaurentLeft kind slot.1) matrix
          (fun index => kappaLaurentRight component slot.2 index) := by
  rw [Fintype.sum_prod_type]
  fin_cases kind <;> fin_cases component <;>
    simp only [forceLaurentFrequency, cellExponential_add, kappaLaurentRight] <;>
    simp [Fin.sum_univ_two, forcePolarComponent, forceLaurentLeft, matrixPairing,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, polarLaurentSign,
      tangentialLaurentVector, radialLaurentVector, physicalRadialVector,
      physicalTangentialVector, physicalToroidalVector,
      cellExponential_one, cellExponential_neg_one, cellExponential_zero]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]
  all_goals ring

end Grad.ActualCurrentPrimitives
