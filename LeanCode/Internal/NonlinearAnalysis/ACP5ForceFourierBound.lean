import ACP4PolarForceRows

noncomputable section
open scoped BigOperators

namespace Grad.ActualCurrentPrimitives
open Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation
open Grad.SourceCollarAngular

def forceFourierTerm (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (slot : Fin 2 × Fin 2) (radial : ℕ) (radius : ℝ) :
    ℤ × ℤ → ComplexEuclidean 1 :=
  coefficientPolarFourier parameters
    (mappedForceFamily parameters L epsilon field (scalarRowMapping (forceLaurentLeft kind slot.1)))
    (mappedForceFamily_coherent parameters L rho epsilon field _ low)
    (kappaLaurentRight component slot.2) radial radius ∘
      angularModeTranslation (forceLaurentFrequency kind component slot)

/-- Literal finite Laurent contractions of the actual physical force-matrix
contractions. Their pointwise and derivative correspondence is proved downstream. -/
def forceFourier (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radial : ℕ) (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  ∑ slot, forceFourierTerm parameters L rho epsilon field kind low component slot radial radius mode

def forceFourierTermConstant (parameters : PhaseParameters) (L : ℝ) (kind : Fin 2) (tangential radial : ℕ)
    (component : Fin 3) (slot : Fin 2 × Fin 2) : ℝ :=
  (1 + |(forceLaurentFrequency kind component slot : ℝ)|) ^ tangential *
    (coefficientFourierConstant tangential radial *
      mappedForceConstant parameters L (scalarRowMapping (forceLaurentLeft kind slot.1))
        (tangential + radial + 1) * ‖kappaLaurentRight component slot.2‖)

def forceFourierConstant (parameters : PhaseParameters) (L : ℝ) (kind : Fin 2) (tangential radial : ℕ) : ℝ :=
  1 + ∑ component : Fin 3, ∑ slot : Fin 2 × Fin 2,
    |forceFourierTermConstant parameters L kind tangential radial component slot|

theorem forceFourierConstant_pos (parameters : PhaseParameters) (L : ℝ) (kind : Fin 2) (tangential radial : ℕ) :
    0 < forceFourierConstant parameters L kind tangential radial := by
  unfold forceFourierConstant
  positivity

theorem forceFourierTerm_summable (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (tangential radial : ℕ) (component : Fin 3) (slot : Fin 2 × Fin 2)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (polarFourierMass parameters tangential radius
      (forceFourierTerm parameters L rho epsilon field kind low component slot radial radius)) :=
  polarFourierMass_shift_summable parameters tangential radius _
    (coefficient_fourier_summable parameters _
      (mappedForceFamily_coherent parameters L rho epsilon field _ low)
      (kappaLaurentRight component slot.2) tangential radial radius nonnegative bounded) _

theorem forceFourierTerm_bound (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (tangential radial : ℕ) (component : Fin 3) (slot : Fin 2 × Fin 2)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    ∑' mode, polarFourierMass parameters tangential radius
        (forceFourierTerm parameters L rho epsilon field kind low component slot radial radius) mode ≤
      forceFourierTermConstant parameters L kind tangential radial component slot *
        physicalBudget parameters field rho epsilon (tangential + radial + 6) := by
  have summable := coefficient_fourier_summable parameters _
    (mappedForceFamily_coherent parameters L rho epsilon field
      (scalarRowMapping (forceLaurentLeft kind slot.1)) low)
    (kappaLaurentRight component slot.2) tangential radial radius nonnegative bounded
  have shifted := polarFourierMass_shift_bound parameters tangential radius _ summable
    (forceLaurentFrequency kind component slot)
  have original := mappedForce_fourier_bound parameters L rho epsilon field
    (scalarRowMapping (forceLaurentLeft kind slot.1)) (kappaLaurentRight component slot.2)
    low tangential radial radius nonnegative bounded
  have bound := mul_le_mul_of_nonneg_left original
    (by positivity : 0 ≤ (1 + |(forceLaurentFrequency kind component slot : ℝ)|) ^ tangential)
  exact shifted.trans (bound.trans_eq (by unfold forceFourierTermConstant; ring))

theorem forceFourier_summable (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (tangential radial : ℕ) (component : Fin 3)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (polarFourierMass parameters tangential radius
      (forceFourier parameters L rho epsilon field kind low component radial radius)) :=
  polarFourierMass_sum_summable parameters tangential radius _
    (fun slot => forceFourierTerm_summable parameters L rho epsilon field kind low
      tangential radial component slot radius nonnegative bounded)

/-- Exact AD24 force-row bound including every angular and axial displacement, all
radial orders, original analytic width and one B6 ball chosen before t,k. -/
theorem forceFourier_bound (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (tangential radial : ℕ) (component : Fin 3)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    ∑' mode, polarFourierMass parameters tangential radius
        (forceFourier parameters L rho epsilon field kind low component radial radius) mode ≤
      forceFourierConstant parameters L kind tangential radial *
        physicalBudget parameters field rho epsilon (tangential + radial + 6) := by
  have total := polarFourierMass_sum_bound parameters tangential radius _
    (fun slot => forceFourierTerm_summable parameters L rho epsilon field kind low
      tangential radial component slot radius nonnegative bounded)
  have terms := Finset.sum_le_sum (s := Finset.univ) (fun slot _ =>
    forceFourierTerm_bound parameters L rho epsilon field kind low tangential radial component slot
      radius nonnegative bounded)
  rw [← Finset.sum_mul] at terms
  have componentBound : (∑ slot, forceFourierTermConstant parameters L kind tangential radial component slot) ≤
      forceFourierConstant parameters L kind tangential radial := by
    have absolute := Finset.sum_le_sum (s := Finset.univ) (fun slot _ =>
      le_abs_self (forceFourierTermConstant parameters L kind tangential radial component slot))
    have componentSum := Finset.single_le_sum
      (f := fun component : Fin 3 => ∑ slot : Fin 2 × Fin 2,
        |forceFourierTermConstant parameters L kind tangential radial component slot|)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ component)
    exact absolute.trans (componentSum.trans (by unfold forceFourierConstant; linarith))
  exact total.trans (terms.trans (mul_le_mul_of_nonneg_right componentBound
    (physicalBudget_nonnegative parameters field rho epsilon _)))

end Grad.ActualCurrentPrimitives

