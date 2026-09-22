import GC17EstimateAlgebra

noncomputable section

set_option maxHeartbeats 1200000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

theorem familyCoherent_sum {L sigma gamma ell : ℝ} {input output : ℕ} {Index : Type*} [Fintype Index]
    (families : Index → CoefficientFamily L sigma gamma ell input output)
    (coherent : ∀ index, FamilyCoherent (families index)) :
    FamilyCoherent (fun grade => ∑ index : Index, families index grade) := by
  intro grade other index otherIndex same cell point
  rw [seedDerivative_sum, seedDerivative_sum]
  apply Finset.sum_congr rfl
  intro item _
  exact coherent item grade other index otherIndex same cell point

theorem family_physicalValue_sum {L sigma gamma ell : ℝ} {input output : ℕ} {Index : Type*} [Fintype Index]
    (admissible : Admissible L sigma gamma ell)
    (families : Index → CoefficientFamily L sigma gamma ell input output)
    (coherent : ∀ index, FamilyCoherent (families index)) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (∑ index : Index, families index grade) angle point =
      ∑ index : Index, coefficientPhysicalValue (families index grade) angle point := by
  rw [coherent_physicalValue _ (familyCoherent_sum families coherent)]
  simp_rw [coherent_physicalValue _ (coherent _)]
  exact map_sum (seedFourierCLM admissible input output angle point) _ _

def EstimateProfile.sum {Index : Type*} [Fintype Index] (profiles : Index → EstimateProfile) : EstimateProfile :=
  ⟨fun grade => ∑ index : Index, (profiles index).fixed grade,
    fun grade => ∑ index : Index, (profiles index).deviation grade⟩

theorem familyEstimate_sum {L ell : ℝ} {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {offset input output : ℕ} {Index : Type*} [Fintype Index]
    (profiles : Index → EstimateProfile)
    (actual reference : Index → CoefficientFamily L parameters.sigma0 parameters.gamma ell input output)
    (estimates : ∀ index, FamilyEstimate parameters field rho epsilon offset (profiles index) (actual index) (reference index)) :
    FamilyEstimate parameters field rho epsilon offset (EstimateProfile.sum profiles)
      (fun grade => ∑ index : Index, actual index grade) (fun grade => ∑ index : Index, reference index grade) where
  actualCoherent := familyCoherent_sum actual (fun index => (estimates index).actualCoherent)
  referenceCoherent := familyCoherent_sum reference (fun index => (estimates index).referenceCoherent)
  fixedNonnegative grade := Finset.sum_nonneg fun index _ => (estimates index).fixedNonnegative grade
  deviationNonnegative grade := Finset.sum_nonneg fun index _ => (estimates index).deviationNonnegative grade
  referenceBound grade := (norm_sum_le _ _).trans (Finset.sum_le_sum fun index _ => (estimates index).referenceBound grade)
  deviationBound grade := by
    rw [← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun index _ => (estimates index).deviationBound grade).trans_eq
      (by simp only [EstimateProfile.sum, Finset.sum_mul]))

def operatorMatrixLinear (input output : ℕ) : OperatorValue input output →ₗ[ℂ] Matrix (Fin output) (Fin input) ℂ where
  toFun := operatorMatrix
  map_add' := operatorMatrix_add
  map_smul' := operatorMatrix_smul

theorem operatorMatrix_sum {input output : ℕ} {Index : Type*} [Fintype Index]
    (values : Index → OperatorValue input output) :
    operatorMatrix (∑ index : Index, values index) = ∑ index : Index, operatorMatrix (values index) :=
  map_sum (operatorMatrixLinear input output) _ _

end Grad.GaugeCoefficients.Physical.Ledger
