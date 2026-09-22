import BL38PhysicalSeries

noncomputable section

open scoped BigOperators ComplexConjugate

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

theorem cartesianPhysicalConjugation_complex_smul (dimension : ℕ) (scalar : ℂ)
    (value : ComplexEuclidean dimension) :
    cartesianPhysicalConjugation dimension (scalar • value) =
      conj scalar • cartesianPhysicalConjugation dimension value := by
  apply PiLp.ext
  intro coordinate
  simp only [cartesianPhysicalConjugation_apply, PiLp.smul_apply, smul_eq_mul, map_mul]

/-- The exact reality pass-through: conjugate-symmetric boundary data give
a conjugate-reflection-symmetric lift, cell by cell. -/
theorem boundaryLift_reality {dimension : ℕ} (parameters : PhaseParameters)
    (values : BoundaryCore parameters dimension) (reality : BoundaryReality parameters values)
    (cell : ℤ) :
    (boundaryLift parameters values).1 (-cell) =
      closedJetConjugate ((boundaryLift parameters values).1 cell) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [closedJetConjugate_value, conjugateClosedMap_apply]
  have mapped := ((cartesianPhysicalConjugation dimension).toContinuousLinearEquiv.toContinuousLinearMap).hasSum
    (boundaryLift_angular_value_hasSum parameters values cell point)
  have applyLaw : ∀ value : ComplexEuclidean dimension,
      (cartesianPhysicalConjugation dimension).toContinuousLinearEquiv.toContinuousLinearMap value =
        cartesianPhysicalConjugation dimension value := fun _ => rfl
  simp only [applyLaw] at mapped
  have termLaw : ∀ mode : ℤ, cartesianPhysicalConjugation dimension
      (boundaryKernel (mode, cell) point.val • values.1 (mode, cell)) =
        boundaryKernel (-mode, -cell) point.val • values.1 (-mode, -cell) := by
    intro mode
    rw [cartesianPhysicalConjugation_complex_smul]
    have kernelLaw : conj (boundaryKernel (mode, cell) point.val) =
        boundaryKernel (-mode, -cell) point.val := by
      rw [boundaryKernel_conj mode cell point.val]
      exact (boundaryKernel_neg_snd (-mode) cell point.val).symm
    have valueLaw : cartesianPhysicalConjugation dimension (values.1 (mode, cell)) =
        values.1 (-mode, -cell) := (reality (mode, cell)).symm
    rw [kernelLaw, valueLaw]
  simp only [termLaw] at mapped
  have reflected : HasSum
      (fun mode : ℤ => boundaryKernel (mode, -cell) point.val • values.1 (mode, -cell))
      (cartesianPhysicalConjugation dimension (((boundaryLift parameters values).1 cell).value point)) :=
    (Equiv.neg ℤ).hasSum_iff.mp mapped
  exact (boundaryLift_angular_value_hasSum parameters values (-cell) point).unique reflected

end Grad.BoundaryLift
