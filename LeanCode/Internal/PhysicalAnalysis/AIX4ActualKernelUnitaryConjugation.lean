import AIX3ExactFourierUnitary

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKernelOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryLift Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction

private theorem orbitEntry_conjugation {src tgt : ℕ} (tau : OrbitParameter)
    (shift mode : ℤ × ℤ) (weight : ℂ)
    (entry : ComplexEuclidean src →L[ℂ] ComplexEuclidean tgt) (field : ComplexEuclidean src) :
    orbitCharacter tau mode • (weight • entry (orbitCharacter (-tau) (twoFrequencyTranslation shift mode) • field)) =
      weight • (orbitCharacter tau shift • entry field) := by
  rw [map_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  calc
    _ = weight * (orbitCharacter tau mode * orbitCharacter (-tau) (twoFrequencyTranslation shift mode)) := by ring
    _ = _ := by rw [orbitCharacter_displacement]

/-- Equality with genuine unitary conjugation on the exact input-mode
bulk action; the physical bulk weight ratio is unchanged. -/
theorem bulkKernelAction_orbit {src tgt : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (radius : RadialPoint) (kernel : RadialKernel parameters radius src tgt) (tau : OrbitParameter) :
    bulkKernelAction parameters power radius (kernelOrbit tau kernel) =
      (orbitLpAction (ComplexEuclidean tgt) tau).comp
        ((bulkKernelAction parameters power radius kernel).comp
          (orbitLpAction (ComplexEuclidean src) (-tau))) := by
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext mode
  have original := (bulkKernelAction_coordinate parameters power radius kernel
    (orbitLpAction (ComplexEuclidean src) (-tau) field) mode).const_smul (orbitCharacter tau mode)
  have translated := bulkKernelAction_coordinate parameters power radius (kernelOrbit tau kernel) field mode
  apply translated.unique
  convert original using 1
  · funext shift
    change (bulkWeightRatio parameters power radius.val shift mode : ℂ) •
        (orbitCharacter tau shift • kernel.entry shift (twoFrequencyTranslation shift mode)
          (field (twoFrequencyTranslation shift mode))) = _
    exact (orbitEntry_conjugation tau shift mode _ _ _).symm
  · rfl

private theorem fullNegativeKernelAction_raw_hasSum {src tgt : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) (kernel : FullTwoFrequencyKernel parameters src tgt)
    (field : NegativeTrace parameters angular cell src) (mode : ℤ × ℤ) :
    HasSum (fun shift => (negativeWeightRatio parameters angular cell shift mode : ℂ) •
      kernel.entry shift (twoFrequencyTranslation shift mode) (field (twoFrequencyTranslation shift mode)))
      (fullNegativeKernelAction parameters angular cell kernel field mode) := by
  exact (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean tgt) 2 mode).hasSum
    ((operatorEvaluation parameters 0 field).hasSum
      (fullNegativeShiftAction_summable parameters angular cell kernel).hasSum)

/-- Every original negative-half boundary grade has the same exact unitary
conjugation, including its original analytic phase weights. -/
theorem fullNegativeKernelAction_orbit {src tgt : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) (kernel : FullTwoFrequencyKernel parameters src tgt) (tau : OrbitParameter) :
    fullNegativeKernelAction parameters angular cell (kernelOrbit tau kernel) =
      (orbitLpAction (ComplexEuclidean tgt) tau).comp
        ((fullNegativeKernelAction parameters angular cell kernel).comp
          (orbitLpAction (ComplexEuclidean src) (-tau))) := by
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext mode
  have original := (fullNegativeKernelAction_raw_hasSum parameters angular cell kernel
    (orbitLpAction (ComplexEuclidean src) (-tau) field) mode).const_smul (orbitCharacter tau mode)
  have translated := fullNegativeKernelAction_raw_hasSum parameters angular cell (kernelOrbit tau kernel) field mode
  apply translated.unique
  convert original using 1
  · funext shift
    change (negativeWeightRatio parameters angular cell shift mode : ℂ) •
        (orbitCharacter tau shift • kernel.entry shift (twoFrequencyTranslation shift mode)
          (field (twoFrequencyTranslation shift mode))) = _
    exact (orbitEntry_conjugation tau shift mode _ _ _).symm
  · rfl

end Grad.AnnularKernelOrbit
