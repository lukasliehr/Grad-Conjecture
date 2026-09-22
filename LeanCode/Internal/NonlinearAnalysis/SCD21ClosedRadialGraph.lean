import SCD20RadialWeakDerivative

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState

def divisionArrayCoordinate (dimension : ℕ) (lower : ℝ) (radial : ℕ)
    (index : Fin (radial + 1)) (mode : ℤ × ℤ) :
    DivisionJetArray dimension lower radial →L[ℂ] RadialL2 dimension lower :=
  (lp.evalCLM ℂ (fun _ : ℤ × ℤ => RadialL2 dimension lower) 2 mode).comp
    (PiLp.proj 1 (fun _ : Fin (radial + 1) => DivisionRow dimension lower) index)

def radialGraphResidual {dimension : ℕ} (lower : ℝ) (positive : 0 < lower)
    (radial : ℕ) (index : Fin radial) (mode : ℤ × ℤ)
    (test : RadialTest lower) (vector : ComplexEuclidean dimension) :
    DivisionJetArray dimension lower radial →L[ℂ] ℂ :=
  (radialPairing lower positive test.value test.continuousValue vector).comp
      (divisionArrayCoordinate dimension lower radial index.succ mode) +
    (radialPairing lower positive test.derivative test.continuousDerivative vector).comp
      (divisionArrayCoordinate dimension lower radial index.castSucc mode)

/-- The actual weak radial derivative graph, with no boundary condition on
the unknown and no independent derivative coordinates. Its inherited norm
is precisely the sum of the full Fourier/radial L2 coordinate norms. -/
def annularDerivativeGraph (dimension : ℕ) (lower : ℝ) (positive : 0 < lower) (radial : ℕ) :
    Submodule ℂ (DivisionJetArray dimension lower radial) :=
  ⨅ (index : Fin radial) (mode : ℤ × ℤ) (test : RadialTest lower) (vector : ComplexEuclidean dimension),
    (radialGraphResidual lower positive radial index mode test vector).ker

theorem annularDerivativeGraph_mem_iff {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (radial : ℕ) (field : DivisionJetArray dimension lower radial) :
    field ∈ annularDerivativeGraph dimension lower positive radial ↔
      ∀ (index : Fin radial) (mode : ℤ × ℤ),
        HasWeakRadialDerivative lower positive (field index.castSucc mode) (field index.succ mode) := by
  simp [annularDerivativeGraph, radialGraphResidual, divisionArrayCoordinate,
    HasWeakRadialDerivative, add_eq_zero_iff_eq_neg]
  rfl

theorem annularDerivativeGraph_closed (dimension : ℕ) (lower : ℝ) (positive : 0 < lower) (radial : ℕ) :
    IsClosed (annularDerivativeGraph dimension lower positive radial :
      Set (DivisionJetArray dimension lower radial)) := by
  simp only [annularDerivativeGraph, Submodule.coe_iInf]
  exact isClosed_iInter fun index => isClosed_iInter fun mode =>
    isClosed_iInter fun test => isClosed_iInter fun vector =>
      (radialGraphResidual lower positive radial index mode test vector).isClosed_ker

instance annularDerivativeGraph_complete (dimension : ℕ) (lower : ℝ) (positive : 0 < lower) (radial : ℕ) :
    CompleteSpace (annularDerivativeGraph dimension lower positive radial) :=
  (annularDerivativeGraph_closed dimension lower positive radial).completeSpace_coe

theorem divisionModeLp_weak_derivative {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (power radial : ℕ) (parameters : PhaseParameters) (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    HasWeakRadialDerivative lower positive
      (divisionModeLp lower power radial parameters field mode)
      (divisionModeLp lower power (radial + 1) parameters field mode) :=
  (radialCoefficient_weak_derivative lower positive bounded
    (dividedPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2)))
    (dividedPolarValue_smooth _) mode.1 radial).smul _

theorem completedDivisionArray_graph {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : AGrade parameters dimension (power + radial + 3)) :
    completedDivisionArray lower positive bounded parameters power radial field ∈
      annularDerivativeGraph dimension lower positive radial := by
  refine UniformSpace.Completion.induction_on field
    ((annularDerivativeGraph_closed dimension lower positive radial).preimage
      (completedDivisionArray lower positive bounded parameters power radial).continuous) ?_
  intro core
  apply (annularDerivativeGraph_mem_iff lower positive radial _).mpr
  intro index mode
  change HasWeakRadialDerivative lower positive
    (completedDivisionArray lower positive bounded parameters power radial
      (aGradeEta parameters core) index.castSucc mode)
    (completedDivisionArray lower positive bounded parameters power radial
      (aGradeEta parameters core) index.succ mode)
  simp only [completedDivisionArray_component, completedDivisionRow_core]
  exact divisionModeLp_weak_derivative lower positive bounded power index.val parameters core.toCore mode

end Grad.SourceCollarDivision
