import GQC40SmoothProjection

noncomputable section

set_option maxHeartbeats 1600000

open Set
open scoped Topology

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearDivision
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.GaugeTransfer

def apSmoothMeanFree {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) :
    Submodule ℂ (APSmooth L sigma gamma ell 1) :=
  ⨅ cell : ℤ, LinearMap.ker ((angularClosedJetLinear 1 0).comp (apSmoothJet admissible 1 cell))

theorem mem_apSmoothMeanFree {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 1) : field ∈ apSmoothMeanFree admissible ↔ APSmoothMeanZero admissible field := by
  simp only [apSmoothMeanFree, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]
  rfl

def apSmoothAxisValues {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) (dimension : ℕ) :
    Submodule ℂ (APSmooth L sigma gamma ell dimension) :=
  ⨅ cell : ℤ, LinearMap.ker (((ContinuousMap.evalCLM ℂ closedOrigin).toLinearMap.comp
    (jetValueLinear dimension)).comp (apSmoothJet admissible dimension cell))

theorem mem_apSmoothAxisValues {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension) :
    field ∈ apSmoothAxisValues admissible dimension ↔ APSmoothAxisValueZero admissible field := by
  simp only [apSmoothAxisValues, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]
  rfl

def apSmoothAxisFirsts {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) (dimension : ℕ) :
    Submodule ℂ (APSmooth L sigma gamma ell dimension) :=
  apSmoothAxisValues admissible dimension ⊓ ⨅ coordinate : Fin 2,
    (apSmoothAxisValues admissible dimension).comap (apSmoothPartial admissible dimension coordinate)

theorem mem_apSmoothAxisFirsts {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension) :
    field ∈ apSmoothAxisFirsts admissible dimension ↔ APSmoothAxisFirstJetZero admissible field := by
  simp only [apSmoothAxisFirsts, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap,
    mem_apSmoothAxisValues]
  rfl

abbrev CompensatedData (L sigma gamma ell : ℝ) :=
  APSmooth L sigma gamma ell 1 × APSmooth L sigma gamma ell 3

def compensatedReconstruct {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] APSmooth L sigma gamma ell 3 :=
  (apSmoothCovariant admissible).comp (LinearMap.fst ℂ _ _) + LinearMap.snd ℂ _ _

theorem compensatedReconstruct_apply {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (data : CompensatedData L sigma gamma ell) :
    compensatedReconstruct admissible data = apSmoothCovariant admissible data.1 + data.2 := rfl

/-- Mean-free Θ, its actual zero first jet, and the zero first jet of
w=(∇Θ+v_c,DellΘ+e). The explicit Hessian cancellation is recovered below;
there is no independent derivative slot and no requirement Dv_c(0)=0. -/
def compensatedFlatCore {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) :
    Submodule ℂ (CompensatedData L sigma gamma ell) :=
  (apSmoothMeanFree admissible ⊓ apSmoothAxisFirsts admissible 1).comap (LinearMap.fst ℂ _ _) ⊓
    (apSmoothAxisFirsts admissible 3).comap (compensatedReconstruct admissible)

theorem mem_compensatedFlatCore {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (data : CompensatedData L sigma gamma ell) :
    data ∈ compensatedFlatCore admissible ↔
      (APSmoothMeanZero admissible data.1 ∧ APSmoothAxisFirstJetZero admissible data.1) ∧
        APSmoothAxisFirstJetZero admissible (compensatedReconstruct admissible data) := by
  simp only [compensatedFlatCore, Submodule.mem_inf, Submodule.mem_comap, LinearMap.fst_apply,
    mem_apSmoothMeanFree, mem_apSmoothAxisFirsts]

def circularCompensatedCore {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) :
    Submodule ℂ (CompensatedData L sigma gamma ell) :=
  compensatedFlatCore admissible ⊓ LinearMap.ker
    ((apSmoothComplement L sigma gamma ell).comp (compensatedReconstruct admissible))

def currentCompensatedCore {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge) :
    Submodule ℂ (CompensatedData L sigma gamma ell) :=
  compensatedFlatCore admissible ⊓ LinearMap.ker
    ((apSmoothGauge admissible gauge coherent).comp (compensatedReconstruct admissible))

theorem compensatedData_ext {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {first second : CompensatedData L sigma gamma ell} (theta : first.1 = second.1)
    (reconstruction : compensatedReconstruct admissible first = compensatedReconstruct admissible second) :
    first = second := by
  apply Prod.ext theta
  exact add_left_cancel ((congrArg (fun scalar : APSmooth L sigma gamma ell 1 =>
    apSmoothCovariant admissible scalar + first.2) theta).symm.trans reconstruction)

end Grad.GaugeCoefficients.Physical.Compensated
