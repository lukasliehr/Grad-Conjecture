import GQC33CovariantJet

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.NonlinearQuotientBounds

def jetValueLinear (dimension : ℕ) : ClosedJet dimension →ₗ[ℂ] C(ClosedDisk, ComplexEuclidean dimension) where
  toFun := ClosedJet.value
  map_add' := closedJet_value_add
  map_smul' := closedJet_value_smul

def physicalFiniteJet (dimension : ℕ) (angle : ℝ) : (ℤ →₀ ClosedJet dimension) →ₗ[ℂ] ClosedJet dimension :=
  Finsupp.lsum ℂ (fun cell => axialPhase cell angle • LinearMap.id)

theorem physicalFiniteJet_value {dimension : ℕ} (angle : ℝ) (core : ℤ →₀ ClosedJet dimension) :
    (physicalFiniteJet dimension angle core).value = ∑ cell ∈ core.support, axialPhase cell angle • (core cell).value := by
  classical
  change jetValueLinear dimension (physicalFiniteJet dimension angle core) = _
  rw [physicalFiniteJet, Finsupp.lsum_apply, Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro cell _
  exact map_smul (jetValueLinear dimension) (axialPhase cell angle) (core cell)

theorem apPhysicalValue_finiteJet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (large : 2 ≤ grade) (angle : ℝ) (core : ℤ →₀ ClosedJet dimension) :
    apPhysicalValue admissible large angle (apFiniteInto L sigma gamma ell core) =
      (physicalFiniteJet dimension angle core).value :=
  (apPhysicalValue_core admissible large angle core).trans (physicalFiniteJet_value angle core).symm

theorem physicalFiniteJet_map {dimension : ℕ} (angle : ℝ) (mapping : ClosedJet dimension →ₗ[ℂ] ClosedJet dimension)
    (core : ℤ →₀ ClosedJet dimension) :
    physicalFiniteJet dimension angle (apFiniteJetMap mapping core) = mapping (physicalFiniteJet dimension angle core) := by
  classical
  rw [physicalFiniteJet, Finsupp.lsum_apply, Finsupp.lsum_apply]
  simp only [Finsupp.sum, map_sum, LinearMap.smul_apply, LinearMap.id_apply]
  change (apFiniteJetMap mapping core).sum (fun cell field => axialPhase cell angle • field) = _
  rw [apFiniteJetMap, Finsupp.mapRange.linearMap_apply, Finsupp.sum_mapRange_index]
  · apply Finset.sum_congr rfl
    intro cell _
    exact (map_smul mapping (axialPhase cell angle) (core cell)).symm
  · intro cell
    exact smul_zero _

end Grad.GaugeCoefficients.Physical.Compensated
