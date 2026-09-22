import GC18APComplementValue
import GC18CMapCoefficient
import GC18CMapAction

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.NonlinearQuotientBounds
open Grad.RepresentedKernel.SpatialProduct
open Grad.GaugeCoefficients.Radial

theorem apOperatorJet_zero {input output : ℕ} (coefficient : SmoothOperatorJet input output) :
    smoothOperatorDerivative coefficient (0, 0) = coefficient.value := by
  apply smoothOperatorDerivative_eq_of_spec
  intro candidate inside
  change coefficient.value candidate = closedDiskLift coefficient.value candidate.val
  unfold closedDiskLift
  rw [dif_pos (openDiskMembershipClosed candidate.val inside)]

theorem apFourierPhase_eq (cell : ℤ) (angle : ℝ) : fourierPhase cell angle = axialPhase cell angle := by
  unfold fourierPhase axialPhase
  congr 1
  push_cast
  ring

theorem apPhysicalValue_single {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (large : 2 ≤ grade) (angle : ℝ) (cell : ℤ) (field : ClosedJet dimension) :
    apPhysicalValue admissible large angle (apFiniteInto L sigma gamma ell (Finsupp.single cell field)) =
      axialPhase cell angle • field.value := by
  rw [← (apPhysicalValue_hasSum admissible large angle (apFiniteInto L sigma gamma ell (Finsupp.single cell field))).tsum_eq]
  simp_rw [apTrace_core]
  rw [tsum_eq_single cell]
  · rw [Finsupp.single_eq_same]
  · intro other different
    rw [Finsupp.single_eq_of_ne different]
    change axialPhase other angle • (0 : C(ClosedDisk, ComplexEuclidean dimension)) = 0
    exact smul_zero (M := ℂ) (A := C(ClosedDisk, ComplexEuclidean dimension)) _

theorem cMapCoefficient_single {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade input output : ℕ} (angle : ℝ) (cell : ℤ) (coefficient : SmoothOperatorJet input output) :
    cMapCoefficient admissible grade input output angle (singleJetCoefficient L sigma gamma ell grade cell coefficient) =
      axialPhase cell angle • coefficient.value := by
  apply ContinuousMap.ext
  intro point
  rw [cMapCoefficient_apply]
  unfold coefficientPhysicalValue
  simp_rw [singleJetCoefficient_derivative]
  rw [tsum_eq_single cell]
  · rw [if_pos rfl, apFourierPhase_eq]
    change axialPhase cell angle • smoothOperatorDerivative coefficient (0, 0) point = _
    rw [apOperatorJet_zero]
    rfl
  · intro other different
    rw [if_neg different]
    exact smul_zero (M := ℂ) (A := OperatorValue input output) _

theorem apMultiplier_single {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output grade : ℕ} (inputCell shift : ℤ) (coefficient : SmoothOperatorJet input output) (field : ClosedJet input) :
    apMultiplier admissible (singleJetCoefficient L sigma gamma ell grade shift coefficient)
        (apFiniteInto L sigma gamma ell (Finsupp.single inputCell field)) =
      apFiniteInto L sigma gamma ell (Finsupp.single (inputCell + shift) (apProductJet coefficient field)) := by
  apply Subtype.ext
  change apAmbientMultiplier admissible (weightedSingle L sigma gamma ell grade shift coefficient)
    (apFiniteEmbed L sigma gamma ell (Finsupp.single inputCell field)) =
      apFiniteEmbed L sigma gamma ell (Finsupp.single (inputCell + shift) (apProductJet coefficient field))
  rw [apFiniteEmbed_single, apFiniteEmbed_single, apAmbientMultiplier_core]

theorem apMultiplier_single_physical {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output grade : ℕ} (large : 2 ≤ grade) (angle : ℝ) (inputCell shift : ℤ)
    (coefficient : SmoothOperatorJet input output) (field : ClosedJet input) :
    apPhysicalValue admissible large angle
      (apMultiplier admissible (singleJetCoefficient L sigma gamma ell grade shift coefficient)
        (apFiniteInto L sigma gamma ell (Finsupp.single inputCell field))) =
      cMapAction (cMapCoefficient admissible grade input output angle (singleJetCoefficient L sigma gamma ell grade shift coefficient))
        (apPhysicalValue admissible large angle (apFiniteInto L sigma gamma ell (Finsupp.single inputCell field))) := by
  rw [apMultiplier_single, apPhysicalValue_single, cMapCoefficient_single, apPhysicalValue_single]
  apply ContinuousMap.ext
  intro point
  change axialPhase (inputCell + shift) angle • (apProductJet coefficient field).value point =
    (axialPhase shift angle • coefficient.value point) (axialPhase inputCell angle • field.value point)
  rw [apProductJet_value, smul_apply, map_smul, smul_smul, axialPhase_add, mul_comm]

end Grad.GaugeCoefficients.Physical.RadialLedger
