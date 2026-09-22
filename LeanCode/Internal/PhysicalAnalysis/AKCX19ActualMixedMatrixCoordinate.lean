import AKCX18SameSignedRankDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

/-- The actual joint (spatial rank, signed power) matrix split. Nonempty
spatial allocations use the completed rank grade at every power; positive
axial allocations use only strictly lower powers of the SAME top spatial
derivative. No top first graph is assumed. -/
theorem startupActualMatrix_mixedCoordinateFirst {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output rank : ℕ}
    (coefficients : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent coefficients)
    (family : StartupSignedFamily input L ell)
    (jets : ℕ → GraphGrade input rank rank openUnitDisk)
    (jetsSame : ∀ power, base input rank openUnitDisk (fun _ => rank) (jets power) = family.moment power)
    (power : ℕ) (word : Fin rank → Fin 2)
    (lower : ∀ q < power, ∃ graph : StartupFirst input,
      base input 1 openUnitDisk (fun _ => 0) graph =
        orderedDerivative input rank rank openUnitDisk (fun _ => rank) le_rfl (jets q) word)
    (image : GraphGrade output rank 0 openUnitDisk)
    (imageSame : base output rank openUnitDisk (fun _ => 0) image =
      (family.matrix admissible coefficients coherent).moment power) :
    ∃ remainder : StartupFirst output,
      orderedDerivative output rank rank openUnitDisk (fun _ => 0) le_rfl image word =
      originalMatrixKernel admissible coefficients coherent
        (orderedDerivative input rank rank openUnitDisk (fun _ => rank) le_rfl (jets power) word) +
      base output 1 openUnitDisk (fun _ => 0) remainder := by
  let moments := fun q => orderedDerivative input rank rank openUnitDisk (fun _ => rank) le_rfl (jets q) word
  let spatialRem := fun j => startupDisplacementOrderedRemainder admissible coefficients coherent j word le_rfl
    (show rank-1 ≤ rank from Nat.sub_le _ _) (jets (power-j))
  let derivatives := fun j => startupDisplacementKernel admissible coefficients coherent zeroDerivativeIndex j
    (moments (power-j)) + spatialRem j
  have weak (j : ℕ) : HasWeakOrderedDerivative output openUnitDisk rank word
      (startupDisplacementKernel admissible coefficients coherent zeroDerivativeIndex j (family.moment (power-j)))
      (derivatives j) := by
    have actual := startupDisplacement_weakLeadingSplit admissible coefficients coherent j word le_rfl
      (show rank-1 ≤ rank from Nat.sub_le _ _) (jets (power-j))
    rw [jetsSame] at actual
    exact actual
  have weakSum := startupWeakOrdered_sum (Finset.range (power+1))
    (fun j => (power.choose j : ℂ) • startupDisplacementKernel admissible coefficients coherent zeroDerivativeIndex j
      (family.moment (power-j)))
    (fun j => (power.choose j : ℂ) • derivatives j)
    (fun j _ => startupWeakOrdered_smul (weak j) (power.choose j : ℂ))
  change HasWeakOrderedDerivative output openUnitDisk rank word
    ((family.matrix admissible coefficients coherent).moment power)
    (∑ j ∈ Finset.range (power+1), (power.choose j : ℂ) • derivatives j) at weakSum
  have actualDerivative : orderedDerivative output rank rank openUnitDisk (fun _ => 0) le_rfl image word =
      ∑ j ∈ Finset.range (power+1), (power.choose j : ℂ) • derivatives j := by
    exact Grad.WeakTesting.Commutation.weakEquality output openUnitDisk openUnitDisk_isOpen rank word word
      (fun _ => rfl) _ _ _
      (orderedDerivative_hasWeak output rank rank openUnitDisk (fun _ => 0) le_rfl image word)
      (by rw [imageSame]; exact weakSum)
  let spatialGraphs (j : ℕ) : StartupFirst output :=
    (startupDisplacementOrderedRemainder_first admissible coefficients coherent j word le_rfl le_rfl (jets (power-j))).choose
  have spatialSame (j : ℕ) : base output 1 openUnitDisk (fun _ => 0) (spatialGraphs j) = spatialRem j :=
    (startupDisplacementOrderedRemainder_first admissible coefficients coherent j word le_rfl le_rfl (jets (power-j))).choose_spec
  let spatialGraph : StartupFirst output := ∑ j ∈ Finset.range (power+1), (power.choose j : ℂ) • spatialGraphs j
  let lowerGraphs : Fin power → StartupFirst input := fun j =>
    (lower (power-(j.val+1)) (startupPositiveAxialRemainder_lower power j)).choose
  have lowerSame (j : Fin power) : base input 1 openUnitDisk (fun _ => 0) (lowerGraphs j) = moments (power-(j.val+1)) :=
    (lower (power-(j.val+1)) (startupPositiveAxialRemainder_lower power j)).choose_spec
  let axialGraph := startupPositiveAxialRemainderGraph admissible coefficients coherent power
    (show 1-1 ≤ 0 by decide) lowerGraphs
  have axialSame : base output 1 openUnitDisk (fun _ => 0) axialGraph =
      startupPositiveAxialRemainder admissible coefficients coherent power moments :=
    startupPositiveAxialRemainderGraph_base admissible coefficients coherent power _ lowerGraphs moments lowerSame
  have assembled : (∑ j ∈ Finset.range (power+1), (power.choose j : ℂ) • derivatives j) =
      startupKernelAxialMoment admissible coefficients coherent zeroDerivativeIndex power moments +
        base output 1 openUnitDisk (fun _ => 0) spatialGraph := by
    simp only [derivatives,smul_add,Finset.sum_add_distrib,spatialGraph,map_sum,map_smul,spatialSame]
    rfl
  refine ⟨axialGraph+spatialGraph,?_⟩
  rw [actualDerivative,assembled,startupKernelAxialMoment_leadingSplit,map_add,axialSame]
  abel

end Grad.CartesianStartup
