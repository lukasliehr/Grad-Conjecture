import AIR6LiteralKnownPhysicalRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKnownLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.BoundaryKernelAction Grad.SourceCollarCoefficients Grad.PhaseAlgebra Grad.AnnularCrossMaps

/-- The same completed known source is exactly BF8's physical low forcing,
with its original rho storage, genuine +Rg, and negative flux derivatives. -/
theorem knownLowForcing_original (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters L compact)
    (known : HighKnownSourceBulk lower) (g : DivisionRow 1 lower) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      knownLowForcing parameters L compact lower positive bounded state known g index radius =
      (lowRhoPhysicalWeight parameters lower positive radius index.2.val : ℂ) •
      crossLowSourceSymbol parameters L radius index
        (lowRhoPhysicalCoefficient parameters lower positive
          (lowPhysicalRowAction parameters L compact lower positive bounded state 0 (knownLowSevenPacket lower known)) radius index.2.val +
          lowRhoPhysicalCoefficient parameters lower positive (known 3) radius index.2.val)
        (lowRhoPhysicalCoefficient parameters lower positive
          (lowPhysicalRowAction parameters L compact lower positive bounded state 1 (knownLowSevenPacket lower known)) radius index.2.val)
        (lowRhoPhysicalCoefficient parameters lower positive
          (lowPhysicalRowAction parameters L compact lower positive bounded state 2 (knownLowSevenPacket lower known)) radius index.2.val -
          radius • lowRhoPhysicalCoefficient parameters lower positive g radius index.2.val) := by
  let j := lowPhysicalRowAction parameters L compact lower positive bounded state 0 (knownLowSevenPacket lower known)
  let c := lowPhysicalRowAction parameters L compact lower positive bounded state 1 (knownLowSevenPacket lower known)
  let rv := lowPhysicalRowAction parameters L compact lower positive bounded state 2 (knownLowSevenPacket lower known)
  filter_upwards [knownLowForcing_stored_ae parameters L compact lower positive bounded state known g index,
    Lp.coeFn_add (j index.2.val) (known 3 index.2.val),
    Lp.coeFn_sub (rv index.2.val) (radialRadiusRow lower positive g index.2.val),
    radialRadiusRow_ae lower positive g] with radius actual first last radial
  rw [actual]
  change crossLowSourceSymbol parameters L radius index
      ((j index.2.val + known 3 index.2.val) radius) (c index.2.val radius)
      ((rv index.2.val - radialRadiusRow lower positive g index.2.val) radius) = _
  rw [first, last]
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [radial index.2.val]
  let weight : ℂ := lowRhoPhysicalWeight parameters lower positive radius index.2.val
  have nonzero : weight ≠ 0 := by
    change (lowRhoPhysicalWeight parameters lower positive radius index.2.val : ℂ) ≠ 0
    exact_mod_cast (lowRhoPhysicalWeight_pos parameters lower positive radius index.2.val).ne'
  change crossLowSourceSymbol parameters L radius index
      (j index.2.val radius + known 3 index.2.val radius) (c index.2.val radius)
      (rv index.2.val radius - radius • g index.2.val radius) =
    weight • crossLowSourceSymbol parameters L radius index
      (weight⁻¹ • j index.2.val radius + weight⁻¹ • known 3 index.2.val radius)
      (weight⁻¹ • c index.2.val radius)
      (weight⁻¹ • rv index.2.val radius - radius • (weight⁻¹ • g index.2.val radius))
  rw [← smul_add, show radius • (weight⁻¹ • g index.2.val radius) = weight⁻¹ • (radius • g index.2.val radius) from smul_comm _ _ _,
    ← smul_sub, crossLowSourceSymbol_smul, smul_inv_smul₀ nonzero]

end Grad.AnnularKnownLow
