import RelatedEquivalence

noncomputable section

namespace Grad.MainAssembly.TargetModuliTopology

open Grad.MainTarget
open Grad.MainAssembly.TargetRelation

/-- The target quotient projection is continuous for its literal coinduced
topology. -/
theorem continuous_moduliClass (regularity : Regularity) :
    Continuous (moduliClass regularity) := by
  exact continuous_coinduced_rng

/-- Exact target quotient-topology comparison with the quotient of the
constructed full-relation Setoid. -/
def moduliHomeomorphRelatedQuotient (regularity : Regularity) :
    Moduli regularity ≃ₜ Quotient (relatedSetoid regularity) where
  toEquiv := moduliEquivRelatedQuotient regularity
  continuous_toFun := by
    apply (continuous_coinduced_dom (f := moduliClass regularity)).mpr
    change Continuous
      (fun configuration : Configuration regularity =>
        Quotient.mk (relatedSetoid regularity) configuration)
    exact continuous_quot_mk
  continuous_invFun := by
    apply (continuous_coinduced_dom
      (f := fun configuration : Configuration regularity =>
        Quotient.mk (relatedSetoid regularity) configuration)).mpr
    change Continuous (moduliClass regularity)
    exact continuous_moduliClass regularity

end Grad.MainAssembly.TargetModuliTopology
