module
import all Concrete
import all ScalarCertificate
import all LocalCliques
import all Transfer
import Lean.Util.CollectAxioms

#print axioms LocalBN.edgeLocalizedNoncompleteUnordered
#print axioms LocalBN.edgeCliqueScalar

open Lean Elab Command in
run_cmd do
  let deps ← liftCoreM (`LocalBN.edgeLocalizedNoncompleteUnordered).transitivelyUsedConstants
  logInfo m!"global_weighted_used={deps.contains `BN.weighted}"
  logInfo m!"edge_clique_scalar_used={deps.contains `LocalBN.edgeCliqueScalar}"
