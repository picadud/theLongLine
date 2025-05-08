
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Tactic
open Topology Set Ordinal
#check ω_ 1
def L:=   Set ((ω_ 1).toType × (Ico (0:ℝ)  1))
