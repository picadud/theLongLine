
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic


open Topology TopologicalSpace Set Ordinal
#check Ordinal.toType ω₁
#check ω₁


def Ico01 := (Ico (0:ℝ)  1)
def L:=   (ω_ 1).toType ×ₗ Ico01

noncomputable example : PartialOrder (ω_ 1).toType := by infer_instance
noncomputable example : PartialOrder Ico01 := by infer_instance
noncomputable example : PartialOrder ((ω_ 1).toType ×ₗ Ico01) := by infer_instance
#synth PartialOrder ((ω_ 1).toType ×ₗ Ico01)
noncomputable instance : PartialOrder L := Prod.Lex.instPartialOrder (ω_ 1).toType ↑Ico01
instance : TopologicalSpace L := Preorder.topology L

#check Uncountable
#check exists_countable_basis
#check singletons_open_iff_discrete
#check IsTopologicalBasis.isOpen_iff
lemma not_second_countable_if_uncountable_discrete_subset (X: Type) [hX:TopologicalSpace X]
    (S: Set X) (h: ¬ S.Countable) (h1: DiscreteTopology S): ¬ SecondCountableTopology X:= by
  by_contra hX

  apply exists_countable_basis at hX
  cases' hX with B hB
  cases' hB with hBc hB
  cases' hB with hB1 hB2
  rw[ ← singletons_open_iff_discrete ] at h1
  have hS: Nonempty S := by
    refine nonempty_iff_ne_empty'.mpr ?_
    by_contra hse
    have he: (∅: Set X).Countable := by exact Subsingleton.to_countable
    rw[← hse] at he
    exact h he
  have h2: ∀ (K : Set S) , IsOpen K  → ∃(Uₖ: Set X), IsOpen Uₖ ∧ Uₖ ∩ S = K := by sorry
  /--use subtype.val with is seemingly the function that induces the subspace topology, leansearch:Topology,IsInducing,subtypeVal-/



theorem firstCountable_LongLine: FirstCountableTopology L:= by

  sorry
#check isSecondCountable
theorem not_secondCountable_LongLine: ¬ SecondCountableTopology L:= by
  sorry
