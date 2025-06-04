
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic


open Topology TopologicalSpace Set Ordinal Classical
<<<<<<< HEAD
noncomputable section
=======
noncomputable section mysection
>>>>>>> 146e3f9b4f98ffcb291b86fb632581c6ed567b20

#check Ordinal.toType ω₁
#check ω₁


def Ico01 := (Ico (0:ℝ)  1)

--/-- Long line -/
--def L := (ω_ 1).toType ×ₗ Ico01

/-- Long line -/
def L := (ω_ 1 : Ordinal.{0}).toType ×ₗ Ico01

noncomputable example : PartialOrder (ω_ 1).toType := by infer_instance
noncomputable example : PartialOrder Ico01 := by infer_instance
noncomputable example : PartialOrder ((ω_ 1).toType ×ₗ Ico01) := by infer_instance
#synth PartialOrder ((ω_ 1).toType ×ₗ Ico01)
noncomputable instance : PartialOrder L := Prod.Lex.instPartialOrder (ω_ 1).toType ↑Ico01
instance : TopologicalSpace L := Preorder.topology L
def onehalf_Ico01 : Ico01 := ⟨(1/2: ℝ) , ⟨by norm_num, by norm_num⟩⟩

def S: Set L := { p | p.2 = onehalf_Ico01 }

example: DiscreteTopology S := by sorry

example: ¬ S.Countable:= sorry




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
  have h2: ∀ (K : Set S) , IsOpen K  → ∃(Uₖ: Set X), IsOpen Uₖ ∧ Uₖ ∩ S = K := by
    --change ∃ (U : Set X), IsOpen U ∧ (fun (s : S) ↦ s.val) ⁻¹' U = K at K_open
    intro K K_open
    obtain ⟨U, U_open, hU⟩ := K_open
    refine ⟨U, U_open, ?_⟩
    simp [← hU]
    exact inter_comm U S
  simp only [nonempty_subtype] at hS
  have h3: ∀ (a : ↑S),  ∃(Uₖ: Set X), IsOpen Uₖ ∧ Subtype.val ⁻¹' Uₖ  = {a} := by
    intro a
    specialize h1 a
    specialize h2 {a} h1
    exact h1
<<<<<<< HEAD

  have h4: ∀ (a : ↑S), ∃ bₐ ∈  B, Subtype.val ⁻¹' bₐ  = {a} := by
    intro a
    specialize h3 a
    cases' h3 with U hU
    cases' hU with hU1 hU2
    have hBasis: ∀ s: Set X, IsOpen s →  ∀ a ∈ s, ∃ t ∈ B, a ∈ t ∧ t ⊆ s:= by
      exact fun s a a_2 a_3 ↦ IsTopologicalBasis.exists_subset_of_mem_open hB2 a_3 a
    specialize hBasis U hU1
    specialize hBasis a
    have ha: a ∈ ({a}: Set S) := rfl
    have hau: a ∈ Subtype.val ⁻¹' U := by
      rw[hU2]
      exact ha
    have hau1: Subtype.val a ∈ U := by exact hau
    apply hBasis at hau1
    cases' hau1 with t ht
    cases' ht with ht1 ht2
    cases' ht2 with ht2 ht3
    use t
    constructor
    ·
      exact ht1
    ·
      ext x
      constructor
      ·
        intro hx
        have hx1: x ∈ Subtype.val ⁻¹' U := by exact ht3 hx
        rw[hU2] at hx1
        exact hx1
      ·
        intro hx
        exact mem_of_eq_of_mem hx ht2

  rw[countable_iff_exists_injOn] at hBc h
  cases' hBc with f hf
  choose g hg using h4
  have hginj: InjOn g (Subtype.val⁻¹' S) ∧ (g '' (Subtype.val⁻¹' S) ⊆ B) := by
    constructor
    unfold InjOn
    intro x1 hx1 x2 hx2
    have hg1:= hg
    specialize hg x1
    specialize hg1 x2
    intro hdiff
    by_contra hx12
    cases' hg with hgb hg
    cases' hg1 with hg1b hg1
    ·
      have h1: ({x1}:Set { x // x ∈ S })  ≠ {x2}:= by exact ne_of_mem_of_not_mem' rfl hx12
      rw[← hg] at h1
      rw[← hg1] at h1
      have h2: ((Subtype.val ⁻¹' g x1):Set { x // x ∈ S }) = Subtype.val ⁻¹' g x2 := by
        exact congrArg (preimage Subtype.val) hdiff
      exact h1 h2
    ·
      rw[Set.subset_def]
      intro x hx
      obtain ⟨a, haS, rfl⟩ := hx
      exact (hg a).1
  cases' hginj with hg1 hg2
  let k:= f ∘ g
  have hk: InjOn k (Subtype.val⁻¹' S) := by
    unfold InjOn
    intro a₁ ha₁ a₂ ha₂ hfg
    have hB₁ : g a₁ ∈ B := hg2 (Set.mem_image_of_mem g ha₁)
    have hB₂ : g a₂ ∈ B := hg2 (Set.mem_image_of_mem g ha₂)
    have hg_eq : g a₁ = g a₂ := hf hB₁ hB₂ hfg
    exact hg1 ha₁ ha₂ hg_eq
  let f' : X → ℕ := λ x => if hxS : x ∈ S then k ⟨x, hxS⟩ else 0
  have f'_inj : Set.InjOn f' S := by
    intros x₁ hx₁ x₂ hx₂ heq
    simp [f', hx₁, hx₂] at heq
    apply hk at heq
    simp only [Subtype.mk.injEq, f', k] at heq
    exact heq





=======
>>>>>>> 146e3f9b4f98ffcb291b86fb632581c6ed567b20

  have h4: ∀ (a : ↑S), ∃ bₐ ∈  B, Subtype.val ⁻¹' bₐ  = {a} := by
    intro a
    specialize h3 a
    cases' h3 with U hU
    cases' hU with hU1 hU2
    have hBasis: ∀ s: Set X, IsOpen s →  ∀ a ∈ s, ∃ t ∈ B, a ∈ t ∧ t ⊆ s:= by
      exact fun s a a_2 a_3 ↦ IsTopologicalBasis.exists_subset_of_mem_open hB2 a_3 a
    specialize hBasis U hU1
    specialize hBasis a
    have ha: a ∈ ({a}: Set S) := rfl
    have hau: a ∈ Subtype.val ⁻¹' U := by
      rw[hU2]
      exact ha
    have hau1: Subtype.val a ∈ U := by exact hau
    apply hBasis at hau1
    cases' hau1 with t ht
    cases' ht with ht1 ht2
    cases' ht2 with ht2 ht3
    use t
    constructor
    ·
      exact ht1
    ·
      ext x
      constructor
      ·
        intro hx
        have hx1: x ∈ Subtype.val ⁻¹' U := by exact ht3 hx
        rw[hU2] at hx1
        exact hx1
      ·
        intro hx
        exact mem_of_eq_of_mem hx ht2

  rw[countable_iff_exists_injOn] at hBc h
  cases' hBc with f hf
  choose g hg using h4
  have hginj: InjOn g (Subtype.val⁻¹' S) ∧ (g '' (Subtype.val⁻¹' S) ⊆ B) := by
    constructor
    unfold InjOn
    intro x1 hx1 x2 hx2
    have hg1:= hg
    specialize hg x1
    specialize hg1 x2
    intro hdiff
    by_contra hx12
    cases' hg with hgb hg
    cases' hg1 with hg1b hg1
    ·
      have h1: ({x1}:Set { x // x ∈ S })  ≠ {x2}:= by exact ne_of_mem_of_not_mem' rfl hx12
      rw[← hg] at h1
      rw[← hg1] at h1
      have h2: ((Subtype.val ⁻¹' g x1):Set { x // x ∈ S }) = Subtype.val ⁻¹' g x2 := by
        exact congrArg (preimage Subtype.val) hdiff
      exact h1 h2
    ·
      rw[Set.subset_def]
      intro x hx
      obtain ⟨a, haS, rfl⟩ := hx
      exact (hg a).1
  cases' hginj with hg1 hg2
  let k:= f ∘ g
  have hk: InjOn k (Subtype.val⁻¹' S) := by
    unfold InjOn
    intro a₁ ha₁ a₂ ha₂ hfg
    have hB₁ : g a₁ ∈ B := hg2 (Set.mem_image_of_mem g ha₁)
    have hB₂ : g a₂ ∈ B := hg2 (Set.mem_image_of_mem g ha₂)
    have hg_eq : g a₁ = g a₂ := hf hB₁ hB₂ hfg
    exact hg1 ha₁ ha₂ hg_eq
  let f' : X → ℕ := λ x => if hxS : x ∈ S then k ⟨x, hxS⟩ else 0
  have f'_inj : Set.InjOn f' S := by
    intros x₁ hx₁ x₂ hx₂ heq
    simp [f', hx₁, hx₂] at heq
    apply hk at heq
    ·
      simp only [Subtype.mk.injEq, f', k] at heq
      exact heq
    ·
      exact hx₁
    ·
      exact hx₂
  have hcontra:∃f : X → ℕ, InjOn f S  := Exists.intro f' f'_inj
  exact h hcontra

--#print axioms not_second_countable_if_uncountable_discrete_subset

theorem firstCountable_LongLine : FirstCountableTopology L := by

  constructor
  intro a
  rw[Filter.isCountablyGenerated_iff_exists_antitone_basis]
  let a2 := a.2
  --def f: ℕ → Set L := fun x => { p | p.1 = a.1, p.2 = (a2 - 1 / x , a2 + 1/x) } define a function like this


  sorry

theorem not_secondCountable_LongLine: ¬ SecondCountableTopology L:= by
  let S' : Set L := S
  have hs: DiscreteTopology S := by sorry
  sorry
