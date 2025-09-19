import SetTheory.ZFC

namespace SetTheory

open Classical

/- Set ω -/
noncomputable def ω := separate infinity_set_instance (λ x: Set => ∀ y: Set, set_inductive y → x ∈ y)

theorem ω_inductive: set_inductive ω := by
  unfold set_inductive; unfold ω; apply And.intro
  . apply in_separate_intro
    . apply axiom_of_infinity.left
    . intro y Hy; unfold set_inductive at Hy
      apply Hy.left
  . intro x Hx; let ⟨Hx1, Hx2⟩ := in_separate_elim Hx
    apply in_separate_intro
    . apply axiom_of_infinity.right; trivial
    . intro y Hy; apply Hy.right; apply Hx2; trivial
theorem ω_pre: ∀ x: Set, x ∈ ω → x ≠ ∅ → ∃ y, y ∈ ω ∧ y⁺ = x := by
  intro x Hx Hxne; apply byContradiction; intro H; simp at H
  let α := ω \ ⦃x⦄; let Hα: set_inductive α := by
    apply And.intro
    . apply in_setminus_intro
      . apply ω_inductive.left
      . intro H'; apply Hxne
        rewrite [Eq.comm]; apply in_singleset_elim; trivial
    . intro y Hy; let ⟨Hy1, Hy2⟩ := in_setminus_elim Hy; apply in_setminus_intro
      . apply ω_inductive.right; trivial
      . intro Hy'; let Hy3 := in_singleset_elim Hy'; apply H y; trivial; trivial
  let ⟨Hx1, Hx2⟩ := in_separate_elim Hx
  let Hx3: x ∉ α := by
    intro H'; let H'' := in_separate_elim H'
    apply H''.right; apply in_singleset_intro; trivial
  apply Hx3; apply Hx2; trivial

end SetTheory
