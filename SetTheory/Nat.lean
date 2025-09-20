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
theorem mathematical_induction_on_ω: ∀ (P: Set → Prop), P ∅ → (∀ x: Set, x ∈ ω → (P x → P (x⁺))) → ∀ x: Set, x ∈ ω → P x := by
  intro P HP0 HPs
  let ω' := separate ω P
  let HIω': set_inductive ω' := by
    apply And.intro
    . apply in_separate_intro
      . apply ω_inductive.left
      . trivial
    . intro y Hy; let ⟨Hy1, Hy2⟩ := in_separate_elim Hy
      apply in_separate_intro
      . apply ω_inductive.right; trivial
      . apply HPs; trivial; trivial
  let Hω: ω = ω' := by
    apply set_eq_intro; intro z; apply Iff.intro
    . unfold ω; rewrite [law_of_separate]; intro ⟨_, H1⟩
      apply H1; apply HIω'
    . intro H'; let H'' := in_separate_elim H'
      apply H''.left
  let Hω1 := set_eq_elim Hω
  intro x; let Hωx := Hω1 x
  rewrite [law_of_separate] at Hωx
  simp at Hωx
  trivial
theorem by_mathematical_induction_on_ω: ∀ {P: Set → Prop}, P ∅ → (∀ x: Set, x ∈ ω → (P x → P (x⁺))) → ∀ x: Set, x ∈ ω → P x := by
  apply mathematical_induction_on_ω

end SetTheory
