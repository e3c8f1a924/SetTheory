import SetTheory.ZFC
import SetTheory.Relations

namespace SetTheory
namespace Omega

open Classical

/- Set ω -/
noncomputable def ω := separate infinity_set_instance (λ x: Set => ∀ y: Set, set_inductive y → x ∈ y)

/- Mathematical induction -/
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

/- Other properties -/
theorem in_ω_subset: ∀ (x: Set), x ∈ ω → x ⊆ ω := by
  apply by_mathematical_induction_on_ω
  . intro x; simp [law_of_emptyset]
  . intro x Hx1 Hx2; unfold set_succ; intro y Hy
    apply (Or.elim (in_union_elim Hy))
    . intro Hy1; apply Hx2; trivial
    . intro Hy1; let Hy2 := in_singleset_elim Hy1; rewrite [Hy2]; trivial
theorem nat_succ_is_nat: ∀ {x: Set}, x ∈ ω → x⁺ ∈ ω := by
  apply ω_inductive.right
theorem nat_pre_in_nat: ∀ {y: Set}, y ∈ ω → (∀ {x: Set}, x⁺ ∈ y → x ∈ y) := by
  apply by_mathematical_induction_on_ω
  . intro x Hx; exfalso; apply law_of_emptyset (x⁺); trivial
  . intro y Hy Hi x Hx1; apply Or.elim (in_union_elim Hx1)
    . intro Hx2; apply sube_succ; apply Hi Hx2
    . rewrite [law_of_singleset]; intro Hx2; rewrite [← Hx2]
      apply sube_succ; apply in_succ
theorem emptyset_in_nat_succ: ∀ {x: Set}, x ∈ ω → ∅ ∈ x⁺ := by
  apply by_mathematical_induction_on_ω
  . apply in_union_intro; right; apply in_singleset_intro; trivial
  . intro x Hx Hx1; apply in_union_intro; left; trivial
theorem nat_pre_eq_unionset: ∀ {x: Set}, x ∈ ω → x = ⋃ (x⁺) := by
  apply by_mathematical_induction_on_ω
  . apply set_eq_intro; intro z; simp [law_of_emptyset, law_of_unionset]; intro x Hx Hz;
    apply Or.elim (in_union_elim Hx);
    . apply law_of_emptyset
    . rewrite [law_of_singleset]; intro Hx1; rewrite [Hx1] at Hz; apply law_of_emptyset z; trivial
  . intro x Hx Hi; apply set_eq_intro; intro z
    apply Iff.intro
    . intro Hz; apply Or.elim (in_union_elim Hz);
      . intro Hz1; apply in_unionset_intro x;
        . apply sube_succ (x⁺) x (in_succ x)
        . trivial
      . rewrite [law_of_singleset]; intro Hz1;
        rewrite [Hz1]; apply in_unionset_intro (x⁺)
        . apply in_succ
        . apply in_succ
    . intro Hz; let ⟨t, Ht1, Ht2⟩ := in_unionset_elim Hz
      apply Or.elim (in_union_elim Ht1)
      . intro Ht; let H1 := in_unionset_intro t Ht Ht2
        rewrite [← Hi] at H1
        apply in_union_intro; left; trivial
      . rewrite [law_of_singleset]; intro Ht; rewrite [Ht] at Ht2; trivial
theorem nat_succ_eq_elim: ∀ {x y: Set}, x ∈ ω → y ∈ ω → x⁺ = y⁺ → x = y := by
  intro x y Hx Hy Ht; rewrite [nat_pre_eq_unionset Hx]; rewrite [nat_pre_eq_unionset Hy]; rewrite [Ht]; trivial
theorem nat_partially_inductive: ∀ {x: Set}, x ∈ ω → x ≠ ∅ → ∅ ∈ x ∧ (∀ y: Set, y ∈ x → y⁺ = x ∨ y⁺ ∈ x) := by
  apply by_mathematical_induction_on_ω
  . intro H1; exfalso; apply H1; trivial
  . intro x Hx Hi Hx1; apply And.intro
    . apply emptyset_in_nat_succ; trivial
    . intro y Hy; apply Or.elim (in_union_elim Hy)
      . intro Hy1; right; apply Or.elim (em (x = ∅))
        . intro Hx2; rewrite [Hx2] at Hy1; exfalso; apply law_of_emptyset y; trivial
        . intro Hx2; apply Or.elim ((Hi Hx2).right y Hy1)
          . intro Hy2; rewrite [Hy2]; apply in_succ
          . intro Hy2; apply sube_succ x; trivial
      . rewrite [law_of_singleset]
        intro H; rewrite [H]; left; trivial
theorem nat_in_or_eq: ∀ {x y: Set}, x ∈ ω → y ∈ ω → x = y ∨ x ∈ y ∨ y ∈ x := by
  let T: ∀ {x: Set}, x ∈ ω → (∀ {y: Set}, y ∈ ω → x = y ∨ x ∈ y ∨ y ∈ x) := by
    apply by_mathematical_induction_on_ω
    . intro y Hy; apply Or.elim (em (∅ = y))
      . intro H1; simp [H1]
      . intro H2; right; left; rewrite [Eq.comm] at H2
        let ⟨z, Hz1, Hz2⟩ := ω_pre y Hy H2
        rewrite [← Hz2]; apply emptyset_in_nat_succ Hz1
    . intro x Hx Hi y Hy; apply Or.elim (Hi Hy)
      . intro H1; rewrite [H1]; right; right; apply in_succ
      . intro Ht; apply Or.elim Ht
        . intro Hx1; apply Or.elim (em (x⁺ = y))
          . intro H; simp [H]
          . intro H1; let H2 := (nat_partially_inductive Hy (set_ne_intro Hx1)).right x Hx1;
            apply Or.elim H2
            . intro H; simp [H]
            . intro H; simp [H]
        . intro Hy1; right; right; apply sube_succ; trivial
  intro x y Hx Hy; apply T; repeat trivial
theorem nat_total_ordered: ∀ {x y: Set}, x ∈ ω → y ∈ ω → x ⊆ y ∨ y ⊆ x := by
  let T: ∀ {x: Set}, x ∈ ω → (∀ {y: Set}, y ∈ ω → x ⊆ y ∨ y ⊆ x) := by
    apply by_mathematical_induction_on_ω
    . intro y Hy; left; intro z Hz; exfalso; apply law_of_emptyset _ Hz
    . intro x Hx Hi y Hy
      apply Or.elim (Hi Hy)
      . intro Hx1; apply Or.elim (em (x = y))
        . intro H1; rewrite [H1]; right; apply sube_succ
        . intro H1; left; intro t Ht; apply Or.elim (in_union_elim Ht)
          . apply Hx1
          . rewrite [law_of_singleset]; intro Ht1; rewrite [Ht1]
            apply Or.elim (nat_in_or_eq Hx Hy)
            . intro Hp; exfalso; apply H1; trivial
            . intro Hp; apply Or.elim Hp
              . simp
              . intro Hyx; let Hr := Hx1 _ Hyx
                exfalso; apply not_in_self y; trivial
      . intro Hx1; right; intro t Ht; apply sube_succ x; apply Hx1; trivial
  intro x y Hx Hy; apply T; repeat trivial
theorem nat_intersect_is_nat: ∀ {x y: Set}, x ∈ ω → y ∈ ω → (x ∩ y) ∈ ω := by
  intro x y Hx Hy; apply Or.elim (nat_total_ordered Hx Hy)
  . intro Hxy; let T: x ∩ y = x := by
      apply set_eq_intro; intro z; rewrite [law_of_intersect]; simp; apply Hxy
    rewrite [T]; trivial
  . intro Hxy; let T: x ∩ y = y := by
      apply set_eq_intro; intro z; rewrite [law_of_intersect]; simp; apply Hxy
    rewrite [T]; trivial
theorem nat_sube_succ_sube: ∀ {x y: Set}, x ∈ ω → y ∈ ω → x ⊆ y → x⁺ ⊆ y⁺ := by
  intro x y Hx Hy Hxy; intro t Ht; apply Or.elim (in_union_elim Ht);
  . intro Ht1; let Ht2 := Hxy _ Ht1; apply sube_succ; trivial
  . rewrite [law_of_singleset]; intro Ht1; rewrite [Ht1]
    apply Or.elim (nat_in_or_eq Hx Hy)
    . intro Hx1; rewrite [Hx1]; apply in_succ
    . intro H; apply Or.elim H
      . intro Hx1; apply sube_succ; trivial
      . intro Hy1; exfalso; apply not_in_self y (Hxy _ Hy1)
theorem nat_in_sube: ∀ {x y: Set}, x ∈ ω → y ∈ ω → x ∈ y → x ⊆ y := by
  intro x y Hx Hy Hxy; apply Or.elim (nat_total_ordered Hx Hy)
  . simp
  . intro H1; let H2 := H1 _ Hxy; let H3 := not_in_self _ H2; exfalso; trivial
theorem nat_sube_in_succ: ∀ {x y: Set}, x ∈ ω → y ∈ ω → x ⊆ y → x ∈ y⁺ := by
  intro x y Hx Hy Hxy; apply Or.elim (nat_in_or_eq Hx (nat_succ_is_nat Hy))
  . intro H1; rewrite [H1] at Hxy; let Hyx := Hxy _ (in_succ y)
    exfalso; apply not_in_self y; trivial
  . intro H; apply Or.elim H
    . simp
    . intro H1; let H2 := Hxy _ H1; let H3 := sube_succ y _ H2
      exfalso; apply not_in_self (y⁺); trivial

end Omega
end SetTheory
