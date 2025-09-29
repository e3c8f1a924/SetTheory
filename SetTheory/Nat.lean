import SetTheory.ZFC
import SetTheory.Relations

namespace SetTheory
namespace Omega

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


/- Recursive Maps -/
theorem in_ω_subset: ∀ (x: Set), x ∈ ω → x ⊆ ω := by
  apply by_mathematical_induction_on_ω
  . intro x; simp [law_of_emptyset]
  . intro x Hx1 Hx2; unfold set_succ; intro y Hy
    apply (Or.elim (in_union_elim Hy))
    . intro Hy1; apply Hx2; trivial
    . intro Hy1; let Hy2 := in_singleset_elim Hy1; rewrite [Hy2]; trivial
theorem nat_succ_is_nat: ∀ {x: Set}, x ∈ ω → x⁺ ∈ ω := by
  apply ω_inductive.right
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
noncomputable def map_recursive (z t f: Set) :=
  (f ⸨∅⸩ = z) ∧
  (∀ x: Set, x ∈ ω → f ⸨x⁺⸩ = t ⸨(⸨x, (f ⸨x⸩)⸩)⸩)
theorem exists_recursive_map: ∀ (B z t: Set), z ∈ B → t ∈ ω × B ↪ B → ∃ (f: Set), f ∈ ω ↪ B ∧ map_recursive z t f := by
  intro B z t Hz Ht;
  let partially_recursive (A z t f: Set) := (f ⸨∅⸩ = z) ∧
    (∀ x: Set, x ∈ A → (x⁺ ∈ A) → f ⸨x⁺⸩ = t ⸨(⸨x, (f ⸨x⸩)⸩)⸩)
  let f := ⋃ transform ω (λ x => ⋃ separate (x⁺ ↪ B) (partially_recursive (x⁺) z t))
  let exists_partially_recursive_map: ∀ (x: Set), x ∈ ω → ∃ f, f ∈ separate (x⁺ ↪ B) (partially_recursive (x⁺) z t) := by
    apply by_mathematical_induction_on_ω
    . unfold set_succ; exists (⦃(⸨∅, z⸩)⦄)
      apply in_separate_intro
      . unfold mapset; apply in_separate_intro
        . apply in_powerset_intro; intro k; rewrite [law_of_singleset]; intro H'; rewrite [H']
          apply pair_in_cartesian_product_intro;
          . apply in_union_intro; right; apply in_singleset_intro; trivial
          . trivial
        . unfold is_map; intro x; intro H; apply Or.elim (in_union_elim H)
          . intro H'; exfalso; apply law_of_emptyset x; trivial
          . intro H'; let H'' := in_singleset_elim H'; rewrite [H'']; exists z
            apply set_eq_intro; intro k; rewrite [law_of_relation_class]
            unfold in_relation; rewrite [law_of_singleset]; rewrite [pair_eq_iff]; rewrite [law_of_singleset]; simp
      . unfold partially_recursive; apply And.intro
        . unfold map_eval; let H1: ⟦(⦃(⸨∅, z⸩)⦄),∅⟧ = ⦃z⦄ := by
            apply set_eq_intro; intro k; rewrite [law_of_relation_class]
            unfold in_relation; rewrite [law_of_singleset]; rewrite [law_of_singleset]
            rewrite [pair_eq_iff]; simp
          rewrite [H1]; rewrite [law_of_unionset_singleset]; trivial
        . intro x; rewrite [law_of_binary_union]; rewrite [law_of_singleset]; simp [law_of_emptyset]
          intro Hx; rewrite [Hx]; unfold set_succ; rewrite [law_of_binary_union]; simp [law_of_emptyset]
          rewrite [law_of_singleset]; intro H1; let H2 := (set_eq_elim H1 ∅); simp [law_of_binary_union, law_of_singleset, law_of_emptyset] at H2
    . intro x Hx ⟨g', Hg'⟩; let g := g' ∪ ⦃(⸨(x⁺), (t ⸨(⸨x, (g' ⸨x⸩)⸩)⸩)⸩)⦄
      exists g; unfold g
      let Hmap: (g' ∪ ⦃(⸨(x⁺), (t⸨⸨x, (g'⸨x⸩)⸩⸩)⸩)⦄) ∈ (x⁺)⁺ ↪ B := by
        unfold mapset; apply in_separate_intro; apply in_powerset_intro
        intro k; rewrite [law_of_binary_union]; intro H'; apply Or.elim H'
        . intro Hk; let Hg'1 := (in_separate_elim Hg').left; unfold mapset at Hg'1
          let ⟨a, b, Hab1, Hab2, Hab3⟩ := in_cartesian_product_elim ((in_powerset_elim (in_separate_elim Hg'1).left) k Hk)
          rewrite [Hab3]; apply pair_in_cartesian_product_intro
          . unfold set_succ; apply in_union_intro; left; apply Hab1
          . apply Hab2
        . rewrite [law_of_singleset]; intro Hk; rewrite [Hk]
          apply pair_in_cartesian_product_intro
          . apply in_succ
          . apply map_eval_in_codomain t (ω × B) B
            . trivial
            . apply pair_in_cartesian_product_intro
              . trivial
              . let Hg'1 := (in_separate_elim Hg').left
                apply map_eval_in_codomain g' (x⁺) B
                . trivial
                . simp [in_succ]
        . unfold is_map; intro k Hk; unfold set_succ at Hk
          apply Or.elim (in_union_elim Hk)
          . intro Hk1; apply Or.elim (in_union_elim Hk1)
            . intro Hk2; exists (g'⸨k⸩)
              apply set_eq_intro; intro α
              rewrite [law_of_relation_class]; rewrite [law_of_singleset]
              unfold in_relation; apply Iff.intro
              . intro Hp; apply Or.elim (in_union_elim Hp)
                . intro Hkα; apply Eq.symm; let Hg'1 := (in_separate_elim Hg').left
                  rewrite [law_of_map_eval g' (x⁺) B k α Hg'1]
                  . trivial
                  . unfold set_succ; apply in_union_intro; left; trivial
                . intro Hkα; let ⟨Hk3, Hα⟩ := pair_eq_elim (in_singleset_elim Hkα)
                  rewrite [Hk3] at Hk2; let Hk4 := sube_succ x _ Hk2; exfalso; apply not_in_self (x⁺); trivial
              . intro Hα; rewrite [Hα]; apply in_union_intro; left
                let Hg'1 := (in_separate_elim Hg').left; let H2 := map_eval_in_map g' (x⁺) B k Hg'1 Hk1;
                apply H2
            . rewrite [law_of_singleset]; intro Hk2; rewrite [Hk2]
              exists (g'⸨x⸩); apply set_eq_intro; intro α; rewrite [law_of_singleset]
              rewrite [law_of_relation_class]; unfold in_relation; apply Iff.intro
              . intro Hxα; apply Or.elim (in_union_elim Hxα)
                . intro Hxα1; apply Eq.symm; let Hg'1 := (in_separate_elim Hg').left
                  rewrite [law_of_map_eval g' (x⁺) B x α Hg'1 (in_succ x)]; apply Hxα1
                . intro Hxα1; let ⟨H1, H2⟩ := pair_eq_elim (in_singleset_elim Hxα1)
                  let H3 := set_eq_elim H1 x; simp [in_succ, not_in_self] at H3
              . intro Hα; rewrite [Hα]; apply in_union_intro; left
                let Hg'1 := (in_separate_elim Hg').left; let H2 := map_eval_in_map g' (x⁺) B x Hg'1 (in_succ x)
                apply H2
          . rewrite [law_of_singleset]; intro Hk2; rewrite [Hk2]
            exists (t ⸨(⸨x, (g' ⸨x⸩)⸩)⸩); apply set_eq_intro
            intro α; rewrite [law_of_relation_class]; rewrite [law_of_singleset]
            apply Iff.intro
            . intro H1; apply Or.elim (in_union_elim H1)
              . intro H2; let Hg'1 := (in_separate_elim Hg').left
                unfold mapset at Hg'1; let Hg'2 := (pair_in_cartesian_product_elim ((in_powerset_elim (in_separate_elim Hg'1).left) (⸨(x⁺), α⸩) H2)).left
                simp [not_in_self] at Hg'2
              . intro H2; let H3 := (pair_eq_elim (in_singleset_elim H2)).right
                trivial
            . intro Hα; rewrite [Hα]; unfold in_relation
              apply in_union_intro; right; apply in_singleset_intro; trivial
      apply in_separate_intro
      . trivial
      . unfold partially_recursive;
        let Hprg' := (in_separate_elim Hg').right
        let Hmg' := (in_separate_elim Hg').left
        apply And.intro
        . let Hx'' := emptyset_in_nat_succ (nat_succ_is_nat Hx)
          let Hx' := emptyset_in_nat_succ Hx
          rewrite [law_of_map_eval (g' ∪ ⦃(⸨(x⁺), (t⸨⸨x, (g'⸨x⸩)⸩⸩)⸩)⦄) ((x⁺)⁺) B ∅ z Hmap Hx''];
          apply in_union_intro; left; let Ht := law_of_map_eval g' (x⁺) B ∅ z Hmg' Hx'; unfold in_relation at Ht
          rewrite [← Ht]; apply Hprg'.left
        . intro k Hk Hk'; rewrite [law_of_map_eval (g' ∪ ⦃(⸨(x⁺), (t⸨⸨x, (g'⸨x⸩)⸩⸩)⸩)⦄) ((x⁺)⁺) B (k⁺) (t⸨⸨ k,((g'∪⦃ (⸨ (x⁺),(t⸨⸨ x,(g'⸨x⸩) ⸩⸩) ⸩) ⦄)⸨k⸩) ⸩⸩) Hmap Hk']
          apply in_union_intro
          apply Or.elim (in_union_elim Hk')
          . intro Hk''; left; apply Or.elim (in_union_elim Hk)
            . intro Hk1; let H1: (g'∪⦃ (⸨ (x⁺),(t⸨⸨ x,(g'⸨x⸩) ⸩⸩) ⸩) ⦄)⸨k⸩ = g'⸨k⸩ := by
                rewrite [law_of_map_eval (g' ∪ ⦃(⸨(x⁺), (t⸨⸨x, (g'⸨x⸩)⸩⸩)⸩)⦄) ((x⁺)⁺) B _ _ Hmap Hk]
                apply in_union_intro; left; let T := law_of_map_eval g' (x⁺) B k (g'⸨k⸩) Hmg' Hk1
                simp at T; unfold in_relation at T; trivial
              rewrite [H1]; let H2 := Hprg'.right k Hk1 Hk'';
              rewrite [law_of_map_eval g' (x⁺) B _ _ Hmg' Hk''] at H2; unfold in_relation at H2; trivial
            . intro Hk2; let Hk3 := in_singleset_elim Hk2; rewrite [Hk3] at Hk'; simp [not_in_self] at Hk'
          . rewrite [law_of_singleset]; intro Hk1; rewrite [Hk1]; right; rewrite [law_of_singleset]
            apply pair_eq_intro; simp; let Hkn := in_ω_subset _ (nat_succ_is_nat (nat_succ_is_nat Hx)) k Hk
            let Hk2 := nat_succ_eq_elim Hkn Hx Hk1
            rewrite [Hk2]; let HT: ((g'∪⦃ (⸨ (x⁺),(t⸨⸨ x,(g'⸨x⸩) ⸩⸩) ⸩) ⦄)⸨x⸩) = g'⸨x⸩ := by
              rewrite [law_of_map_eval _ _ _ _ _ Hmap (sube_succ (x⁺) x (in_succ x))]
              apply in_union_intro; left; let T := law_of_map_eval g' (x⁺) B x (g'⸨x⸩) Hmg' (in_succ x);
              simp at T; unfold in_relation at T; trivial
            rewrite [HT]; trivial
  sorry

noncomputable def ω_recursive_maps (B z t: Set) := separate (ω ↪ B) (map_recursive z t)

end Omega
end SetTheory
