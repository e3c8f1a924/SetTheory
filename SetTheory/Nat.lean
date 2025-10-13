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
noncomputable def map_recursive (z t f: Set) :=
  (f ⸨∅⸩ = z) ∧
  (∀ x: Set, x ∈ ω → f ⸨x⁺⸩ = t ⸨(f ⸨x⸩)⸩)
noncomputable def partially_recursive (A z t f: Set) := (f ⸨∅⸩ = z) ∧
    (∀ x: Set, x ∈ A → (x⁺ ∈ A) → f ⸨x⁺⸩ = t ⸨(f ⸨x⸩)⸩)
noncomputable def partially_recursive_map_constructor (B z t x: Set) := ⋃ separate (x⁺ ↪ B) (partially_recursive (x⁺) z t)
noncomputable def recursive_map_constructor (B z t: Set) := ⋃ transform ω (λ x => partially_recursive_map_constructor B z t x)
theorem law_of_recursive_map: ∀ (B z t: Set), z ∈ B → t ∈ B ↪ B → recursive_map_constructor B z t ∈ ω ↪ B ∧ map_recursive z t (recursive_map_constructor B z t) := by
  intro B z t Hz Ht;
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
    . intro x Hx ⟨g', Hg'⟩; let g := g' ∪ ⦃(⸨(x⁺), (t ⸨((g' ⸨x⸩))⸩)⸩)⦄
      exists g; unfold g
      let Hmap: (g' ∪ ⦃(⸨(x⁺), (t⸨(g'⸨x⸩)⸩)⸩)⦄) ∈ (x⁺)⁺ ↪ B := by
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
          . apply map_eval_in_codomain t B B
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
            exists (t ⸨((g' ⸨x⸩))⸩); apply set_eq_intro
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
          rewrite [law_of_map_eval (g' ∪ ⦃(⸨(x⁺), (t⸨(g'⸨x⸩)⸩)⸩)⦄) ((x⁺)⁺) B ∅ z Hmap Hx''];
          apply in_union_intro; left; let Ht := law_of_map_eval g' (x⁺) B ∅ z Hmg' Hx'; unfold in_relation at Ht
          rewrite [← Ht]; apply Hprg'.left
        . intro k Hk Hk';
          rewrite [law_of_map_eval (g' ∪ ⦃(⸨(x⁺), (t⸨(g'⸨x⸩)⸩)⸩)⦄) ((x⁺)⁺) B (k⁺) (t⸨((g'∪⦃ (⸨ (x⁺),(t⸨(g'⸨x⸩) ⸩) ⸩) ⦄)⸨k⸩) ⸩) Hmap Hk']
          apply in_union_intro
          apply Or.elim (in_union_elim Hk')
          . intro Hk''; left; apply Or.elim (in_union_elim Hk)
            . intro Hk1; let H1: (g'∪⦃ (⸨ (x⁺),(t⸨(g'⸨x⸩) ⸩) ⸩) ⦄)⸨k⸩ = g'⸨k⸩ := by
                rewrite [law_of_map_eval (g' ∪ ⦃(⸨(x⁺), (t⸨(g'⸨x⸩)⸩)⸩)⦄) ((x⁺)⁺) B _ _ Hmap Hk]
                apply in_union_intro; left; let T := law_of_map_eval g' (x⁺) B k (g'⸨k⸩) Hmg' Hk1
                simp at T; unfold in_relation at T; trivial
              rewrite [H1]; let H2 := Hprg'.right k Hk1 Hk'';
              rewrite [law_of_map_eval g' (x⁺) B _ _ Hmg' Hk''] at H2; unfold in_relation at H2; trivial
            . intro Hk2; let Hk3 := in_singleset_elim Hk2; rewrite [Hk3] at Hk'; simp [not_in_self] at Hk'
          . rewrite [law_of_singleset]; intro Hk1; rewrite [Hk1]; right; rewrite [law_of_singleset]
            apply pair_eq_intro; simp; let Hkn := in_ω_subset _ (nat_succ_is_nat (nat_succ_is_nat Hx)) k Hk
            let Hk2 := nat_succ_eq_elim Hkn Hx Hk1
            rewrite [Hk2]; let HT: ((g'∪⦃ (⸨ (x⁺),(t⸨(g'⸨x⸩) ⸩) ⸩) ⦄)⸨x⸩) = g'⸨x⸩ := by
              rewrite [law_of_map_eval _ _ _ _ _ Hmap (sube_succ (x⁺) x (in_succ x))]
              apply in_union_intro; left; let T := law_of_map_eval g' (x⁺) B x (g'⸨x⸩) Hmg' (in_succ x);
              simp at T; unfold in_relation at T; trivial
            rewrite [HT]; trivial
  let partially_recursive_map_unique: ∀ (x: Set), x ∈ ω → ∃ (f: Set), separate (x⁺ ↪ B) (partially_recursive (x⁺) z t) = ⦃f⦄ := by
    apply by_mathematical_induction_on_ω
    . let ⟨f, Hf⟩ := exists_partially_recursive_map ∅ (ω_inductive.left)
      exists f; apply set_eq_intro; intro g; apply Iff.intro
      . rewrite [law_of_singleset]; intro Hg; let ⟨Hf1, Hf2⟩ := in_separate_elim Hf
        let ⟨Hg1, Hg2⟩ := in_separate_elim Hg; apply map_eq_intro Hg1 Hf1
        . intro x Hx; apply Or.elim (in_union_elim Hx)
          . intro Hx1; simp [law_of_emptyset] at Hx1
          . rewrite [law_of_singleset]; intro Hx1; rewrite [Hx1];
            rewrite [Hf2.left]; rewrite [Hg2.left]; trivial
      . simp [law_of_singleset]; intro Hg; simp [Hg, Hf]
    . intro x Hx ⟨f', Hf'⟩; let ⟨f, Hf⟩ := exists_partially_recursive_map (x⁺) (nat_succ_is_nat Hx)
      exists f; apply set_eq_intro; intro g; rewrite [law_of_singleset]; apply Iff.intro
      . intro Hg; let ⟨Hf1, Hf2⟩ := in_separate_elim Hf; let ⟨Hg1, Hg2⟩ := in_separate_elim Hg
        apply map_eq_intro Hg1 Hf1; intro p;
        let H1: ∀ k: Set, k ∈ (x⁺) → f⸨k⸩ = g⸨k⸩ := by
          let _f := map_constructor (x⁺) (λ k: Set => f⸨k⸩)
          let Hqf: ∀ α, α ∈ (x⁺) → _f⸨α⸩ = f⸨α⸩ := by
                intro α Hα; unfold _f; rewrite [law_of_map_constructor_eval]; repeat trivial
          let H_f: _f ∈ separate (x⁺ ↪ B) (partially_recursive (x⁺) z t) := by
            apply in_separate_intro
            . unfold _f; unfold mapset; apply in_separate_intro
              . apply in_powerset_intro; intro q Hq
                unfold map_constructor at Hq; let ⟨r, Hr1, Hr2⟩ := in_transform_elim Hq
                rewrite [← Hr2]; simp; apply pair_in_cartesian_product_intro
                . trivial
                . apply map_eval_in_codomain f ((x⁺)⁺) B _ Hf1
                  apply sube_succ; trivial
              . apply map_constructor_is_map (x⁺) (λ k => f⸨k⸩)
            . unfold partially_recursive; apply And.intro
              . rewrite [Hqf ∅ (emptyset_in_nat_succ Hx)]
                apply Hf2.left
              . intro α Hα Hαs; rewrite [Hqf (α⁺) Hαs]
                rewrite [Hqf α Hα]; apply Hf2.right
                . apply sube_succ; trivial
                . apply sube_succ; trivial
          let _g := map_constructor (x⁺) (λ k: Set => g⸨k⸩)
          let Hqg: ∀ α, α ∈ (x⁺) → _g⸨α⸩ = g⸨α⸩ := by
                intro α Hα; unfold _g; rewrite [law_of_map_constructor_eval]; repeat trivial
          let H_g: _g ∈ separate (x⁺ ↪ B) (partially_recursive (x⁺) z t) := by
            apply in_separate_intro
            . unfold _g; unfold mapset; apply in_separate_intro
              . apply in_powerset_intro; intro q Hq
                unfold map_constructor at Hq; let ⟨r, Hr1, Hr2⟩ := in_transform_elim Hq
                rewrite [← Hr2]; simp; apply pair_in_cartesian_product_intro
                . trivial
                . apply map_eval_in_codomain g ((x⁺)⁺) B _ Hg1
                  apply sube_succ; trivial
              . apply map_constructor_is_map (x⁺) (λ k => g⸨k⸩)
            . unfold partially_recursive; apply And.intro
              . rewrite [Hqg ∅ (emptyset_in_nat_succ Hx)]
                apply Hg2.left
              . intro α Hα Hαs; rewrite [Hqg (α⁺) Hαs]
                rewrite [Hqg α Hα]; apply Hg2.right
                . apply sube_succ; trivial
                . apply sube_succ; trivial
          rewrite [Hf'] at H_f
          let H_f1 := in_singleset_elim H_f
          rewrite [Hf'] at H_g
          let H_g1 := in_singleset_elim H_g
          intro k Hk; rewrite [← Hqf k Hk]; rewrite [← Hqg k Hk]
          rewrite [H_f1]; rewrite [H_g1]; trivial
        intro Hp; apply Eq.symm
        apply Or.elim (in_union_elim Hp)
        . intro Hp1; apply H1 p Hp1
        . rewrite [law_of_singleset]; intro Hp1; rewrite [Hp1]
          rewrite [Hp1] at Hp; let Hp2 := nat_pre_in_nat (nat_succ_is_nat (nat_succ_is_nat Hx)) Hp
          rewrite [Hf2.right x Hp2 Hp]
          rewrite [Hg2.right x Hp2 Hp]
          apply Or.elim (in_union_elim Hp2)
          . intro Hx1; rewrite [H1 x Hx1]; trivial
          . rewrite [law_of_singleset]; intro Hx1; let Hx2 := in_succ x; rewrite [← Hx1] at Hx2; exfalso; apply not_in_self x Hx2
      . intro Hg; rewrite [Hg]; trivial
  let partially_recursive_map_constructor_partially_recursive: ∀ (x: Set), x ∈ ω → partially_recursive (x⁺) z t (partially_recursive_map_constructor B z t x) := by
    intro x Hx
    unfold partially_recursive_map_constructor
    let H1 := unionset_separate_single_elim (partially_recursive_map_unique x Hx)
    apply H1.right
  let partially_recursive_map_constructor_in_mapset: ∀ (x: Set), x ∈ ω → partially_recursive_map_constructor B z t x ∈ x⁺ ↪ B := by
    intro x Hx
    unfold partially_recursive_map_constructor
    let H1 := unionset_separate_single_elim (partially_recursive_map_unique x Hx)
    apply H1.left
  let partially_recursive_map_constructor_sube: ∀ (x y: Set), x ∈ ω → y ∈ ω → y ⊆ x → (partially_recursive_map_constructor B z t y) ⊆ partially_recursive_map_constructor B z t x := by
    intro x y Hx Hy Hyx α; intro Hp; let ⟨α, Hα, Hp1⟩ := in_map_elim (partially_recursive_map_constructor_in_mapset y Hy) Hp
    rewrite [Hp1]; apply in_map_intro (partially_recursive_map_constructor_in_mapset x Hx) (nat_sube_succ_sube Hy Hx Hyx _ Hα)
    apply pair_eq_intro
    . trivial
    . let HT: ∀ (β: Set), β ∈ ω → β ∈ y⁺ → partially_recursive_map_constructor B z t y⸨β⸩ = partially_recursive_map_constructor B z t x⸨β⸩ := by
        let Hpr1 := partially_recursive_map_constructor_partially_recursive x Hx
        let Hpr2 := partially_recursive_map_constructor_partially_recursive y Hy
        apply by_mathematical_induction_on_ω
        . intro Hn; rewrite [Hpr1.left]; rewrite [Hpr2.left]; trivial
        . intro β Hβ Hi Hβs; let Ht := nat_in_sube (nat_succ_is_nat Hβ) (nat_succ_is_nat Hy) Hβs _ (in_succ β); let Hi1 := Hi Ht
          rewrite [Hpr2.right β Ht Hβs]
          let Hβs1 := nat_sube_succ_sube Hy Hx Hyx _ Hβs
          let Ht1 := nat_sube_succ_sube Hy Hx Hyx _ Ht
          rewrite [Hpr1.right β Ht1 Hβs1]
          rewrite [Hi1]; trivial
      apply HT
      . apply in_ω_subset (y⁺) (nat_succ_is_nat Hy); trivial
      . trivial
  let recursive_map_constructor_in_mapset: recursive_map_constructor B z t ∈ ω ↪ B := by
    unfold mapset; apply in_separate_intro
    . apply in_powerset_intro; intro p Hp
      let ⟨f, Hf1, Hf2⟩ := in_unionset_elim Hp
      let ⟨x, Hx1, Hx2⟩ := in_transform_elim Hf1
      rewrite [← Hx2] at Hf2
      unfold partially_recursive_map_constructor at Hf2
      let ⟨α, Hα1, Hα2⟩ := in_unionset_elim Hf2
      let Hα3 := in_powerset_elim (in_separate_elim (in_separate_elim Hα1).left).left
      let ⟨β, γ, Hβ, Hγ, Hβγ⟩ := in_cartesian_product_elim (Hα3 _ Hα2)
      rewrite [Hβγ]; apply pair_in_cartesian_product_intro
      . apply in_ω_subset (x⁺) (nat_succ_is_nat Hx1); trivial
      . trivial
    . unfold is_map; intro x Hx; exists ((partially_recursive_map_constructor B z t x) ⸨x⸩)
      apply set_eq_intro; intro p; rewrite [law_of_singleset]
      rewrite [law_of_relation_class]; unfold in_relation; unfold recursive_map_constructor
      rewrite [law_of_unionset]; apply Iff.intro
      . intro ⟨r, Hr1, Hr2⟩; let ⟨α, Hα1, Hα2⟩ := in_transform_elim Hr1
        rewrite [← Hα2] at Hr2
        let T: ⸨x, p⸩ ∈ partially_recursive_map_constructor B z t x := by
          apply Or.elim (nat_total_ordered Hα1 Hx)
          . intro Hαx; apply partially_recursive_map_constructor_sube x α Hx Hα1 Hαx; trivial
          . intro Hxα; let HT: ⸨x, ((partially_recursive_map_constructor B z t x) ⸨x⸩)⸩ ∈ partially_recursive_map_constructor B z t x := by
              let H1 := law_of_map_eval _ _ _ _ ((partially_recursive_map_constructor B z t x) ⸨x⸩) (partially_recursive_map_constructor_in_mapset _ Hx) (in_succ x)
              unfold in_relation at H1; rewrite [← H1]; trivial
            let HT1 := partially_recursive_map_constructor_sube α x Hα1 Hx Hxα
            let HT2 := HT1 _ HT
            let ⟨β, Hβ⟩ := (in_separate_elim (partially_recursive_map_constructor_in_mapset _ Hα1)).right x (nat_sube_in_succ Hx Hα1 Hxα)
            let HT3 := set_eq_elim Hβ
            let HT4 := HT3 p;
            let HT5 := HT3 ((partially_recursive_map_constructor B z t x) ⸨x⸩)
            rewrite [law_of_singleset] at HT4 HT5
            rewrite [law_of_relation_class] at HT4 HT5
            unfold in_relation at HT4 HT5
            simp [Hr2] at HT4; simp [HT2] at HT5
            rewrite [HT4]; rewrite [← HT5]; trivial
        let HT1 := law_of_map_eval _ _ _ _ p (partially_recursive_map_constructor_in_mapset x Hx) (in_succ x)
        apply Eq.symm
        rewrite [HT1]; apply T
      . intro Hp; rewrite [Hp]; exists (partially_recursive_map_constructor B z t x)
        apply And.intro
        . apply in_transform_intro x
          . apply Hx
          . trivial
        . let H1 := law_of_map_eval (partially_recursive_map_constructor B z t x) (x⁺) B x (partially_recursive_map_constructor B z t x ⸨x⸩)
          simp at H1; let H2 := H1 (partially_recursive_map_constructor_in_mapset x Hx) (in_succ x)
          unfold in_relation at H2; trivial
  apply And.intro
  . trivial
  . unfold map_recursive; apply And.intro
    . rewrite [law_of_map_eval _ _ _ _ _ recursive_map_constructor_in_mapset ω_inductive.left]
      unfold in_relation
      unfold recursive_map_constructor
      apply in_unionset_intro (partially_recursive_map_constructor B z t ∅)
      . apply in_transform_intro ∅
        . apply ω_inductive.left
        . trivial
      . let HT := law_of_map_eval _ _ _ ∅ z (partially_recursive_map_constructor_in_mapset ∅ (ω_inductive.left)) (in_succ ∅)
        unfold in_relation at HT; rewrite [← HT]
        apply (partially_recursive_map_constructor_partially_recursive ∅ (ω_inductive.left)).left
    . intro x Hx; rewrite [law_of_map_eval _ _ _ _ _ recursive_map_constructor_in_mapset (nat_succ_is_nat Hx)]
      unfold in_relation; apply in_unionset_intro (partially_recursive_map_constructor B z t (x⁺))
      . apply in_transform_intro (x⁺)
        . apply nat_succ_is_nat Hx
        . trivial
      . let H1: (recursive_map_constructor B z t⸨x⸩) = (partially_recursive_map_constructor B z t (x⁺)) ⸨x⸩ := by
          rewrite [law_of_map_eval _ _ _ _ _ recursive_map_constructor_in_mapset Hx]
          unfold in_relation
          apply in_unionset_intro (partially_recursive_map_constructor B z t (x⁺))
          . apply in_transform_intro (x⁺)
            . apply nat_succ_is_nat Hx
            . trivial
          . let H1 := map_eval_in_map _ _ _ x (partially_recursive_map_constructor_in_mapset (x⁺) (nat_succ_is_nat Hx)) ((sube_succ (x⁺)) _ (in_succ x))
            unfold in_relation at H1; trivial
        rewrite [H1]; let HT := law_of_map_eval _ _ _ (x⁺) (t⸨(partially_recursive_map_constructor B z t (x⁺)⸨x⸩) ⸩) (partially_recursive_map_constructor_in_mapset (x⁺) (nat_succ_is_nat Hx)) (in_succ (x⁺))
        unfold in_relation at HT;
        rewrite [← HT]
        let HT1 := (partially_recursive_map_constructor_partially_recursive (x⁺) (nat_succ_is_nat Hx)).right x ((sube_succ (x⁺)) _ (in_succ x)) (in_succ (x⁺))
        trivial

end Omega
end SetTheory
