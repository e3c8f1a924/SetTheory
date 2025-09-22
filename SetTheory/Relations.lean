import SetTheory.ZFC

namespace SetTheory

open Classical

/- Cartesian Product -/
noncomputable def cartesian_product (x: Set) (y: Set) := separate (𝒫 (𝒫 (x ∪ y))) (λ t: Set => ∃ (a b: Set), a ∈ x ∧ b ∈ y ∧ t = ⸨a, b⸩)
notation:115 a:115 "×" b: 115  => cartesian_product a b
theorem law_of_cartesian_product: ∀ (x y z: Set), z ∈ x × y ↔ ∃ (a b: Set), a ∈ x ∧ b ∈ y ∧ z = ⸨a, b⸩ := by
  intro x y z; unfold cartesian_product; rewrite [law_of_separate]; simp
  intro a Ha b Hb Hz; apply in_powerset_intro; intro t Ht; apply in_powerset_intro
  intro k Hk; apply in_union_intro; rewrite [Hz] at Ht; unfold pair at Ht
  apply Or.elim (in_unordered_pair_elim Ht)
  . intro Ht1; rewrite [Ht1] at Hk; let Hk1 := in_singleset_elim Hk; rewrite [Hk1]; left; trivial
  . intro Ht1; rewrite [Ht1] at Hk; apply Or.elim (in_unordered_pair_elim Hk)
    . intro Hk2; rewrite [Hk2]; left; trivial
    . intro Hk2; rewrite [Hk2]; right; trivial
theorem in_cartesian_product_intro: ∀ {x y z: Set} (a b: Set), a ∈ x → b ∈ y → z = ⸨a, b⸩ → z ∈ x × y := by
  intro x y z a b H1 H2 H3; rewrite [law_of_cartesian_product]
  exists a; exists b
theorem in_cartesian_product_elim: ∀ {x y z: Set}, z ∈ x × y → ∃ (a b: Set), a ∈ x ∧ b ∈ y ∧ z = ⸨a, b⸩ := by
  intro x y z Hz; rewrite [← law_of_cartesian_product]; trivial

end SetTheory
