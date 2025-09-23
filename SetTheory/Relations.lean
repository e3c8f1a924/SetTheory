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
theorem pair_in_cartesian_product_iff: ∀ (a b x y: Set), ⸨x, y⸩ ∈ a × b ↔ x ∈ a ∧ y ∈ b := by
  intro a b x y; rewrite [law_of_cartesian_product]; apply Iff.intro
  . intro ⟨α, β, ⟨Hα, Hβ, He⟩⟩; let ⟨Hx, Hy⟩ := pair_eq_elim He; simp [Hx, Hy, Hα, Hβ]
  . intro ⟨Hx, Hy⟩; exists x; exists y
theorem pair_in_cartesian_product_intro: ∀ {a b x y: Set}, x ∈ a → y ∈ b → ⸨x, y⸩ ∈ a × b := by
  intro a b x y Hx Hy; rewrite [pair_in_cartesian_product_iff]; simp [Hx, Hy]
theorem pair_in_cartesian_product_elim: ∀ {a b x y: Set}, ⸨x, y⸩ ∈ a × b → x ∈ a ∧ y ∈ b := by
  intro a b x y H; rewrite [← pair_in_cartesian_product_iff]; trivial

/- Binary Relations -/
noncomputable def in_relation (a b R: Set) := ⸨a, b⸩ ∈ R
notation:100 a:101 "⟪" R:101 "⟫" b: 101 => in_relation a b R
theorem relation_intro: ∀ {a b R: Set}, ⸨a, b⸩ ∈ R → a ⟪R⟫ b := by
  intro a b R H; unfold in_relation; trivial
theorem relation_elim: ∀ {a b R: Set}, a ⟪R⟫ b → ⸨a, b⸩ ∈ R := by
  intro a b R H; unfold in_relation at H; trivial
noncomputable def relation_constructor (a b: Set) (f: Set → Set → Prop) := separate (a × b) (λ t: Set => f (pair_left t) (pair_right t))
theorem law_of_relation_constructor: ∀ (a b: Set) (f: Set → Set → Prop) (x y: Set), x ⟪relation_constructor a b f⟫ y ↔ x ∈ a ∧ y ∈ b ∧ f x y := by
  intro a b f x y; apply Iff.intro
  . intro H; let H1 := relation_elim H; unfold relation_constructor at H1;
    let ⟨Hl, Hr⟩ := in_separate_elim H1; let ⟨Ha, Hb⟩ := pair_in_cartesian_product_elim Hl
    simp [law_of_pair_left, law_of_pair_right] at Hr; simp [Ha, Hb, Hr]
  . intro ⟨Hx, Hy, Hf⟩; apply relation_intro; unfold relation_constructor
    apply in_separate_intro
    . apply pair_in_cartesian_product_intro
      . trivial
      . trivial
    . simp [law_of_pair_left, law_of_pair_right, Hf]
theorem relation_constructor_intro: ∀ {a b: Set} {f: Set → Set → Prop} {x y: Set}, x ∈ a → y ∈ b → f x y → x ⟪relation_constructor a b f⟫ y := by
  intro a b f x y Hx Hy Hf; rewrite [law_of_relation_constructor]; simp [Hx, Hy, Hf]
theorem relation_constructor_elim: ∀ {a b: Set} {f: Set → Set → Prop} {x y: Set}, x ⟪relation_constructor a b f⟫ y → x ∈ a ∧ y ∈ b ∧ f x y := by
  intro a b f x y H; rewrite [← law_of_relation_constructor]; trivial

/- Equivalence Relations -/
noncomputable def relation_refl (a: Set) (R: Set) := ∀ x: Set, x ∈ a → x ⟪R⟫ x
noncomputable def relation_symm (R: Set) := ∀ (x y: Set), x ⟪R⟫ y → y ⟪R⟫ x
noncomputable def relation_trans (R: Set) := ∀ (x y z: Set), x ⟪R⟫ y → y ⟪R⟫ z → x ⟪R⟫ z
noncomputable def equivalence_relations (a: Set) := separate (a × a) (λ x: Set => (relation_refl a x) ∧ relation_symm x ∧ relation_trans x)
theorem law_of_equivalence_relations: ∀ (a R: Set), R ∈ equivalence_relations a ↔ R ∈ a × a ∧ relation_refl a R ∧ relation_symm R ∧ relation_trans R := by
  intro a R; unfold equivalence_relations; rewrite [law_of_separate]; trivial
theorem in_equivalence_relations_intro: ∀ {a R: Set}, R ∈ a × a → relation_refl a R → relation_symm R → relation_trans R → R ∈ equivalence_relations a := by
  intro a R; rewrite [law_of_equivalence_relations]; intro H1 H2 H3 H4; simp [H1, H2, H3, H4]
theorem in_equivalence_relations_elim: ∀ {a R: Set}, R ∈ equivalence_relations a → R ∈ a × a ∧ relation_refl a R ∧ relation_symm R ∧ relation_trans R := by
  simp [law_of_equivalence_relations]

/- Quotient Sets -/
noncomputable def quotient_set (a R: Set) := transform a (λ x: Set => separate a (λ y: Set => x ⟪R⟫ y))
notation:110 a:111 "/" b: 111  => quotient_set a b

end SetTheory
