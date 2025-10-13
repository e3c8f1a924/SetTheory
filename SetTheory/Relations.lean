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
noncomputable def equivalence_relations (a: Set) := separate (𝒫 (a × a)) (λ x: Set => (relation_refl a x) ∧ relation_symm x ∧ relation_trans x)
theorem law_of_equivalence_relations: ∀ (a R: Set), R ∈ equivalence_relations a ↔ R ∈ 𝒫 (a × a) ∧ relation_refl a R ∧ relation_symm R ∧ relation_trans R := by
  intro a R; unfold equivalence_relations; rewrite [law_of_separate]; trivial
theorem in_equivalence_relations_intro: ∀ {a R: Set}, R ∈ 𝒫 (a × a) → relation_refl a R → relation_symm R → relation_trans R → R ∈ equivalence_relations a := by
  intro a R; rewrite [law_of_equivalence_relations]; intro H1 H2 H3 H4; simp [H1, H2, H3, H4]
theorem in_equivalence_relations_elim: ∀ {a R: Set}, R ∈ equivalence_relations a → R ∈ 𝒫 (a × a) ∧ relation_refl a R ∧ relation_symm R ∧ relation_trans R := by
  simp [law_of_equivalence_relations]

/- Quotient Sets -/
noncomputable def relation_class (R a: Set) := separate (transform R pair_right) (λ b => a ⟪R⟫ b)
notation:130 "⟦ " R:131 "," a: 131 " ⟧" => relation_class R a
theorem law_of_relation_class: ∀ (R a b: Set), b ∈ ⟦R, a⟧ ↔ a ⟪R⟫ b := by
  intro R a b; unfold relation_class; apply Iff.intro
  . intro H; let ⟨H1, H2⟩ := in_separate_elim H; apply H2
  . intro H; apply in_separate_intro;
    . unfold in_relation at H; apply in_transform_intro (⸨a, b⸩)
      . apply H
      . simp [law_of_pair_right]
    . trivial
theorem in_relation_class_intro: ∀ {R a b: Set}, a ⟪R⟫ b → b ∈ ⟦R, a⟧ := by
  intro R a b H; simp [law_of_relation_class, H]
theorem in_relation_class_elim: ∀ {R a b: Set}, b ∈ ⟦R, a⟧ → a ⟪R⟫ b := by
  intro R a b Hb; rewrite [← law_of_relation_class]; trivial
noncomputable def quotient_set (a R: Set) := transform a (λ x: Set => ⟦R, x⟧)
notation:110 a:111 "/" b: 111  => quotient_set a b
noncomputable def is_patrition (a b: Set) := a = ⋃ b ∧ (∀ (x y: Set), x ∈ b → y ∈ b → x ≠ y → x ∩ y = ∅)
theorem equivalence_relations_quitient_set_partition: ∀ (a R: Set), R ∈ equivalence_relations a → is_patrition a (a / R) := by
  intro a R HR; let ⟨HR1, HR2, HR3, HR4⟩ := in_equivalence_relations_elim HR
  unfold is_patrition; apply And.intro
  . apply set_eq_intro; intro z; apply Iff.intro
    . intro Hz; apply in_unionset_intro (⟦R, z⟧)
      . unfold quotient_set; apply in_transform_intro z
        . trivial
        . trivial
      . apply in_relation_class_intro; apply HR2; trivial
    . intro Hz; let ⟨k, Hk1, Hk2⟩ := in_unionset_elim Hz
      unfold quotient_set at Hk1; let ⟨t, Ht1, Ht2⟩ := in_transform_elim Hk1
      rewrite [← Ht2] at Hk2; let Hk3 := in_relation_class_elim Hk2; let Hk4 := relation_elim Hk3
      let HR5 := in_powerset_elim HR1; let Hk5 := HR5 _ Hk4
      let Hk6 := pair_in_cartesian_product_elim Hk5
      simp [Hk6]
  . intro x y Hx Hy Hn; apply set_eq_intro; apply byContradiction; intro Ht; simp at Ht
    let ⟨z, Hz⟩ := Ht; simp [law_of_emptyset] at Hz; apply Hn; unfold quotient_set at Hx Hy
    let ⟨zx, Hzx1, Hzx2⟩ := in_transform_elim Hx
    let ⟨zy, Hzy1, Hzy2⟩ := in_transform_elim Hy
    let ⟨Hz1, Hz2⟩ := in_intersect_elim Hz
    rewrite [← Hzx2] at Hz1
    rewrite [← Hzy2] at Hz2
    rewrite [← Hzx2, ← Hzy2]; apply set_eq_intro
    intro k; rewrite [law_of_relation_class]; rewrite [law_of_relation_class]
    let Hz3 := in_relation_class_elim Hz1; let Hz4 := in_relation_class_elim Hz2
    let Hz5 := HR4 _ _ _ Hz3 (HR3 _ _ Hz4)
    apply Iff.intro
    . intro H1; apply (HR4 _ _ _ (HR3 _ _ Hz5)); trivial
    . intro H1; apply (HR4 _ _ _ Hz5); trivial
theorem law_of_equivalence_class_eq: ∀ (a R x y: Set), R ∈ equivalence_relations a → x ∈ a → y ∈ a → (⟦R, x⟧ = ⟦R, y⟧ ↔ x ⟪R⟫ y) := by
  intro a R x y HR Hx Hy; apply Iff.intro
  . intro H1; let H2 := (set_eq_elim H1) y; rewrite [law_of_relation_class] at H2; rewrite [law_of_relation_class] at H2
    let ⟨_, HR1, _, _⟩ := in_equivalence_relations_elim HR;
    simp [HR1 _ Hy] at H2; trivial
  . intro H1; apply set_eq_intro; intro z; rewrite [law_of_relation_class]
    rewrite [law_of_relation_class]; let ⟨_, _, HR2, HR1⟩ := in_equivalence_relations_elim HR
    apply Iff.intro
    . intro Hxz; apply HR1 _ _ _ (HR2 _ _ H1) Hxz
    . intro Hyz; apply HR1 _ _ _ H1; trivial
theorem equivalence_class_eq_intro: ∀ (a: Set) {R x y: Set}, R ∈ equivalence_relations a → x ∈ a → y ∈ a → x ⟪R⟫ y → ⟦R, x⟧ = ⟦R, y⟧ := by
  intro a R x y HR Hx Hy Hxy; rewrite [law_of_equivalence_class_eq a R x y]; repeat trivial
theorem equivalence_class_eq_elim: ∀ (a: Set) {R x y: Set}, R ∈ equivalence_relations a → x ∈ a → y ∈ a → ⟦R, x⟧ = ⟦R, y⟧ → x ⟪R⟫ y := by
  intro a R x y HR Hx Hy Hxy; rewrite [← law_of_equivalence_class_eq a R x y]; repeat trivial

/- Mappings -/
noncomputable def is_map (a f: Set) := ∀ x, x ∈ a → (∃ y, ⟦f, x⟧ = ⦃y⦄)
noncomputable def mapset (a b: Set) := separate (𝒫 (a × b)) (λ R => is_map a R)
notation:114 a:115 "↪" b: 115  => mapset a b
noncomputable def map_eval (f x: Set) := ⋃ ⟦f, x⟧
notation:113 f:114 "⸨" x: 114 "⸩"  => map_eval f x
theorem map_eval_in_codomain: ∀ (f a b x), f ∈ a ↪ b → x ∈ a → f⸨x⸩ ∈ b := by
  intro f a b x Hf Hx; unfold map_eval; unfold mapset at Hf
  let ⟨Hf1, Hf2⟩ := in_separate_elim Hf; let ⟨y, Hy2⟩ := Hf2 x Hx
  rewrite [Hy2]; rewrite [law_of_unionset_singleset]
  let Hy3 := set_eq_elim Hy2 y; simp [law_of_singleset, law_of_relation_class] at Hy3;
  unfold in_relation at Hy3; let Hf3 := in_powerset_elim Hf1
  let Hy4 := Hf3 _ Hy3; let Hy5 := pair_in_cartesian_product_elim Hy4;
  apply Hy5.right
theorem map_eval_in_map: ∀ (f a b x), f ∈ a ↪ b → x ∈ a → x ⟪f⟫ (f⸨x⸩) := by
  intro f a b x Hf Hx; apply relation_intro; unfold mapset at Hf
  let ⟨Hf1, Hf2⟩ := in_separate_elim Hf; let ⟨y, Hy2⟩ := Hf2 x Hx
  unfold map_eval; rewrite [Hy2]; rewrite [law_of_unionset_singleset]
  let Hy3 := set_eq_elim Hy2 y; simp [law_of_singleset] at Hy3
  let Hy4 := in_relation_class_elim Hy3; unfold in_relation at Hy4; trivial
theorem law_of_map_eval: ∀ (f a b x y), f ∈ a ↪ b → x ∈ a → (f⸨x⸩ = y ↔ x ⟪f⟫ y) := by
  intro f a b x y Hf Hx; apply Iff.intro
  . intro Hfx; rewrite [← Hfx]; apply map_eval_in_map f a b x Hf Hx
  . intro Hxy; let Hr := in_relation_class_intro Hxy
    let Ht := map_eval_in_map f a b x Hf Hx; let Hxfx := in_relation_class_intro Ht
    unfold mapset at Hf; let ⟨Hf1, Hf2⟩ := in_separate_elim Hf;
    let ⟨k, Hk2⟩ := Hf2 x Hx
    rewrite [Hk2] at Hr Hxfx; let Hr1 := in_singleset_elim Hr; let Hxfx1 := in_singleset_elim Hxfx
    simp [Hxfx1, Hr1]
noncomputable def map_constructor (a: Set) (F: Set → Set) := transform a (λ x: Set => ⸨x, F x⸩)
theorem map_constructor_is_map: ∀ (a: Set) (F: Set → Set), is_map a (map_constructor a F) := by
  intro a F; unfold map_constructor; unfold is_map
  intro x Hx; exists (F x); apply set_eq_intro
  intro z; rewrite [law_of_relation_class]; rewrite [law_of_singleset]
  unfold in_relation; apply Iff.intro
  . intro H; let ⟨k, Hk1, Hk2⟩ := in_transform_elim H
    let ⟨Hk3, Hk4⟩ := pair_eq_elim Hk2; rewrite [Hk3] at Hk4; rewrite [Hk4]; trivial
  . intro Hz; rewrite [Hz]; apply in_transform_intro x; repeat trivial
noncomputable def map_constructor_range (a: Set) (F: Set → Set) := transform a (λ t => F t)
theorem map_constructor_in_mapset: ∀ (a: Set) (F: Set → Set), (map_constructor a F) ∈ a ↪ (map_constructor_range a F) := by
  intro a F;
  unfold mapset; apply in_separate_intro
  . apply in_powerset_intro; intro t Ht; unfold map_constructor at Ht; let ⟨z, Hz1, Hz2⟩ := in_transform_elim Ht
    rewrite [← Hz2]; apply pair_in_cartesian_product_intro
    . trivial
    . apply in_transform_intro z; repeat trivial
  . apply map_constructor_is_map
theorem law_of_map_constructor_eval: ∀ (a: Set) (F: Set → Set), ∀ (x: Set), x ∈ a → (map_constructor a F) ⸨x⸩ = F x := by
  intro a F x Hx; let Ht := law_of_map_eval _ _ _ x (F x) (map_constructor_in_mapset a F) Hx
  rewrite [Ht]; unfold in_relation; unfold map_constructor; apply in_transform_intro x
  . trivial
  . trivial
theorem map_eq_intro: ∀ {f g a b: Set}, f ∈ a ↪ b → g ∈ a ↪ b → (∀ (x: Set), x ∈ a → f⸨x⸩ = g⸨x⸩) → f = g := by
  intro f g a b Hf Hg He; apply set_eq_intro; intro z;
  let Hfc := in_powerset_elim (in_separate_elim Hf).left z
  let Hgc := in_powerset_elim (in_separate_elim Hg).left z
  apply Iff.intro
  . intro Hzf; let ⟨x, y, Hx, Hy, Hz⟩ := in_cartesian_product_elim (Hfc Hzf)
    rewrite [Hz]; rewrite [Hz] at Hzf
    let Hfx: f⸨x⸩ = y := by
      rewrite [law_of_map_eval f a b x y Hf Hx]
      unfold in_relation; trivial
    let Hex := He x Hx; rewrite [Hfx] at Hex; apply relation_elim
    rewrite [← law_of_map_eval g a b x y Hg Hx]; apply Eq.symm; trivial
  . intro Hzg; let ⟨x, y, Hx, Hy, Hz⟩ := in_cartesian_product_elim (Hgc Hzg)
    rewrite [Hz]; rewrite [Hz] at Hzg
    let Hgx: g⸨x⸩ = y := by
      rewrite [law_of_map_eval g a b x y Hg Hx]
      unfold in_relation; trivial
    let Hex := He x Hx; rewrite [Hgx] at Hex; apply relation_elim
    rewrite [← law_of_map_eval f a b x y Hf Hx]; trivial
theorem in_map_elim: ∀ {f a b t: Set}, f ∈ a ↪ b → t ∈ f → ∃ x: Set, x ∈ a ∧ t = ⸨x, (f⸨x⸩)⸩ := by
  intro f a b t Hf Ht; unfold mapset at Hf
  let ⟨Hf1, Hf2⟩ := in_separate_elim Hf
  rewrite [law_of_powerset] at Hf1;
  let H2 := Hf1 _ Ht
  let ⟨α, β, Hα, Hβ, Hαβ⟩ := in_cartesian_product_elim H2
  exists α; apply And.intro
  . trivial
  . rewrite [Hαβ]; apply pair_eq_intro
    . trivial
    . rewrite [Hαβ] at Ht
      apply Eq.symm
      rewrite [law_of_map_eval _ _ _ _ _ Hf Hα]
      apply Ht
theorem in_map_intro: ∀ {f a b t x: Set}, f ∈ a ↪ b → x ∈ a → t = ⸨x, (f⸨x⸩)⸩ → t ∈ f := by
  intro f a b t x Hf Hx Ht; rewrite [Ht]
  apply map_eval_in_map _ _ _ _ Hf Hx

/- Operations -/
noncomputable def operation_set (a b c: Set) := (a × b) ↪ c
noncomputable def operation_eval (o a b: Set) := o⸨(⸨a, b⸩)⸩
notation:112 a:113 "⟦" o: 113 "⟧" b:113 => operation_eval o a b

end SetTheory
