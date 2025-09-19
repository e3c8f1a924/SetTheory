namespace SetTheory

open Classical

axiom Set: Type
axiom set_inhabited: Inhabited Set
axiom set_in: Set → Set → Prop
notation:100 lhs:101 " ∈ " rhs:101 => set_in lhs rhs
notation:100 lhs:101 " ∉ " rhs:101 => ¬ set_in lhs rhs
/- Axiom of Extensionality -/
axiom set_eq_intro: ∀ {x y: Set}, (∀ (z: Set), z ∈ x ↔ z ∈ y) → x = y
theorem set_eq_elim: ∀ {x y: Set}, x = y → (∀ (z: Set), z ∈ x ↔ z ∈ y) := by
  intro x y H; rewrite [H]; intro z; trivial

/- Subsets -/
def set_sube (x: Set) (y: Set) := ∀ z: Set, z ∈ x → z ∈ y
def set_sub (x: Set) (y: Set) := set_sube x y ∧ x ≠ y
notation:100 lhs:101 " ⊆ " rhs:101 => set_sube lhs rhs
notation:100 lhs:101 " ⊂ " rhs:101 => set_sub lhs rhs
theorem sube_refl: ∀ x: Set, x ⊆ x := by
  intro H x; intro H1; trivial
theorem sube_tran: ∀ x y z: Set, x ⊆ y → y ⊆ z → x ⊆ z := by
  intro x y z H1 H2 t Ht; apply H2; apply H1; trivial

/- Axiom of Power Sets -/
axiom powerset: Set → Set
notation:120 "𝒫 " sth:121 => powerset sth
axiom law_of_powerset: ∀ x y: Set, y ∈ 𝒫 x ↔ y ⊆ x
theorem in_powerset_intro: ∀ {x y: Set}, y ⊆ x → y ∈ 𝒫 x := by
  intro x y H; rewrite [law_of_powerset]; trivial
theorem in_powerset_elim: ∀ {x y: Set}, y ∈ 𝒫 x → y ⊆ x := by
  intro x y H; rewrite [← law_of_powerset]; trivial

/- Axiom of Union -/
axiom unionset: Set → Set
notation:120 "⋃ " sth:121 => unionset sth
axiom law_of_unionset: ∀ x y: Set, y ∈ ⋃ x ↔ ∃ z: Set, z ∈ x ∧ y ∈ z
theorem in_unionset_intro: ∀ {x y: Set} (z: Set), z ∈ x → y ∈ z → y ∈ ⋃ x := by
  intro x y z Hz Hy; rewrite [law_of_unionset]; exists z
theorem in_unionset_elim: ∀ {x y: Set}, y ∈ ⋃ x → ∃ z: Set, z ∈ x ∧ y ∈ z := by
  intro x y H; rewrite [← law_of_unionset]; trivial

/- Axiom of Replacement -/
def replace_pattern_welldefined (p: Set → Set → Prop) := ∀ x, ∀ y z, p x y → p x z → y = z
axiom replace (_: Set) (p: Set → Set → Prop): replace_pattern_welldefined p → Set
axiom law_of_replacement: ∀ (x: Set) (p: Set → Set → Prop) (H: replace_pattern_welldefined p), ∀ (y: Set), y ∈ replace x p H ↔ (∃ z: Set, z ∈ x ∧ p z y)
theorem in_replacement_intro: ∀ {x: Set} {p: Set → Set → Prop} {H: replace_pattern_welldefined p} {y: Set} (z: Set), z ∈ x → p z y → y ∈ replace x p H := by
  intro x p H y z H1 H2; rewrite [law_of_replacement]; exists z
theorem in_replacement_elim: ∀ {x: Set} {p: Set → Set → Prop} {H: replace_pattern_welldefined p}, ∀ {y: Set}, y ∈ replace x p H → (∃ z: Set, z ∈ x ∧ p z y) := by
  intro x p H y Hy; rewrite [← law_of_replacement]; trivial

/- Separate Sets -/
def separate_filter_pattern (x: Set) (f: Set → Prop) :=
  λ y z: Set => y = z ∧ z ∈ x ∧ f z
theorem separate_filter_pattern_welldefined: ∀ (x: Set) (f: Set → Prop), ∀ t, ∀ y z, (separate_filter_pattern x f) t y → (separate_filter_pattern x f) t z → y = z := by
  intro x f x y z; unfold separate_filter_pattern
  intro H1 H2; rewrite [Eq.symm H1.left]; apply H2.left
noncomputable def separate (x: Set) (p: Set → Prop) := replace x (separate_filter_pattern x p) (separate_filter_pattern_welldefined x p)
theorem law_of_separate: ∀ (x: Set) (p: Set → Prop), ∀ (y: Set), y ∈ separate x p ↔ y ∈ x ∧ p y := by
  intro x p y; unfold separate; rewrite [law_of_replacement]; unfold separate_filter_pattern
  apply Iff.intro
  . intro ⟨_, H⟩; apply H.right.right
  . intro H; exists y; apply And.intro
    . apply H.left
    . apply And.intro; trivial; apply H
theorem in_separate_intro: ∀ {x: Set} {p: Set → Prop} {y: Set}, y ∈ x → p y → y ∈ separate x p := by
  intro x p y Hy Hpy; rewrite [law_of_separate]; trivial
theorem in_separate_elim: ∀ {x: Set} {p: Set → Prop}, ∀ {y: Set}, y ∈ separate x p → y ∈ x ∧ p y := by
  intro x p y Hy; rewrite [← law_of_separate]; trivial

/- Set Transformers -/
def transformer_pattern (_: Set) (f: Set → Set) :=
  λ y z: Set => f y = z
theorem transformer_patrern_welldefined : ∀ (x: Set) (f: Set → Set), replace_pattern_welldefined (transformer_pattern x f) := by
  unfold replace_pattern_welldefined; unfold transformer_pattern
  intro _ f x y z H1 H2; rewrite [Eq.symm H1]; rewrite [H2]; trivial
noncomputable def transform (x: Set) (f: Set → Set) := replace x (transformer_pattern x f) (transformer_patrern_welldefined x f)
theorem law_of_transform: ∀ (x: Set) (f: Set → Set), ∀ (y: Set), y ∈ transform x f ↔ ∃ z, z ∈ x ∧ f z = y := by
  unfold transform; intro x f y; rewrite [law_of_replacement]; unfold transformer_pattern; trivial
theorem in_transform_intro: ∀ {x: Set} {f: Set → Set} {y: Set} (z: Set), z ∈ x → f z = y → y ∈ transform x f := by
  intro x f y z Hz Hfz; rewrite [law_of_transform]; exists z
theorem in_transform_elim: ∀ {x: Set} {f: Set → Set}, ∀ {y: Set}, y ∈ transform x f → ∃ z, z ∈ x ∧ f z = y := by
  intros; rewrite [← law_of_transform]; trivial

/- Emptyset -/
noncomputable def emptyset := separate set_inhabited.default (λ _ => False)
notation:1024 (priority := high) "∅" => emptyset
theorem law_of_emptyset: ∀ x: Set, x ∉ ∅ := by
  intros z H; unfold emptyset at H; rewrite [law_of_separate] at H; apply H.right
theorem set_ne_elim: ∀ {x: Set}, x ≠ ∅ → ∃ y, y ∈ x := by
  intro x H; apply byContradiction; intro H'
  apply H; simp at H'; apply set_eq_intro; intro z
  apply Iff.intro
  . intro Hz; exfalso; apply (H' z); trivial
  . intro Hz; exfalso; apply (law_of_emptyset z); trivial

/- Single Sets -/
noncomputable def single (x: Set) := separate (𝒫 x) (λ y => y = x)
notation:130 "⦃ " sth:131 " ⦄" => single sth
theorem law_of_singleset: ∀ (x: Set) (y: Set), y ∈ ⦃x⦄ ↔ y = x := by
  intro x y; unfold single; rewrite [law_of_separate]; apply Iff.intro
  . intro H; apply H.right
  . intro H; apply And.intro
    . rewrite [law_of_powerset]; rewrite [H]; apply sube_refl
    . trivial
theorem in_singleset_intro: ∀ {x y: Set}, y = x → y ∈ ⦃x⦄ := by
  intro x y Hy; rewrite [law_of_singleset]; trivial
theorem in_singleset_elim: ∀ {x y: Set}, y ∈ ⦃x⦄ → y = x := by
  intro x y Hy; rewrite [← law_of_singleset]; trivial
theorem sube_singleset_elim: ∀ {x y: Set}, y ⊆ ⦃x⦄ → y = ∅ ∨ y = ⦃x⦄ := by
  intro x y H; unfold set_sube at H
  apply (Or.elim (em (y = ∅)))
  . intro H1; left; trivial
  . intro Hy; right; let ⟨z, Hz⟩ := set_ne_elim Hy
    let Hz' := in_singleset_elim (H _ Hz);
    rewrite [Hz'] at Hz; apply set_eq_intro
    intro t; apply Iff.intro
    . apply H
    . intro Ht; let Ht' := in_singleset_elim Ht
      rewrite [Ht']; trivial
theorem singleset_ne: ∀ {x: Set}, ⦃x⦄ ≠ ∅ := by
  intro x H; apply law_of_emptyset x
  rewrite [← H]; apply in_singleset_intro; trivial
theorem singleset_eq_elim: ∀ {x y: Set}, ⦃x⦄ = ⦃y⦄ → x = y := by
  intro x y H; let H1 := (set_eq_elim H) x;
  rewrite [law_of_singleset] at H1
  rewrite [law_of_singleset] at H1
  rewrite [← H1]; trivial

/- Unordered Pairs -/
noncomputable def unordered_pair (x: Set) (y: Set) := transform (𝒫 ⦃x⦄) (λ (z: Set) => if z = ∅ then y else x)
notation:130 "⦃ " a:131 "," b: 131 " ⦄" => unordered_pair a b
theorem law_of_unordered_pair: ∀ (x y z: Set), z ∈ ⦃x, y⦄ ↔ z = x ∨ z = y := by
  intro x y z; unfold unordered_pair; apply Iff.intro
  . intro H; let ⟨α, ⟨Hα1, Hα2⟩⟩ := in_transform_elim H
    let Hα1' := sube_singleset_elim (in_powerset_elim Hα1)
    apply Or.elim Hα1'
    . intro Hα; rewrite [Hα] at Hα2; simp at Hα2; right; rewrite [Hα2]; trivial
    . intro Hα; rewrite [Hα] at Hα2; simp [singleset_ne] at Hα2; left; rewrite [Hα2]; trivial
  . intro H; apply Or.elim H
    . intro Hz; rewrite [Hz]; apply in_transform_intro (⦃x⦄)
      . apply in_powerset_intro; apply sube_refl
      . simp [singleset_ne]
    . intro Hz; rewrite [Hz]; apply in_transform_intro ∅
      . apply in_powerset_intro; intro t Ht; exfalso; apply law_of_emptyset t; trivial
      . simp
theorem in_unordered_pair_intro: ∀ {x y z: Set}, z = x ∨ z = y → z ∈ ⦃x, y⦄ := by
  intro x y z H; rewrite [law_of_unordered_pair]; trivial
theorem in_unordered_pair_elim: ∀ {x y z: Set}, z ∈ ⦃x, y⦄ → z = x ∨ z = y := by
  intro x y z H; rewrite [← law_of_unordered_pair]; trivial

/- Binary Union -/
noncomputable def union (x y: Set) := ⋃ ⦃x, y⦄
notation:110 a:111 "∪" b: 111  => union a b
theorem law_of_binary_union: ∀ (x y z: Set), z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y := by
  intro x y z; unfold union; rewrite [law_of_unionset];
  apply Iff.intro
  . intro ⟨t, ⟨Ht, Hz⟩⟩; let Ht' := in_unordered_pair_elim Ht
    apply Or.elim Ht'
    . intro Ht1; rewrite [← Ht1]; left; trivial
    . intro Ht1; rewrite [← Ht1]; right; trivial
  . intro H; apply Or.elim H
    . intro Hz; exists x; simp [Hz]
      apply in_unordered_pair_intro; left; trivial
    . intro Hz; exists y; simp [Hz]
      apply in_unordered_pair_intro; right; trivial
theorem in_union_intro: ∀ {x y z: Set}, z ∈ x ∨ z ∈ y → z ∈ x ∪ y := by
  intro x y z H; rewrite [law_of_binary_union]; trivial
theorem in_union_elim: ∀ {x y z: Set}, z ∈ x ∪ y → z ∈ x ∨ z ∈ y := by
  intro x y z H; rewrite [← law_of_binary_union]; trivial

/- Axiom of Infinity -/
noncomputable def set_succ (x: Set) := x ∪ ⦃x⦄
notation:125 sth:126 "⁺" => set_succ sth
noncomputable def set_inductive (x: Set) := ∀ y: Set, y ∈ x → y⁺ ∈ x
axiom axiom_of_infinity: ∃ x: Set, set_inductive x

/- Pairs -/
noncomputable def pair (x y: Set) := ⦃(⦃x⦄), (⦃x, y⦄)⦄
noncomputable def pair_left (x: Set) := ⋃ separate (⋃ x) (λ z: Set => ⦃z⦄ ∈ x)
noncomputable def pair_right (x: Set) := if (⋃ x) = ⦃pair_left x⦄ then pair_left x else ⋃ separate (⋃ x) (λ z: Set => z ≠ pair_left x)
notation:130 "⸨ " a:131 "," b: 131 " ⸩" => pair a b
theorem law_of_pair_left: ∀ (x y: Set), pair_left (⸨x, y⸩) = x := by
  intro x y; unfold pair_left; apply set_eq_intro
  intro z; rewrite [law_of_unionset]; apply Iff.intro
  . intro ⟨α, ⟨Hα1, Hα2⟩⟩; let ⟨Hα3, Hα4⟩ := in_separate_elim Hα1
    let ⟨β, ⟨Hβ1, Hα6⟩⟩ := in_unionset_elim Hα3
    unfold pair at Hβ1; let Hβ2 := in_unordered_pair_elim Hβ1
    apply Or.elim Hβ2
    . intro Hβ3; rewrite [Hβ3] at Hα6; let Hα7 := in_singleset_elim Hα6
      rewrite [← Hα7]; trivial
    . intro Hβ3; rewrite [Hβ3] at Hα6; let Hα7 := in_unordered_pair_elim Hα6
      apply Or.elim Hα7
      . intro Hα8; rewrite [← Hα8]; trivial
      . intro Hα8; rewrite [Hα8] at Hα4; unfold pair at Hα4
        apply Or.elim (in_unordered_pair_elim Hα4)
        . intro H'; let H'' := singleset_eq_elim H'
          rewrite [← H'']; rewrite [← Hα8]; trivial
        . intro Hy; let Hy1 := (set_eq_elim Hy) x
          rewrite [law_of_unordered_pair] at Hy1
          let Hx: x = y := by
            rewrite [← law_of_singleset]; rewrite [Hy1]; left; trivial
          rewrite [Hx]; rewrite [← Hα8]; trivial
  . intro Hz; exists x; apply And.intro
    . apply in_separate_intro
      . apply in_unionset_intro (⦃x⦄)
        . unfold pair; apply in_unordered_pair_intro; left; trivial
        . apply in_singleset_intro; trivial
      . unfold pair; apply in_unordered_pair_intro; left; trivial
    . trivial
theorem law_of_pair_right: ∀ (x y: Set), pair_right (⸨x, y⸩) = y := by
  intro x y; unfold pair_right; apply Or.elim (em ((⋃ ⸨x, y⸩) = ⦃pair_left (⸨x, y⸩)⦄))
  . intro H; simp [H]; rewrite [law_of_pair_left] at H; let H' := (set_eq_elim H) y
    rewrite [law_of_unionset] at H'
    let H1: y = x := by
      rewrite [← law_of_singleset]; rewrite [← H']; exists ⦃x, y⦄
      apply And.intro
      . unfold pair; apply in_unordered_pair_intro; right; trivial
      . apply in_unordered_pair_intro; right; trivial
    rewrite [H1]; apply law_of_pair_left
  . intro H; simp [H]; rewrite [law_of_pair_left]
    let H1: ⋃ ⸨x, y⸩ = ⦃x, y⦄ := by
      apply set_eq_intro; intro z
      rewrite [law_of_unionset]; rewrite [law_of_unordered_pair]
      apply Iff.intro
      . intro ⟨α, ⟨Hα1, Hα2⟩⟩; unfold pair at Hα1
        apply Or.elim (in_unordered_pair_elim Hα1)
        . intro H1; rewrite [H1] at Hα2; left; apply in_singleset_elim; trivial
        . intro H2; rewrite [H2] at Hα2; apply in_unordered_pair_elim; trivial
      . intro H1; apply Or.elim H1
        . intro H2; exists ⦃x⦄; apply And.intro
          . unfold pair; apply in_unordered_pair_intro; left; trivial
          . apply in_singleset_intro; trivial
        . intro H2; exists (⦃x, y⦄); apply And.intro
          . unfold pair; apply in_unordered_pair_intro; right; trivial
          . apply in_unordered_pair_intro; right; trivial
    rewrite [H1]
    let H2: (separate (⦃ x,y ⦄) fun z => ¬z = x) = ⦃y⦄ := by
      apply set_eq_intro; intro z; rewrite [law_of_separate]
      rewrite [law_of_unordered_pair]; apply Iff.intro
      . intro ⟨Hx, Hy⟩; apply Or.elim Hx
        . intro H3; contradiction
        . intro H3; apply in_singleset_intro; trivial
      . intro H3; let H4 := in_singleset_elim H3; apply And.intro
        . right; trivial
        . intro H5; rewrite [H4] at H5
          let H6 : ⸨x, y⸩ = ⦃(⦃x⦄)⦄ := by
            unfold pair; apply set_eq_intro
            intro α; rewrite [law_of_unordered_pair]
            let H8 : ⦃x, y⦄ = ⦃x⦄ := by
              apply set_eq_intro; intro β; rewrite [law_of_unordered_pair]
              rewrite [H5]; simp; rewrite [law_of_singleset]; trivial
            rewrite [H8]; simp; rewrite [law_of_singleset]; trivial
          simp [law_of_pair_left] at H; rewrite [H6] at H
          apply H; apply set_eq_intro; intro α; apply Iff.intro
          . intro H7; let ⟨β, ⟨Hβ1, Hβ2⟩⟩ := in_unionset_elim H7;
            let Hβ3 := in_singleset_elim Hβ1; rewrite [Hβ3] at Hβ2; trivial
          . intro H7; apply in_unionset_intro (⦃x⦄);
            . apply in_singleset_intro; trivial
            . trivial
    rewrite [H2]; apply set_eq_intro; intro z;
    apply Iff.intro
    . intro H2; let ⟨α, ⟨Hα1, Hα2⟩⟩ := in_unionset_elim H2
      rewrite [in_singleset_elim Hα1] at Hα2; trivial
    . intro H3; apply in_unionset_intro y
      . apply in_singleset_intro; trivial
      . trivial

end SetTheory
