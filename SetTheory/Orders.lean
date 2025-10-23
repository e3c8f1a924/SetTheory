import SetTheory.Relations

namespace SetTheory
namespace Omega

noncomputable def partial_orders (a: Set) := separate (𝒫 (a × a)) (λ R =>
  relation_refl a R ∧
  relation_antisymm R ∧
  relation_trans R
)
theorem in_partial_orders_iff: ∀ (x R: Set), R ∈ partial_orders x ↔ R ⊆ x × x ∧ relation_refl x R ∧ relation_antisymm R ∧ relation_trans R := by
  intro x R; unfold partial_orders; rewrite [law_of_separate]
  rewrite [law_of_powerset]; trivial
theorem in_partial_orders_elim: ∀ {x R: Set}, R ∈ partial_orders x → R ⊆ x × x ∧ relation_refl x R ∧ relation_antisymm R ∧ relation_trans R := by
  intro x R H; rewrite [← in_partial_orders_iff]; trivial
theorem in_partial_orders_intro: ∀ {x R: Set}, R ⊆ x × x → relation_refl x R → relation_antisymm R → relation_trans R → R ∈ partial_orders x := by
  intro x R HR H1 H2 H3; rewrite [in_partial_orders_iff]
  simp [HR, H1, H2, H3]

noncomputable def total_orders (a: Set) := separate (partial_orders a) (λ R => relation_conn a R)
theorem in_total_orders_iff: ∀ (x R: Set), R ∈ total_orders x ↔ R ∈ partial_orders x ∧ relation_conn x R := by
  intro x R; unfold total_orders; rewrite [law_of_separate]; trivial
theorem in_total_orders_elim: ∀ {x R: Set}, R ∈ total_orders x → R ∈ partial_orders x ∧ relation_conn x R := by
  intro x R; rewrite [← in_total_orders_iff]; simp
theorem in_total_orders_intro: ∀ {x R: Set}, R ∈ partial_orders x → relation_conn x R → R ∈ total_orders x := by
  intro x R; intro HR H1; rewrite [in_total_orders_iff]; simp [HR, H1]

noncomputable def well_orders (a: Set) := separate (total_orders a) (λ R => relation_well_founded a R)
theorem in_well_orders_iff: ∀ (x R: Set), R ∈ well_orders x ↔ R ∈ total_orders x ∧ relation_well_founded x R := by
  intro x R; unfold well_orders; simp [law_of_separate]
theorem in_well_orders_elim: ∀ {x R: Set}, R ∈ well_orders x → R ∈ total_orders x ∧ relation_well_founded x R := by
  simp [in_well_orders_iff]
theorem in_well_orders_intro: ∀ {x R: Set}, R ∈ total_orders x → relation_well_founded x R → R ∈ well_orders x := by
  intro x R HR H1; rewrite [in_well_orders_iff]; simp [HR, H1]

noncomputable def order_chains (a R: Set) := separate (𝒫 a) (λ S => relation_conn S R)
theorem in_order_chains_iff: ∀ (a R S: Set), S ∈ order_chains a R ↔ S ⊆ a ∧ relation_conn S R := by
  intro a R S; unfold order_chains; simp [law_of_separate, law_of_powerset]
theorem in_order_chains_elim: ∀ {a R S: Set}, S ∈ order_chains a R → S ⊆ a ∧ relation_conn S R := by
  simp [in_order_chains_iff]
theorem in_order_chains_intro: ∀ {a R S: Set}, S ⊆ a → relation_conn S R → S ∈ order_chains a R := by
  intro a R S H1 H2; simp [in_order_chains_iff, H1, H2]

end Omega
end SetTheory
