import defs single finite branch grow data.list

open classical

lemma branch_to_dense : ∀ l, (∀ b, height b = height_bound l → ⟨b⟩ → (l ↦ b)) → (∀ t, height_bound l <= height t → (l ↦ t)):=
begin
  intros l h1 t h2,
  cases (kernel_lemma _ _ (height_bound_ge1 _) h2),
  have ht1 : _ := h.left,
  have ht2 : _ := h.right.left,
  have ht3 : _ := h.right.right,
  have ht : (l ↦ w), apply h1, rewrite ht2, assumption,
  cases (grow_list_exists_one _ _ ht),
  apply exists_one_grow_list,
  existsi w_1, split, exact h_1.left,
  apply grow_trans,
  exact h_1.right, exact ht3
end

lemma branch_to_complete : ∀ l, (∀ b, height b = height_bound l → ⟨b⟩ → (l ↦ b)) → almost_complete l :=
begin
  intros, 
  apply almost_complete.cmp_rule,
  cases (bounded_height_list (height_bound l)),
  existsi w, intros t h',
  have ht : _ := (branch_to_dense l a t), 
  have ht' : ¬(height_bound l ≤ height t), tauto, 
  apply h, omega
end

lemma complete_to_week_dense : ∀ l, almost_complete l → (∃ h, h ≥ 1 ∧ (∀ t, height t = h → (l ↦ t))) :=
begin
  intros l h, 
  cases h, cases h_a, 
  existsi (height_bound h_a_w)+1,
  split,omega, 
  intros t h1, 
  classical, 
  by_contra,
  have ht : _ := h_a_h _ a, 
  have ht' : _ := height_bound_correct h_a_w _ ht,
  rewrite h1 at ht', 
  exact nat.not_succ_le_self (height_bound h_a_w) ht'
end

lemma complete_to_branch : ∀ l, almost_complete l → (∀ b, height b = height_bound l → ⟨b⟩ → (l ↦ b)) :=
begin
  intros l h1 b h2 h3, 
  classical, by_contra,
  cases complete_to_week_dense l h1,
  cases le_or_gt w (height b),
  begin
    cases (kernel_lemma b w h.left h_1), 
    have ht : _ := h.right w_1 (eq.symm (h_2.right.left)),
    apply a, cases grow_list_exists_one l w_1 ht, 
    have ht' : _ := grow_trans _ _ _ h_3.right h_2.right.right, 
    apply exists_one_grow_list, existsi w_2,
    split, repeat {tauto}
  end,
  begin
    have ht' : height b + (w - height b) = w, omega, 
    cases (grow_high_tree b h3 (w - height b)),
    cases h_2.right, 
    have h_2' : height w_1 = w, omega, 
    have h' : _ := h.right w_1 h_2',
    apply a, cases grow_list_exists_one l w_1 h',
    have h_height : _ := height_bound_correct l w_2 h_3.left,
    rewrite h2.symm at h_height,
    have h_almost : _ := (branch_prefix w_1 w_2 b h_2.left h_3.right left h_height),
    apply exists_one_grow_list, existsi w_2,
    tauto
  end
end

theorem complete_iff_branch : ∀ l, almost_complete l ↔ (∀ b, height b = height_bound l → ⟨b⟩ → (l ↦ b)) :=
begin
  intros, split,
  exact complete_to_branch _, 
  exact branch_to_complete _
end

