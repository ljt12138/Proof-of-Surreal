import data.list tactic.omega defs single height

def left_tree : list tree → list tree
| [] := []
| (t :: l) := ⟦t ∣⟧ :: left_tree l

def right_tree : list tree → list tree
| [] := []
| (t :: l) := ⟦∣ t⟧ :: right_tree l

def full_list_tree (t : tree) : list tree → list tree
| [] := []
| (t' :: l) := ⟦t, t'⟧ :: (full_list_tree l)

def full_list : list tree → list tree → list tree
| [] := λ l, []
| (t :: l) := λ l', full_list_tree t l' ++ full_list l l'

lemma left_tree_correct : ∀ l t, t ∈ l → ⟦t ∣⟧ ∈ left_tree l :=
begin
  intros l t h, 
  induction l,
  cases h, cases h,
  begin unfold left_tree, rewrite h, apply list.mem_cons_self end,
  begin 
    unfold left_tree, apply list.mem_cons_of_mem, apply l_ih, apply h
  end
end

lemma right_tree_correct : ∀ l t, t ∈ l → ⟦∣ t⟧ ∈ right_tree l := 
begin
  intros l t h, 
  induction l,
  cases h, cases h, 
  begin unfold right_tree, rewrite h, apply list.mem_cons_self end,
  begin
    unfold right_tree, apply list.mem_cons_of_mem, apply l_ih, apply h
  end
end

lemma full_list_tree_correct : ∀ l t t', t' ∈ l → ⟦t, t'⟧ ∈ full_list_tree t l :=
begin
  intros l,
  induction l,
  begin intros, cases a end,
  begin
    intros t t' h, 
    cases h, 
    begin rewrite h, unfold full_list_tree, apply list.mem_cons_self end, 
    begin unfold full_list_tree, apply list.mem_cons_of_mem, apply l_ih, assumption end,
  end
end

lemma full_tree_correct : ∀ l l' t t', t ∈ l → t' ∈ l' → ⟦t, t'⟧ ∈ full_list l l' := 
begin
  intros l,
  induction l, 
  begin 
    intros l' t t' h1 h2, 
    cases h1
  end,
  begin
    intros l' t t' h1 h2, 
    unfold full_list, 
    cases h1, 
    begin 
      rewrite h1, apply list.mem_append_left, 
      apply full_list_tree_correct, assumption 
    end,
    begin
      apply list.mem_append_right, 
      apply l_ih, 
      assumption, assumption
    end
  end
end


lemma cross_product_tree : ∀ l : list tree, ∃ l' : list tree, ∀ t t', 
                             t ∈ l → t' ∈ l → ⟦t, t'⟧ ∈ l' ∧ ⟦t ∣⟧ ∈ l' ∧ ⟦∣ t'⟧ ∈ l' :=
begin
  intros l,
  have ht : ∃ l', l' = left_tree l ++ right_tree l ++ full_list l l, existsi left_tree l ++ right_tree l ++ full_list l l, refl,
  cases ht, 
  existsi ht_w, 
  intros t t' h1 h2, 
  split, 
  begin -- full 
    rewrite ht_h, 
    apply list.mem_append_right,
    apply full_tree_correct,
    repeat {assumption}
  end,
  split,
  begin -- left
    rewrite ht_h,
    apply list.mem_append_left, apply list.mem_append_left,
    apply left_tree_correct, assumption
  end,
  begin -- right
    rewrite ht_h,
    apply list.mem_append_left, apply list.mem_append_right,
    apply right_tree_correct, assumption
  end
end

lemma height_zero : ∀ t : tree, ¬(height t ≤ 0) :=
begin
  intros t contra, 
  have ht : height t = 0, omega,
  have ht' : height t ≥ 1, apply height_ge1,
  rewrite ht at ht',
  cases ht'
end

lemma bounded_height_list : ∀ h : ℕ, ∃ l : list tree, ∀ t : tree, 
                                        height t ≤ h → t ∈ l :=
begin
  intros h, induction h,
  begin 
    existsi list.nil, intros t a,
    exfalso, apply height_zero, repeat {assumption}
  end,
  begin
    cases h_n, 
    begin -- actuall induction basis
      existsi ([●]),
      intros t h,
      cases t, 
      simp, 
      repeat {
        unfold height at h, 
        exfalso, have ht : height t ≤ 0, omega,
        apply height_zero, repeat {assumption}
      },
      unfold height at h, 
      have ht : max (height t_a) (height t_a_1) = 0, omega, 
      have ht' : height t_a ≤ max (height t_a) (height t_a_1), apply le_max_left,
      rewrite ht at ht', 
      have ht2 : height t_a = 0, omega,
      have ht3 : height t_a ≥ 1, apply height_ge1, 
      rewrite ht2 at ht3, cases ht3
    end,
    begin
      cases h_ih, 
      cases (cross_product_tree h_ih_w), 
      existsi ● :: w, 
      intros t ht, 
      cases t, 
      begin apply list.mem_cons_self end,
      repeat {
        apply list.mem_cons_of_mem, 
        have hi : ● ∈ h_ih_w, apply h_ih_h, unfold height, omega,
        have hj : t ∈ h_ih_w, apply h_ih_h, unfold height at ht, omega, 
        try {exact (and.left (and.right (h t ● hj hi)))},
        try {exact (and.right (and.right (h ● t hi hj)))}
      },
      apply list.mem_cons_of_mem, 
      have hm : height t_a ≤ max (height t_a) (height t_a_1), apply le_max_left,
      have hn : height t_a_1 ≤ max (height t_a) (height t_a_1), apply le_max_right,
      have hi : t_a ∈ h_ih_w, apply h_ih_h, unfold height at ht, omega,
      have hj : t_a_1 ∈ h_ih_w, apply h_ih_h, unfold height at ht, omega, 
      exact (and.left (h t_a t_a_1 hi hj)), 
    end
  end
end

