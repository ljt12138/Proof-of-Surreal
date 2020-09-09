import data.list tactic.omega defs single height

def left_bintree : list bintree → list bintree
| [] := []
| (t :: l) := ⟦t ∣⟧ :: left_bintree l

def right_bintree : list bintree → list bintree
| [] := []
| (t :: l) := ⟦∣ t⟧ :: right_bintree l

def full_list_bintree (t : bintree) : list bintree → list bintree
| [] := []
| (t' :: l) := ⟦t, t'⟧ :: (full_list_bintree l)

def full_list : list bintree → list bintree → list bintree
| [] := λ l, []
| (t :: l) := λ l', full_list_bintree t l' ++ full_list l l'

lemma left_bintree_correct : ∀ l t, t ∈ l → ⟦t ∣⟧ ∈ left_bintree l :=
begin
  intros l t h, 
  induction l,
  cases h, cases h,
  begin unfold left_bintree, rewrite h, apply list.mem_cons_self end,
  begin 
    unfold left_bintree, apply list.mem_cons_of_mem, apply l_ih, apply h
  end
end

lemma right_bintree_correct : ∀ l t, t ∈ l → ⟦∣ t⟧ ∈ right_bintree l := 
begin
  intros l t h, 
  induction l,
  cases h, cases h, 
  begin unfold right_bintree, rewrite h, apply list.mem_cons_self end,
  begin
    unfold right_bintree, apply list.mem_cons_of_mem, apply l_ih, apply h
  end
end

lemma full_list_bintree_correct : ∀ l t t', t' ∈ l → ⟦t, t'⟧ ∈ full_list_bintree t l :=
begin
  intros l,
  induction l,
  begin intros, cases a end,
  begin
    intros t t' h, 
    cases h, 
    begin rewrite h, unfold full_list_bintree, apply list.mem_cons_self end, 
    begin unfold full_list_bintree, apply list.mem_cons_of_mem, apply l_ih, assumption end,
  end
end

lemma full_bintree_correct : ∀ l l' t t', t ∈ l → t' ∈ l' → ⟦t, t'⟧ ∈ full_list l l' := 
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
      apply full_list_bintree_correct, assumption 
    end,
    begin
      apply list.mem_append_right, 
      apply l_ih, 
      assumption, assumption
    end
  end
end


lemma cross_product_bintree : ∀ l : list bintree, ∃ l' : list bintree, ∀ t t', 
                             t ∈ l → t' ∈ l → ⟦t, t'⟧ ∈ l' ∧ ⟦t ∣⟧ ∈ l' ∧ ⟦∣ t'⟧ ∈ l' :=
begin
  intros l,
  have ht : ∃ l', l' = left_bintree l ++ right_bintree l ++ full_list l l, existsi left_bintree l ++ right_bintree l ++ full_list l l, refl,
  cases ht, 
  existsi ht_w, 
  intros t t' h1 h2, 
  split, 
  begin -- full 
    rewrite ht_h, 
    apply list.mem_append_right,
    apply full_bintree_correct,
    repeat {assumption}
  end,
  split,
  begin -- left
    rewrite ht_h,
    apply list.mem_append_left, apply list.mem_append_left,
    apply left_bintree_correct, assumption
  end,
  begin -- right
    rewrite ht_h,
    apply list.mem_append_left, apply list.mem_append_right,
    apply right_bintree_correct, assumption
  end
end

lemma bounded_height_list : ∀ h : ℕ, ∃ l : list bintree, ∀ t : bintree, 
                                        height t ≤ h → t ∈ l :=
begin
  intros h, induction h,
  begin 
    existsi list.nil, intros t a,
    simp at a, exfalso, exact a
  end,
  begin
    cases h_n, 
    begin -- actuall induction basis
      existsi ([●]),
      intros t h,
      cases t, 
      simp, 
      repeat { simp at h, exfalso, exact h }, 
    end,
    begin
      cases h_ih, 
      cases (cross_product_bintree h_ih_w), 
      existsi (list.cons ● w), 
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

