import data.list tactic.omega defs single branch

lemma grow_trans : ∀ t1 t2 t3 : bintree, 
      (t1 ↣ t2) → (t2 ↣ t3) → (t1 ↣ t3) :=
begin
  intro t1, induction t1,
  begin intros, auto_grow end,
  repeat { begin 
    intros t2 t3 H1 H2,
    cases H1, cases H2, 
    have H3 : (t1_a ↣ H2_t'), apply t1_ih, repeat {assumption},
    auto_grow
  end }, 
  intros t2 t3 H1 H2, 
  cases H1, cases H2, 
  have H3 : (t1_a ↣ H2_t1'), apply t1_ih_a, repeat {assumption},
  have H4 : (t1_a_1 ↣ H2_t2'), apply t1_ih_a_1, repeat {assumption},
  auto_grow
end

lemma grow_list_exists_one : ∀ (l : list bintree) (t : bintree), (l ↦ t) →
                           ∃ t', (t' ∈ l) ∧ (t' ↣ t) :=
begin
  intros l t h,
  induction h,
  begin existsi h_t, split, apply list.mem_cons_self, assumption end,
  begin
    cases h_ih,
    existsi h_ih_w,
    split, apply list.mem_cons_of_mem, tauto, tauto
  end
end

lemma exists_one_grow_list : ∀ l t, (∃ t', ((t' ∈ l) ∧ (t' ↣ t))) → (l ↦ t) :=
begin
  intros l,
  induction l,
  begin intros, cases a, cases a_h.left end,
  begin
    intros t h,
    cases h,
    unfold has_mem.mem list.mem at h_h,
    cases h_h.left,
    begin
      apply grow_list.head_grow,
      rewrite h at h_h,
      exact h_h.right
    end,
    begin
      apply grow_list.tail_grow,
      apply l_ih,
      existsi h_w, split,
      assumption, exact h_h.right
    end
  end
end

lemma kernel_lemma : ∀ (t : bintree) (h : ℕ), 
  h ≥ 1 → h ≤ height t → ∃ b : bintree, ⟨b⟩ ∧ h = height b ∧ (b ↣ t) := 
begin
  intros t,
  induction t,
  begin -- single node
    intros, unfold height at a_1, 
    have H : h = 1, omega,
    rewrite H, fapply exists.intro, exact ●, 
    split, apply is_branch.single, 
    split, unfold height, auto_grow,
  end, 
  repeat { -- left and right
    intros h H1 H2, 
    cases h, cases H1, unfold height at H2, 
    have H1' : h ≥ 0, omega, 
    have H2' : h ≤ height t_a, omega, 
    cases h, 
    begin -- h = 0, which is trivial
      fapply exists.intro, exact ●, 
      split, exact is_branch.single, 
      split, unfold height, apply grow.single_grow    
    end,
    begin -- h ≠ 0, apply induction hypothesis
      have H3 : ∃ (b : bintree), ⟨b⟩ ∧ h.succ = height b ∧ (b↣t_a), 
        apply t_ih, omega, omega,  
      cases H3, 
      try { 
        existsi ⟦H3_w∣⟧, split, apply is_branch.left_nl, tauto, 
        split, unfold height, 
               have Ht : h.succ = height H3_w, tauto, omega,
        apply grow.left_grow, tauto,  
      },
      try {
        existsi ⟦∣H3_w⟧, split, apply is_branch.right_nl, tauto, 
        split, unfold height,
               have Ht : h.succ = height H3_w, tauto, omega, 
        apply grow.right_grow, tauto,
      }
    end
  }, 
  intros h H1 H2, -- both left and right, completely similar, while more tedious
  cases h, cases H1, unfold height at H2, 
  have H1' : h ≥ 0, omega,
  have H2' : h ≤ max (height t_a) (height t_a_1), omega,
  cases h, 
  begin
    fapply exists.intro, exact ●, 
    split, exact is_branch.single, 
    split, unfold height, apply grow.single_grow
  end, 
  begin
    have H3 : h.succ ≤ height t_a ∨ h.succ ≤ height t_a_1, 
      begin 
        have H3' : max (height t_a) (height t_a_1) = height t_a ∨ max (height t_a) (height t_a_1) = height t_a_1, apply max_choice,
        destruct H3', 
          intro H4, left, rewrite H4 at H2', assumption,
          intro H4, right, rewrite H4 at H2', assumption
      end,
    destruct H3,
    begin
      intros H4, 
      have H5 : h.succ ≥ 1, omega, 
      have H6 : ∃ (b : bintree), ⟨ b ⟩ ∧ h.succ = height b ∧ (b ↣ t_a), 
        apply t_ih_a, repeat {assumption},
      cases H6, cases H6_h, cases H6_h_right, existsi (⟦H6_w, ●⟧), 
      split, apply is_branch.left_l, assumption, 
      split, unfold height, 
        have Ht : (1 ≤ height H6_w), apply ge.le, apply height_ge1, 
        have Ht' : max (height H6_w) 1 = height H6_w, apply max_eq_left, assumption, 
        omega,
      auto_grow  
    end,
    begin
      intros H4, 
      have H5 : h.succ ≥ 1, omega, 
      have H6 : ∃ (b : bintree), ⟨ b ⟩ ∧ h.succ = height b ∧ (b ↣ t_a_1), 
        apply t_ih_a_1, repeat {assumption}, 
      cases H6, cases H6_h, cases H6_h_right, existsi (⟦●, H6_w⟧), 
      split, apply is_branch.right_l, assumption, 
      split, unfold height, 
        have Ht : (1 ≤ height H6_w), apply ge.le, apply height_ge1, 
        have Ht' : max 1 (height H6_w) = height H6_w, apply max_eq_right, assumption,
        omega,
      auto_grow
    end
  end
end

