import data.list algebra.ring tactic.omega defs single height tactics

lemma branch_son : ∀ t s : bintree, ⟨ t ⟩ → is_son s t → ⟨ s ⟩ := 
begin
  intros t,
  induction t,
  begin intros s H1 H2, cases H2 end, -- single case 
  repeat { -- left and right cases
    begin intros s H1 H2, cases H1, cases H2, assumption end,
  },
  begin 
    intros s H1 H2,
    cases H1, cases H2, assumption, auto_branch,  
    cases H2, auto_branch, assumption
  end
end

lemma branch_with_two_sons : ∀ b b' : bintree, 
      ⟨⟦b, b'⟧⟩ → b = ● ∨ b' = ● := 
begin
  intros b b' H1, 
  cases H1, 
  begin right, refl end, 
  begin left, refl end
end

def gen_link : ℕ → bintree
| 0 := ● 
| (nat.succ n) := ⟦●, gen_link n⟧

lemma gen_link_branch : ∀ n, ⟨gen_link n⟩ :=
begin
  intros n, induction n, 
  unfold gen_link, auto_branch, 
  unfold gen_link, auto_branch
end

lemma gen_link_height : ∀ n, height (gen_link n) = n + 1 := 
begin
  intros n, 
  induction n, 
  simp, unfold gen_link height, 
  unfold gen_link height, 
  have ht : _ := height_ge1 (gen_link n_n),
  have ht' : _ := ge.le ht,  
  have ht2 : _ := max_eq_right ht', rewrite ht2, omega 
end

lemma height_max_1_left : ∀ t, max (height t) 1 = height t := 
begin
  intros t, have ht : 1 ≤ height t := ge.le (height_ge1 _),
  apply max_eq_left, assumption
end

lemma height_max_1_right : ∀ t, max 1 (height t) = height t := 
begin
  intros t, have ht : 1 ≤ height t := ge.le (height_ge1 _),
  apply max_eq_right, assumption
end

lemma grow_high_bintree : ∀ t, ⟨t⟩ → ∀ h, (∃ t', ⟨t'⟩ ∧ (t ↣ t') ∧ height t' = height t + h) := 
begin
  intros t a, 
  induction a, 
  begin intros, existsi (gen_link h), split, exact gen_link_branch _, split, apply grow.single_grow, rewrite (gen_link_height _), unfold height, omega end,
  begin
    intros h, cases a_ih h, existsi ⟦w∣⟧, split, 
    auto_branch, split,
    auto_grow, 
    unfold height, rewrite h_1.right.right, omega 
  end,
  begin 
    intros h, cases a_ih h, existsi ⟦w, ●⟧, split,
    auto_branch, split,
    auto_grow,
    unfold height, repeat {rewrite height_max_1_left},
    rewrite h_1.right.right, omega
  end,
  begin 
    intros h, cases a_ih h, existsi ⟦∣w⟧, split,
    auto_branch, split,
    auto_grow, 
    unfold height, rewrite h_1.right.right, omega,
  end,
  begin 
    intros h, cases a_ih h, existsi ⟦●, w⟧, split,
    auto_branch, split,
    auto_grow,  
    unfold height, repeat {rewrite height_max_1_right},
    rewrite h_1.right.right, omega
  end
end

lemma branch_grow : ∀ b b' : bintree, ⟨ b ⟩ → (b' ↣ b) → ⟨ b' ⟩ := 
begin
  intros b b' h1 h2, 
  induction h2, 
  auto_branch,
  cases h1, auto_branch,
  cases h1, auto_branch,
  cases h1, 
  repeat{
    try {rewrite (single_grow _ h2_a_1)},
    try {rewrite (single_grow _ h2_a)},
    auto_branch
  }
end

lemma branch_prefix : ∀ b t t' : bintree, ⟨b⟩ → (t ↣ b) → (t' ↣ b) 
                                 → (height t ≤ height t') → (t ↣ t') := 
begin
  intros b, 
  induction b,
  begin -- base case, which is trivial since b = ●
    intros, auto_grow      
  end,
  begin -- left
    intros t t' h1 h2 h3 h4, 
    cases t, 
    begin auto_grow end,
    begin 
      cases h3, 
      begin 
        unfold height at h4, simp at h4, exfalso, exact h4
      end,
      begin
        cases h2, 
        unfold height at h4, 
        cases h1,  
        have ht : height t ≤ height h3_t, omega, 
        have ht' : (t ↣ h3_t), apply b_ih, repeat {assumption}, 
        auto_grow
      end
    end, 
    cases h3, cases h2, cases h2,
    cases h3, cases h2, cases h2, 
  end,
  begin -- right 
    intros t t' h1 h2 h3 h4, 
    cases t, 
    begin auto_grow end, 
    cases h3, cases h2, cases h2,
    begin 
      cases h3, 
      begin
        unfold height at h4, simp at h4, 
        exfalso, exact h4
      end,
      begin
        cases h2, 
        unfold height at h4, 
        cases h1, simp at h4,  
        have ht' : (t ↣ h3_t), apply b_ih, repeat {assumption}, 
        auto_grow
      end
    end,
    cases h3, cases h2, cases h2
  end,
  begin -- full
    intros t t' h1 h2 h3 h4, 
    cases t, 
    begin auto_grow end,
    cases h3, cases h2, cases h2, cases h2,
    cases t', 
    begin 
      unfold height at h4,
      simp at h4, exfalso, exact h4
    end, 
    begin cases h3 end,
    begin cases h3 end,
    begin 
      cases h2, cases h3, unfold height at h4,
      have h4' : max (height t_a) (height t_a_1) ≤ max (height t'_a) (height t'_a_1), omega, 
      have ht : max (height t'_a) (height t'_a_1) = height t'_a ∨ max (height t'_a) (height t'_a_1) = height t'_a_1, apply max_choice,
      have ht' : max (height t_a) (height t_a_1) ≤ height t'_a ∨ max (height t_a) (height t_a_1) ≤ height t'_a_1,
      begin 
        cases ht, 
        begin rewrite ht at h4, left, omega end,
        begin rewrite ht at h4, right, omega end,
      end,
      cases ht',
      begin
        have hl : _ := le_of_max_le_left ht',
        have hr : _ := le_of_max_le_right ht',
        cases h1,
        begin   
          have res_l : (t_a ↣ t'_a), 
          begin apply b_ih_a, repeat {assumption} end,
          auto_grow 
        end,
        begin 
          auto_grow, unfold height at *, auto_grow    
        end
      end,
      begin
        have hl : _ := le_of_max_le_left ht', 
        have hr : _ := le_of_max_le_right ht', 
        cases h1, 
        begin
          auto_grow, unfold height at *, auto_grow, auto_grow   
        end,
        begin
          have res_r : (t_a_1 ↣ t'_a_1), 
          begin apply b_ih_a_1, repeat {assumption} end,
          auto_grow
        end
      end
    end
  end
end
  
