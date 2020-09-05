import data.list algebra.ring tactic.omega defs

lemma single_complete: almost_complete [●] := 
begin
  apply almost_complete.cmp_rule,
  existsi ([]), 
  intros t h, 
  exfalso, apply h, apply grow_list.head_grow, 
  apply grow.single_grow
end  

lemma single_grow : ∀ t : tree, (t ↣ ●) → t = ● := 
begin
  intros t H1,
  destruct t,
  begin intros, assumption end,
  repeat { 
    intros a H2, 
    rewrite H2 at H1,
    cases H1,
  }, -- this proves the first two goals
  begin
    intros a a1 H2,
    rewrite H2 at H1,
    cases H1,
  end -- this proves the last two goals
end

