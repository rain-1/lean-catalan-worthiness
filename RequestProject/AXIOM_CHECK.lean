import RequestProject.Unconditional

/-- info: 'Catalan.catalan_worthiness_uncond_catalan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Catalan.catalan_worthiness_uncond_catalan

/-! The near-critical theorem remains conditional on the explicit Nesterenko form and
archimedean-rate inputs, but its deduction introduces no additional axioms. -/
#print axioms Catalan.catalan_worthiness_one_sub_eps_of_form
#print axioms Catalan.catalan_worthiness_one_sub_eps_unconditional
